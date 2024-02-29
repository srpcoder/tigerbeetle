//! Compaction moves or merges a table's values from the previous level.
//!
//! Each Compaction is paced to run in an arbitrary amount of beats, by the forest.
//!
//!
//! Compaction overview:
//!
//! 1. Given:
//!
//!   - levels A and B, where A+1=B
//!   - a single table in level A ("table A")
//!   - all tables from level B which intersect table A's key range ("tables B")
//!     (This can include anything between 0 tables and all of level B's tables.)
//!
//! 2. If table A's key range is disjoint from the keys in level B, move table A into level B.
//!    All done! (But if the key ranges intersect, jump to step 3).
//! FIXME: Update
//! 3. Create an iterator from the sort-merge of table A and the concatenation of tables B.
//!    If the same key exists in level A and B, take A's and discard B's. †
//!
//! 4. Write the sort-merge iterator into a sequence of new tables on disk.
//!
//! 5. Update the input tables in the Manifest with their new `snapshot_max` so that they become
//!    invisible to subsequent read transactions.
//!
//! 6. Insert the new level-B tables into the Manifest.
//!
//! † When A's value is a tombstone, there is a special case for garbage collection. When either:
//! * level B is the final level, or
//! * A's key does not exist in B or any deeper level,
//! then the tombstone is omitted from the compacted output, see: `compaction_must_drop_tombstones`.
//!
const std = @import("std");
const mem = std.mem;
const math = std.math;
const assert = std.debug.assert;
const Allocator = std.mem.Allocator;

const log = std.log.scoped(.compaction);
const tracer = @import("../tracer.zig");

const constants = @import("../constants.zig");

const stdx = @import("../stdx.zig");
const GridType = @import("../vsr/grid.zig").GridType;
const BlockPtr = @import("../vsr/grid.zig").BlockPtr;
const BlockPtrConst = @import("../vsr/grid.zig").BlockPtrConst;
const allocate_block = @import("../vsr/grid.zig").allocate_block;
const TableInfoType = @import("manifest.zig").TreeTableInfoType;
const ManifestType = @import("manifest.zig").ManifestType;
const schema = @import("schema.zig");

/// The upper-bound count of input tables to a single tree's compaction.
///
/// - +1 from level A.
/// - +lsm_growth_factor from level B. The A-input table cannot overlap with an extra B-input table
///   because input table selection is least-overlap. If the input table overlaps on one or both
///   edges, there must be another table with less overlap to select.
pub const compaction_tables_input_max = 1 + constants.lsm_growth_factor;

/// The upper-bound count of output tables from a single tree's compaction.
/// In the "worst" case, no keys are overwritten/merged, and no tombstones are dropped.
pub const compaction_tables_output_max = compaction_tables_input_max;

/// Information used when scheduling compactions. Kept unspecalized to make the forest
/// code easier.
pub const CompactionInfo = struct {
    /// How many values, across all tables, need to be processed.
    compaction_tables_value_count: usize,

    // Keys are integers in TigerBeetle, with a maximum size of u128. Store these
    // here, instead of Key, to keep this unspecalized.
    target_key_min: u128,
    target_key_max: u128,
};

pub const Exhausted = struct { bar: bool, beat: bool };
const BlipCallback = *const fn (*anyopaque, ?Exhausted) void;
pub const BlipStage = enum { read, merge, write };

// The following types need to specalize on Grid, but are used both by CompactionType and the
// forest.
pub fn CompactionHelperType(comptime Grid: type) type {
    return struct {
        /// Wrap a RingBuffer, and provide an interface around it given that the underlying slice
        /// is managed (ie, BlockPtr) memory.
        pub const BlockRingBuffer = struct {
            pub const Inner = @import("../ring_buffer.zig").RingBuffer(CompactionBlock, .slice);
            pub const Slice = Inner.Slice;

            inner: Inner,
            read_outstanding: ?struct { start: usize, len: usize } = null,
            write_outstanding: ?struct { start: usize, len: usize } = null,

            pub fn init(blocks: []CompactionBlock) BlockRingBuffer {
                assert(blocks.len % 2 == 0);

                return .{
                    .inner = Inner.init(blocks),
                };
            }

            pub fn format(value: BlockRingBuffer, comptime _: []const u8, _: std.fmt.FormatOptions, writer: anytype) !void {
                return writer.print("BlockRingBuffer: inner.index: {}, inner.count: {}, write_outstanding: {?}", .{ value.inner.index, value.inner.count, value.write_outstanding });
            }

            /// Reads a slice from the ring buffer.
            /// Must be consumed by calling .read().
            fn readable_slice(self: *BlockRingBuffer) Slice {
                assert(self.read_outstanding == null);
                stdx.maybe(self.write_outstanding == null);

                const start = self.inner.index;
                const len = @min(self.inner.count, @divExact(self.inner.buffer.len, 2));

                log.info("BlockRingBuffer.readable_slice() inner.buffer.len: {}, inner.index: {}, inner.count: {} slicing (start = {}, len = {})", .{ self.inner.buffer.len, self.inner.index, self.inner.count, start, len });

                if (self.write_outstanding) |write_outstanding| {
                    // FIXME: Assert no overlap between write_outstanding and {start, len}.
                    _ = write_outstanding;
                }

                self.read_outstanding = .{ .start = start, .len = len };
                return self.inner.as_slice(start, len);
            }

            fn read(self: *BlockRingBuffer, len: usize) void {
                assert(self.read_outstanding != null);
                assert(len <= self.read_outstanding.?.len);
                assert(len <= @divExact(self.inner.buffer.len, 2));

                self.read_outstanding = null;

                // FIXME: Wait what is this lolgic?
                self.inner.index = (self.inner.index + len) % self.inner.buffer.len;
                self.inner.count -= len;
            }

            /// Returns a slice into the ring buffer that can be written to. Only one
            /// writable_slice can be active at a time.
            /// Must be persisted by calling write().
            fn writable_slice(self: *BlockRingBuffer) Slice {
                assert(self.write_outstanding == null);
                stdx.maybe(self.read_outstanding == null);

                const start = self.inner.index + self.inner.count;
                const len = @min(self.inner.buffer.len - self.inner.count, @divExact(self.inner.buffer.len, 2));

                log.info("BlockRingBuffer.writable_slice() inner.buffer.len: {}, inner.index: {}, inner.count: {} slicing (start = {}, len = {})", .{ self.inner.buffer.len, self.inner.index, self.inner.count, start, len });

                self.write_outstanding = .{ .start = start, .len = len };
                return self.inner.as_slice(start, len);
            }

            fn write(self: *BlockRingBuffer, len: usize) void {
                assert(self.write_outstanding != null);
                assert(len <= self.write_outstanding.?.len);
                assert(len <= @divExact(self.inner.buffer.len, 2));

                log.info("BlockRingBuffer.write({})", .{len});
                self.write_outstanding = null;

                self.inner.count += len;
                assert(self.inner.count <= self.inner.buffer.len);
            }
        };

        pub const CompactionBlocks = struct {
            /// Index blocks are global, and shared between blips.
            /// FIXME: This complicates things somewhat.
            source_index_blocks: []CompactionBlock,

            /// For each source level, we have a ring buffer of CompactionBlocks.
            source_value_blocks: [2]BlockRingBuffer,

            /// We only have one ring buffer of output CompactionBlocks.
            target_value_blocks: BlockRingBuffer,
        };

        pub const CompactionBlock = struct {
            block: BlockPtr,

            // CompactionBlocks are stored in buffers where we need a pointer to get back to our
            // parent.
            target: ?*anyopaque = null,

            // FIXME: This can very much be a union in future!
            read: Grid.Read = undefined,
            write: Grid.Write = undefined,
        };
    };
}

pub fn CompactionInterfaceType(comptime Grid: type, comptime tree_infos: anytype) type {
    const Helpers = CompactionHelperType(Grid);

    return struct {
        const Dispatcher = T: {
            var type_info = @typeInfo(union(enum) {});

            // Union fields for each compaction type.
            for (tree_infos) |tree_info| {
                const Compaction = tree_info.Tree.Compaction;
                const type_name = @typeName(Compaction);

                for (type_info.Union.fields) |field| {
                    if (std.mem.eql(u8, field.name, type_name)) {
                        break;
                    }
                } else {
                    type_info.Union.fields = type_info.Union.fields ++ [_]std.builtin.Type.UnionField{.{
                        .name = type_name,
                        .type = *Compaction,
                        .alignment = @alignOf(*Compaction),
                    }};
                }
            }

            // We need a tagged union for dynamic dispatching.
            type_info.Union.tag_type = blk: {
                const union_fields = type_info.Union.fields;
                var tag_fields: [union_fields.len]std.builtin.Type.EnumField =
                    undefined;
                for (&tag_fields, union_fields, 0..) |*tag_field, union_field, i| {
                    tag_field.* = .{
                        .name = union_field.name,
                        .value = i,
                    };
                }

                break :blk @Type(.{ .Enum = .{
                    .tag_type = std.math.IntFittingRange(0, tag_fields.len - 1),
                    .fields = &tag_fields,
                    .decls = &.{},
                    .is_exhaustive = true,
                } });
            };

            break :T @Type(type_info);
        };

        const Self = @This();

        dispatcher: Dispatcher,
        info: CompactionInfo,

        pub fn init(info: CompactionInfo, compaction: anytype) @This() {
            const Compaction = @TypeOf(compaction.*);
            const type_name = @typeName(Compaction);

            return .{
                .info = info,
                .dispatcher = @unionInit(Dispatcher, type_name, compaction),
            };
        }

        pub fn bar_setup_budget(self: *const Self, beats_max: u64, target_index_blocks: Helpers.BlockRingBuffer) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.bar_setup_budget(beats_max, target_index_blocks),
            };
        }

        pub fn beat_grid_reserve(self: *Self) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.beat_grid_reserve(),
            };
        }

        pub fn beat_blocks_assign(self: *Self, blocks: Helpers.CompactionBlocks) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.beat_blocks_assign(blocks),
            };
        }

        // FIXME: Very unhappy with the callback style here!
        pub fn blip_read(self: *Self, callback: BlipCallback) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_read(callback, self),
            };
        }

        pub fn blip_merge(self: *Self, callback: BlipCallback) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_merge(callback, self),
            };
        }

        pub fn blip_write(self: *Self, callback: BlipCallback) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.blip_write(callback, self),
            };
        }

        pub fn beat_grid_forfeit(self: *Self) void {
            return switch (self.dispatcher) {
                inline else => |compaction_impl| compaction_impl.beat_grid_forfeit(),
            };
        }
    };
}

pub fn CompactionType(
    comptime Table: type,
    comptime Tree: type,
    comptime Storage: type,
) type {
    return struct {
        const Helpers = CompactionHelperType(Grid);
        const Compaction = @This();

        const Grid = GridType(Storage);
        pub const Tree_ = Tree;

        const Manifest = ManifestType(Table, Storage);
        const TableInfo = TableInfoType(Table);
        const TableInfoReference = Manifest.TableInfoReference;
        const CompactionRange = Manifest.CompactionRange;

        const Key = Table.Key;
        const Value = Table.Value;
        const key_from_value = Table.key_from_value;
        const tombstone = Table.tombstone;

        const TableInfoA = union(enum) {
            immutable: *Tree.TableMemory,
            disk: TableInfoReference,
        };

        // THis name tho :(
        /// The BlockRingBufferValueIterator has a lifetime over the entire bar, but its backing
        /// buffer (the BlockRingBuffer) only has a lifetime of a beat.
        const BlockRingBufferValueIterator = struct {
            const Position = struct {
                value_block: usize = 0,
                value_block_index: usize = 0,
            };

            ring_buffer: ?*Helpers.BlockRingBuffer = null,
            readable_slice: ?*Helpers.BlockRingBuffer.Slice = null,
            blocks_fully_consumed: usize = 0,
            position: Position = .{},
            last_value: ?Value = null,

            pub fn init() BlockRingBufferValueIterator {
                return .{};
            }

            /// Returns the number of values that are in memory (_not_ the total number of values
            /// remaining).
            pub fn remaining_in_memory(self: *BlockRingBufferValueIterator) usize {
                assert(self.ring_buffer != null);
                assert(self.readable_slice != null);

                if (self.readable_slice.?.count() == 0 or self.readable_slice.?.head_index == self.readable_slice.?.count())
                    return 0;

                return result: {
                    const head_remaining = Table.data_block_values_used(self.readable_slice.?.head_ptr().block)[self.position.value_block_index..].len;
                    var rest_remaining: usize = 0;
                    for (self.readable_slice.?.head_index + 1..self.readable_slice.?.count()) |i| {
                        rest_remaining += Table.data_block_values_used(self.readable_slice.?.get_ptr(i).block).len;

                        // FIXME: If not last, assert full.
                    }
                    break :result head_remaining + rest_remaining;
                };
            }

            // FIXME: Ignoring performance for now, lets do it naively.
            pub fn next(self: *BlockRingBufferValueIterator) ?Value {
                assert(self.ring_buffer != null);
                assert(self.readable_slice != null);

                std.log.info("next(): head_index: {}, count: {}, value_block_index: {}", .{ self.readable_slice.?.head_index, self.readable_slice.?.count(), self.position.value_block_index });

                const current_values = Table.data_block_values_used(self.readable_slice.?.head_ptr().block);
                const value = current_values[self.position.value_block_index];

                if (self.position.value_block_index + 1 == current_values.len) {
                    self.blocks_fully_consumed += 1;

                    self.position.value_block_index = 0;
                    self.position.value_block += 1;
                    self.readable_slice.?.head_index += 1;
                    if (self.readable_slice.?.head_index == self.readable_slice.?.count()) {
                        return null;
                    }
                } else {
                    self.position.value_block_index += 1;
                }

                assert(self.last_value == null or key_from_value(&self.last_value.?) < key_from_value(&value));

                self.last_value = value;
                return value;
            }

            pub fn ring_buffer_set(self: *BlockRingBufferValueIterator, ring_buffer: *Helpers.BlockRingBuffer, readable_slice: *Helpers.BlockRingBuffer.Slice) void {
                std.log.info("RB SET", .{});
                assert(self.ring_buffer == null);
                assert(self.readable_slice == null);

                self.ring_buffer = ring_buffer;
                self.readable_slice = readable_slice;
            }

            pub fn ring_buffer_clear(self: *BlockRingBufferValueIterator) void {
                std.log.info("RB clear - fully consumed {}", .{self.blocks_fully_consumed});
                assert(self.ring_buffer != null);
                assert(self.readable_slice != null);

                self.ring_buffer.?.read(self.blocks_fully_consumed);

                self.blocks_fully_consumed = 0;
                self.ring_buffer = null;
                self.readable_slice = null;
            }
        };

        const Bar = struct {
            tree: *Tree,

            /// `op_min` is the first op/beat of this compaction's half-bar.
            /// `op_min` is used as a snapshot — the compaction's input tables must be visible
            /// to `op_min`.
            ///
            /// After this compaction finishes:
            /// - `op_min + half_bar_beat_count - 1` will be the input tables' snapshot_max.
            /// - `op_min + half_bar_beat_count` will be the output tables' snapshot_min.
            op_min: u64,

            /// Whether this compaction will use the move-table optimization.
            /// Specifically, this field is set to True if the optimal compaction
            /// table in level A can simply be moved to level B.
            move_table: bool,

            table_info_a: TableInfoA,
            range_b: CompactionRange,

            /// Levels may choose to drop tombstones if keys aren't included in the lower levels.
            /// This invariant is always true for the last level as it doesn't have any lower ones.
            drop_tombstones: bool,

            /// Number of beats we should aim to finish this compaction in. It might be fewer, but it'll
            /// never be more.
            beats_max: ?u64,
            compaction_tables_value_count: u64,
            per_beat_input_goal: u64 = 0,

            /// The total number of input values processed by this compaction across the bar. Must equal
            /// compaction_tables_value_count by the bar_finish.
            source_values_processed: u64 = 0,

            /// When level_b == 0, it means level_a is the immutable table, which is special in a
            /// few ways:
            /// * It uses an iterator interface, as opposed to raw blocks like the rest.
            /// * It is responsible for keeping track of its own position, across beats.
            /// * It encompasses all possible values, so we don't need to worry about reading more.
            source_a: Tree.TableMemory.Iterator, //union(enum) { immutable: Tree.TableMemory.Iterator, disk: ValueBlocksIterator },

            /// level_b always comes from disk, and always starts a bar at (0, 0, 0).
            source_b: BlockRingBufferValueIterator = .{},

            /// At least 2 output index blocks needs to span beat boundaries, otherwise it wouldn't be
            /// possible to pace at a more granular level than tables.
            target_index_blocks: ?Helpers.BlockRingBuffer,

            /// Manifest log appends are queued up until `finish()` is explicitly called to ensure
            /// they are applied deterministically relative to other concurrent compactions.
            // Worst-case manifest updates:
            // See docs/internals/lsm.md "Compaction Table Overlap" for more detail.
            manifest_entries: stdx.BoundedArray(struct {
                operation: enum {
                    // FIXME: Perhaps MSB ordering (level_b_insert) etc
                    insert_to_level_b,
                    move_to_level_b,
                },
                table: TableInfo,
            }, constants.lsm_growth_factor + 1) = .{},

            table_builder: Table.Builder = .{},

            // Keep track of the last key from table a and b respectively. Used to assert we are
            // processing data in sequential order and not missing anything.
            // last_blip_merge_keys: [2]?Key = .{ null, null },
        };

        const Beat = struct {
            const Read = struct {
                callback: BlipCallback,
                ptr: *anyopaque,

                pending_reads_index: usize = 0,
                pending_reads_data: usize = 0,

                next_tick: Grid.NextTick = undefined,
                timer: std.time.Timer,
                timer_read: usize = 0,
            };
            const Merge = struct {
                callback: BlipCallback,
                ptr: *anyopaque,

                // These are blip local state. The value of target_value_block_index is copied out
                // at the end of the merge (by reslicing the blocks), so that the upcoming
                // blip_write knows what to write.
                target_value_block_index: usize = 0,

                next_tick: Grid.NextTick = undefined,
                timer: std.time.Timer,
            };
            const Write = struct {
                callback: BlipCallback,
                ptr: *anyopaque,

                pending_writes: usize = 0,

                next_tick: Grid.NextTick = undefined,
                timer: std.time.Timer,
            };

            grid_reservation: ?Grid.Reservation,

            blocks: ?Helpers.CompactionBlocks = null,

            source_values_processed: u64 = 0,

            // Unlike other places where we can use a single state enum, a single Compaction
            // instance is _expected_ to be reading, writing and merging all at once. These
            // are not disjoint states!
            //
            // {read,merge,write} are considered inactive if their context is null.
            read: ?Read = null,
            merge: ?Merge = null,
            write: ?Write = null,

            fn activate_and_assert(self: *Beat, stage: BlipStage, callback: BlipCallback, ptr: *anyopaque) void {
                switch (stage) {
                    .read => {
                        assert(self.read == null);
                        // assert(self.merge == null or self.merge_split != self.read_split);
                        // assert(self.write == null or self.read_split == self.write_split);

                        self.read = .{
                            .callback = callback,
                            .ptr = ptr,
                            .timer = std.time.Timer.start() catch unreachable,
                        };
                        self.read.?.timer.reset();
                    },
                    .merge => {
                        assert(self.merge == null);
                        // assert(self.read == null or self.merge_split != self.read_split);
                        // assert(self.write == null or self.merge_split != self.write_split);

                        self.merge = .{
                            .callback = callback,
                            .ptr = ptr,
                            .timer = std.time.Timer.start() catch unreachable,
                        };
                        self.merge.?.timer.reset();
                    },
                    .write => {
                        assert(self.write == null);
                        // assert(self.merge == null or self.merge_split != self.write_split);
                        // assert(self.read == null or self.read_split == self.write_split);

                        self.write = .{
                            .callback = callback,
                            .ptr = ptr,
                            .timer = std.time.Timer.start() catch unreachable,
                        };
                        self.write.?.timer.reset();
                    },
                }
            }

            fn deactivate_and_assert_and_callback(self: *Beat, stage: BlipStage, exhausted: ?Exhausted) void {
                switch (stage) {
                    .read => {
                        assert(self.read != null);
                        assert(self.read.?.pending_reads_index == 0);
                        assert(self.read.?.pending_reads_data == 0);

                        const callback = self.read.?.callback;
                        const ptr = self.read.?.ptr;

                        self.read = null;

                        callback(ptr, exhausted);
                    },
                    .merge => {
                        assert(self.merge != null);

                        const callback = self.merge.?.callback;
                        const ptr = self.merge.?.ptr;

                        self.merge = null;

                        callback(ptr, exhausted);
                    },
                    .write => {
                        assert(self.write != null);
                        assert(self.write.?.pending_writes == 0);

                        const callback = self.write.?.callback;
                        const ptr = self.write.?.ptr;

                        self.write = null;

                        callback(ptr, exhausted);
                    },
                }
            }

            fn assert_all_inactive(self: *Beat) void {
                assert(self.read == null);
                assert(self.merge == null);
                assert(self.write == null);
            }
        };

        // Passed by `init`.
        tree_config: Tree.Config,
        level_b: u8,
        grid: *Grid,

        // Populated by {bar,beat}_setup.
        bar: ?Bar,
        beat: ?Beat,

        pub fn init(tree_config: Tree.Config, grid: *Grid, level_b: u8) !Compaction {
            assert(level_b < constants.lsm_levels);

            return Compaction{
                .tree_config = tree_config,
                .grid = grid,
                .level_b = level_b,

                .bar = null,
                .beat = null,
            };
        }

        pub fn deinit(compaction: *Compaction) void {
            _ = compaction;
        }

        pub fn reset(compaction: *Compaction) void {
            // FIXME: Ensure blocks are released... Also what if bar is null.
            compaction.bar.?.table_builder.reset();

            compaction.* = .{
                .tree_config = compaction.tree_config,
                .grid = compaction.grid,
                .level_b = compaction.level_b,

                .bar = null,
                .beat = null,
            };
        }

        pub fn assert_between_bars(compaction: *const Compaction) void {
            assert(compaction.bar == null);
            assert(compaction.beat == null);
        }

        /// Perform the bar-wise setup, and returns the compaction work that needs to be done for
        /// scheduling decisions. Returns null if there's no compaction work, or if move_table
        /// is happening (since it only touches the manifest).
        pub fn bar_setup(compaction: *Compaction, tree: *Tree, op: u64) ?CompactionInfo {
            assert(compaction.bar == null);
            assert(compaction.beat == null);

            var compaction_tables_value_count: usize = 0;

            // level_b 0 is special; unlike all the others which have level_a on disk, level 0's
            // level_a comes from the immutable table. This means that blip_read will be a partial,
            // no-op, and that the minimum input blocks are lowered by one.
            // TODO: Actually make use of the above information.
            if (compaction.level_b == 0) {
                // Do not start compaction if the immutable table does not require compaction.
                if (tree.table_immutable.mutability.immutable.flushed) {
                    return null;
                }

                const values_count = tree.table_immutable.count();
                assert(values_count > 0);

                const range_b = tree.manifest.immutable_table_compaction_range(
                    tree.table_immutable.key_min(),
                    tree.table_immutable.key_max(),
                );

                // +1 to count the immutable table (level A).
                assert(range_b.tables.count() + 1 <= compaction_tables_input_max);
                assert(range_b.key_min <= tree.table_immutable.key_min());
                assert(tree.table_immutable.key_max() <= range_b.key_max);

                log.info("{s}: compacting immutable table to level 0 " ++
                    "(snapshot_min={d} compaction.op_min={d} table_count={d} values={d})", .{
                    tree.config.name,
                    tree.table_immutable.mutability.immutable.snapshot_min,
                    op,
                    range_b.tables.count() + 1,
                    values_count,
                });

                compaction_tables_value_count += values_count;
                for (range_b.tables.const_slice()) |*table| {
                    std.log.info("XXXXXXXXXXXXXX values coming from range_b: {}", .{table.table_info.value_count});
                    compaction_tables_value_count += table.table_info.value_count;
                }

                compaction.bar = .{
                    .tree = tree,
                    .op_min = op,

                    .move_table = false,
                    .table_info_a = .{ .immutable = &tree.table_immutable },
                    .range_b = range_b,
                    .drop_tombstones = tree.manifest.compaction_must_drop_tombstones(
                        compaction.level_b,
                        range_b,
                    ),

                    .source_a = tree.table_immutable.iterator(),

                    .compaction_tables_value_count = compaction_tables_value_count,

                    .target_index_blocks = null,
                    .beats_max = null,
                };
            } else {
                const level_a = compaction.level_b - 1;

                // Do not start compaction if level A does not require compaction.
                const table_range = tree.manifest.compaction_table(level_a) orelse return null;
                // FIXME: For now
                assert(false);

                const table_a = table_range.table_a.table_info;
                const range_b = table_range.range_b;

                assert(range_b.tables.count() + 1 <= compaction_tables_input_max);
                assert(table_a.key_min <= table_a.key_max);
                assert(range_b.key_min <= table_a.key_min);
                assert(table_a.key_max <= range_b.key_max);

                log.info("{s}: compacting {d} tables from level {d} to level {d}", .{
                    tree.config.name,
                    range_b.tables.count() + 1,
                    level_a,
                    compaction.level_b,
                });

                compaction_tables_value_count += table_a.value_count;
                for (range_b.tables.const_slice()) |*table|
                    compaction_tables_value_count += table.table_info.value_count;

                const perform_move_table = range_b.tables.empty();

                compaction.bar = .{
                    .tree = tree,
                    .op_min = op,

                    .move_table = perform_move_table,
                    .table_info_a = .{ .disk = table_range.table_a },
                    .range_b = range_b,
                    .drop_tombstones = tree.manifest.compaction_must_drop_tombstones(
                        compaction.level_b,
                        range_b,
                    ),

                    .source_a = tree.table_immutable.iterator(), // FIXME: BOGUS!

                    .compaction_tables_value_count = compaction_tables_value_count,

                    .target_index_blocks = null,
                    .beats_max = null,
                };

                // Return null if move_table is used. We still need to set our bar state above, as
                // it's what keeps track of the manifest updates to be applied synchronously at
                // the end of the bar.
                if (perform_move_table) {
                    compaction.move_table();
                    return null;
                }
            }

            // The last level must always drop tombstones.
            assert(compaction.bar.?.drop_tombstones or compaction.level_b < constants.lsm_levels - 1);

            return .{
                .compaction_tables_value_count = compaction_tables_value_count,
                .target_key_min = compaction.bar.?.range_b.key_min,
                .target_key_max = compaction.bar.?.range_b.key_max,
            };
        }

        /// Setup the per beat budget, as well as the output index blocks. Done in a separate step to bar_setup()
        /// since the forest requires information from that step to calculate how it should split the work, and
        /// if there's move table, target_index_blocks must be len 0.
        // Minimum of 1, max lsm_growth_factor+1 of target_index_blocks.
        // FIXME: Distill to set_value_count_per_beat
        /// beats_max is the number of beats that this compaction will have available to do its work.
        /// A compaction may be done before beats_max, if eg tables are mostly empty.
        /// Output index blocks are special, and are allocated at a bar level unlike all the other blocks
        /// which are done at a beat level. This is because while we can ensure we fill a value block, index
        /// blocks are too infrequent (one per table) to divide compaction by.
        pub fn bar_setup_budget(compaction: *Compaction, beats_max: u64, target_index_blocks: Helpers.BlockRingBuffer) void {
            assert(beats_max <= constants.lsm_batch_multiple);
            assert(compaction.bar != null);
            assert(compaction.beat == null);

            const bar = &compaction.bar.?;

            assert(bar.per_beat_input_goal == 0);

            // FIXME: Actually move this calc into beat_grid_reserve, and subtract the values we've already done from it.
            // This way we self correct our pacing!
            // FIXME: Naming of per_beat_input_goal: value_count_per_beat
            bar.per_beat_input_goal = stdx.div_ceil(bar.compaction_tables_value_count, beats_max);
            bar.target_index_blocks = target_index_blocks;

            if (bar.move_table) {
                // FIXME: Asserts here
                // assert(target_index_blocks.len == 0);
                // assert(compaction.bar.?.per_beat_input_goal == 0);
            } else {
                // assert(target_index_blocks.len > 0);
                assert(bar.per_beat_input_goal > 0);
            }

            // log.info("Set up budget: OI: [0][0]: {*}, [1][0]: {*}", .{ target_index_blocks[0][0], target_index_blocks[1][0] });

            // FIXME: Ok, so this gets set once, but we do an extra value block. What we should do is recalculate this dynamically after each beat, to better spread
            // the work out....
            log.info("Total: {} per beat goal: {}", .{ bar.compaction_tables_value_count, bar.per_beat_input_goal });
        }

        /// Reserve blocks from the grid for this beat's worth of work, in the semi-worst case:
        /// - no tombstones are dropped,
        /// - no values are overwritten,
        /// - but, we know exact input value counts, so table fullness *is* accounted for.
        ///
        /// We must reserve before doing any async work so that the block acquisition order
        /// is deterministic (relative to other concurrent compactions).
        pub fn beat_grid_reserve(
            compaction: *Compaction,
        ) void {
            assert(compaction.bar != null);
            assert(compaction.beat == null);

            const bar = &compaction.bar.?;
            assert(bar.per_beat_input_goal > 0);

            // If we're move_table, only the manifest is being updated, *not* the grid.
            assert(!bar.move_table);

            const value_blocks_per_beat = stdx.div_ceil(
                bar.per_beat_input_goal,
                Table.layout.block_value_count_max,
            );
            // FIXME: What if we have partially filled index block from previous beat, that we now fill - do we need a +1?
            const index_blocks_per_beat = stdx.div_ceil(
                value_blocks_per_beat,
                Table.data_block_count_max,
            );
            const total_blocks_per_beat = index_blocks_per_beat + value_blocks_per_beat;

            // TODO The replica must stop accepting requests if it runs out of blocks/capacity,
            // rather than panicking here.
            // (actually, we want to still panic but with something nicer like vsr.fail)
            const grid_reservation = compaction.grid.reserve(total_blocks_per_beat).?;

            compaction.beat = .{
                .grid_reservation = grid_reservation,
            };
        }

        pub fn beat_blocks_assign(compaction: *Compaction, blocks: Helpers.CompactionBlocks) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            compaction.beat.?.blocks = blocks;
        }

        // Our blip pipeline is 3 stages long, and split into read, merge and write stages. The
        // merge stage has a data dependency on both the read (source) and write (target) stages.
        //
        // Within a single compaction, the pipeline looks something like:
        // --------------------------------------------------
        // | Ra₀    | Ca₀     | Wa₀     | Ra₁ → D |          |
        // --------------------------------------------------
        // |       | Ra₁     | Ca₁     | Wa₁     |           |
        // --------------------------------------------------
        // |       |        | Ra₀     | Ca₀ → E | Wb₀       |
        // --------------------------------------------------
        //
        // Where → D means that the result of the read were discarded, and → E means that the merge
        // step indicated our work was complete for either this beat or bar.
        //
        // Internally, we have a split counter - the first time blip_read() is called, it works on
        // buffer split 0, the next time on buffer set 1 and this alternates. The same process
        // happens with blip_merge() and blip_write(), which we represent as eg blip_merge(0).
        //
        // At the moment, the forest won't pipeline different compactions from other tree-levels
        // together. It _can_ do this, but it requires a bit more thought in how memory is managed.
        //
        // IO work is always submitted to the kernel _before_ entering blip_merge().
        //
        // TODO: even without a threadpool, we can likely drive better performance by doubling up
        // the stages. The reason for this is that we expect blip_merge() to be quite a bit quicker
        // than blip_write().

        /// Perform read IO to fill our source_index_blocks and source_value_blocks with as many
        /// blocks as we can, given their sizes, and where we are in the amount of work we need to
        /// do this beat.
        pub fn blip_read(compaction: *Compaction, callback: BlipCallback, ptr: *anyopaque) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const beat = &compaction.beat.?;
            beat.activate_and_assert(.read, callback, ptr);

            compaction.blip_read_index();
        }

        // FIXME: This should only read the index blocks if we need to. Currently it behaves like a
        // half stage.
        fn blip_read_index(compaction: *Compaction) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const bar = &compaction.bar.?;
            const beat = &compaction.beat.?;
            const blocks = &beat.blocks.?;

            assert(beat.read != null);
            const read = &beat.read.?;

            // index_block_a will always point to source_index_blocks[0] (even though if our source
            // is immutable this isn't needed! future optimization)
            // index_block_b will be the index block of the table we're currently merging with.
            var read_target: usize = 0;
            switch (bar.table_info_a) {
                .disk => |table_ref| {
                    // FIXME: For testing, easier to reason about only the immutable -> disk case.
                    assert(false);

                    blocks.source_index_blocks[read_target].target = compaction;
                    compaction.grid.read_block(
                        .{ .from_local_or_global_storage = blip_read_index_callback },
                        &blocks.source_index_blocks[read_target].read,
                        table_ref.table_info.address,
                        table_ref.table_info.checksum,
                        .{ .cache_read = true, .cache_write = true },
                    );
                    read.pending_reads_index += 1;
                },
                .immutable => {
                    // Immutable values come from the in memory immutable table - no need to do any reads.
                },
            }

            // ALWAYS increment read_target for now, so index for table_a is in [0].
            if (read_target == 0) read_target += 1;

            // FIXME: This assumes we have 1 + lsm_growth_factor blocks available.
            assert(blocks.source_index_blocks.len >= bar.range_b.tables.count() + read_target);

            for (bar.range_b.tables.const_slice()) |table_ref| {
                blocks.source_index_blocks[read_target].target = compaction;
                compaction.grid.read_block(
                    .{ .from_local_or_global_storage = blip_read_index_callback },
                    &blocks.source_index_blocks[read_target].read,
                    table_ref.table_info.address,
                    table_ref.table_info.checksum,
                    .{ .cache_read = true, .cache_write = true },
                );
                read.pending_reads_index += 1;
                read_target += 1;
            }

            log.info("blip_read(): Scheduled {} index reads", .{
                read.pending_reads_index,
            });

            // Either we have pending index reads, in which case blip_read_data gets called by
            // blip_read_index_callback once all reads are done, or we don't, in which case call it
            // here.
            if (read.pending_reads_index == 0) {
                return compaction.blip_read_data();
            }
        }

        fn blip_read_index_callback(grid_read: *Grid.Read, index_block: BlockPtrConst) void {
            const parent = @fieldParentPtr(Helpers.CompactionBlock, "read", grid_read);
            const compaction: *Compaction = @alignCast(@ptrCast(parent.target));
            assert(compaction.bar != null);
            assert(compaction.beat != null);
            assert(compaction.tree_config.id == schema.TableIndex.metadata(index_block).tree_id);

            const beat = &compaction.beat.?;

            assert(beat.read != null);
            const read = &beat.read.?;

            read.pending_reads_index -= 1;
            read.timer_read += 1;

            stdx.copy_disjoint(
                .exact,
                u8,
                parent.block,
                index_block,
            );
            log.info("blip_read({}): Copied index block.", .{0});

            // FIXME: Not sure if I like this too much. According to release_table_blocks, it'll only release at the end of the bar, so should be ok?
            // FIXME: It's critical to release blocks, so ensure this is done properly.
            // compaction.release_table_blocks(index_block);

            if (read.pending_reads_index != 0) return;

            compaction.blip_read_data();
        }

        fn blip_read_data(compaction: *Compaction) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const bar = &compaction.bar.?;
            const beat = &compaction.beat.?;

            assert(beat.read != null);
            const read = &beat.read.?;

            assert(read.pending_reads_data == 0);

            // Read data for table a - which we'll only have if compaction.level_b > 0.
            if (bar.table_info_a == .disk) {
                assert(false); // FIXME: Unsupported for now!
                // const index_block = beat.blocks.source_index_blocks[0];
                // const index_schema = schema.TableIndex.from(index_block);

                // const value_blocks_used = index_schema.data_blocks_used(index_block);
                // // assert(bar.current_table_a_value_block_index < value_blocks_used);

                // const value_block_addresses = index_schema.data_addresses_used(index_block);
                // const value_block_checksums = index_schema.data_checksums_used(index_block);

                // while (value_blocks_read_a < beat.blocks.source_value_blocks[beat.read_split][0].len and value_blocks_read_a < value_blocks_used) {
                //     beat.grid_reads[read.pending_reads_data].target = compaction;
                //     beat.grid_reads[read.pending_reads_data].hack = read.pending_reads_data;
                //     compaction.grid.read_block(
                //         .{ .from_local_or_global_storage = blip_read_data_callback },
                //         &beat.grid_reads[read.pending_reads_data].read,
                //         value_block_addresses[value_blocks_read_a],
                //         value_block_checksums[value_blocks_read_a].value,
                //         .{ .cache_read = true, .cache_write = true },
                //     );

                //     read.pending_reads_data += 1;
                //     value_blocks_read_a += 1;
                // }
            }

            // Read data for our tables in range b, which will always come from disk.
            const table_b_count = bar.range_b.tables.count();

            var source_b_value_blocks = beat.blocks.?.source_value_blocks[1].writable_slice();
            var previous_schema: ?schema.TableIndex = null;
            var current_table_b_index_block_index: usize = 0; // FIXME: Hardcoded to 0 for now.

            // table_loop: while (current_table_b_index_block_index < table_b_count) : (current_table_b_index_block_index += 1) {
            if (table_b_count == 1) {
                // The 1 + is to skip over the table a index block.
                const index_block = beat.blocks.?.source_index_blocks[1 + current_table_b_index_block_index].block;
                const index_schema = schema.TableIndex.from(index_block);
                assert(previous_schema == null or stdx.equal_bytes(schema.TableIndex, &previous_schema.?, &index_schema));
                previous_schema = index_schema;

                const value_blocks_used = index_schema.data_blocks_used(index_block);
                _ = value_blocks_used;

                const value_block_addresses = index_schema.data_addresses_used(index_block);
                const value_block_checksums = index_schema.data_checksums_used(index_block);

                // std.log.info(".... this current_table_b_index_block_index({}) has {} used value blocks. We are on {}", .{ current_table_b_index_block_index, value_blocks_used, bar.current_table_b_value_block_index });
                // assert(bar.current_table_b_value_block_index < value_blocks_used);
                // Try read in as many value blocks as this index block has...
                var i: usize = bar.source_b.position.value_block;
                while (i < source_b_value_blocks.count() and source_b_value_blocks.head_index < source_b_value_blocks.count()) {
                    const compaction_block = source_b_value_blocks.pop_ptr();

                    compaction_block.target = compaction;
                    log.info("blip_read(): Issuing a value read for 0x{x}", .{@intFromPtr(compaction_block.block)});
                    compaction.grid.read_block(
                        .{ .from_local_or_global_storage = blip_read_data_callback },
                        &compaction_block.read,
                        value_block_addresses[i],
                        value_block_checksums[i].value,
                        .{ .cache_read = true, .cache_write = true },
                    );

                    read.pending_reads_data += 1;
                    i += 1;
                    // bar.current_table_b_value_block_index += 1;

                    // But, once our read buffer is full, break out of the outer loop.
                    // if (value_blocks_read_b == beat.blocks.source_value_blocks[beat.read_split][1].len) {
                    //     break; //:table_loop;
                    // }
                }

                // If we're here, it means we're incrementing our active index block. Reset the value block index to 0 too
                // bar.current_table_b_value_block_index = 0;
            } else {
                assert(table_b_count == 0);
            }

            beat.blocks.?.source_value_blocks[1].write(source_b_value_blocks.head_index);
            log.info("blip_read(): Scheduled {} data reads.", .{read.pending_reads_data});

            // Either we have pending data reads, in which case blip_read_next_tick gets called by
            // blip_read_data_callback once all reads are done, or we don't, in which case call it
            // here via next_tick.
            if (read.pending_reads_data == 0) {
                compaction.grid.on_next_tick(blip_read_next_tick, &read.next_tick);
            }
        }

        fn blip_read_data_callback(grid_read: *Grid.Read, value_block: BlockPtrConst) void {
            const parent = @fieldParentPtr(Helpers.CompactionBlock, "read", grid_read);
            const compaction: *Compaction = @alignCast(@ptrCast(parent.target));

            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const beat = &compaction.beat.?;

            assert(beat.read != null);
            const read = &beat.read.?;

            read.pending_reads_data -= 1;
            read.timer_read += 1;

            // FIXME: This copies the block we should instead steal it...
            log.info("blip_read(): copying value block to 0x{x}", .{@intFromPtr(parent.block)});
            stdx.copy_disjoint(
                .exact,
                u8,
                parent.block,
                value_block,
            );

            // Join on all outstanding reads before continuing.
            if (read.pending_reads_data != 0) return;

            // Call the next tick handler directly. This callback is invoked async, so it's safe
            // from stack overflows.
            blip_read_next_tick(&read.next_tick);
        }

        fn blip_read_next_tick(next_tick: *Grid.NextTick) void {
            const read: *?Beat.Read = @ptrCast(@fieldParentPtr(Beat.Read, "next_tick", next_tick));
            const beat = @fieldParentPtr(Beat, "read", read);

            const duration = read.*.?.timer.read();
            log.info("blip_read(): Took {} to read all blocks - {}", .{ std.fmt.fmtDuration(duration), read.*.?.timer_read });

            beat.deactivate_and_assert_and_callback(.read, null);
        }

        /// Perform CPU merge work, to transform our source tables to our target tables.
        /// This has a data dependency on both the read buffers and the write buffers for the
        /// active split.
        ///
        /// blip_merge is also responsible for signalling when to stop blipping entirely. A
        /// sequence of blips is over when one of the following condition are met, considering we
        /// don't want to output partial value blocks unless we really really have to:
        ///
        /// * We have reached our per_beat_input_goal. Finish up the next value block, and we're
        ///   done.
        /// * We have no more source values remaining, at all - the bar is done. This will likely
        ///   result in a partially full value block, but that's OK (end of a table).
        /// * We have no more output value blocks remaining in our buffer - we might need more
        ///   blips, but that's up to the forest to orchestrate.
        /// * We have no more output index blocks remaining in our buffer - we might have a partial
        ///   value block here, but that's OK (end of a table).
        pub fn blip_merge(compaction: *Compaction, callback: BlipCallback, ptr: *anyopaque) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const bar = &compaction.bar.?;
            const beat = &compaction.beat.?;

            beat.activate_and_assert(.merge, callback, ptr);
            const merge = &beat.merge.?;

            var source_exhausted_bar = false;
            var source_exhausted_beat = false;

            assert(bar.table_builder.value_count < Table.layout.block_value_count_max);

            var source_a = &bar.source_a;
            var source_b = &bar.source_b;

            const blocks = &beat.blocks.?;
            const source_blocks_a = &blocks.source_value_blocks[0];
            _ = source_blocks_a;
            var source_blocks_b = blocks.source_value_blocks[1].readable_slice();
            var target_value_blocks = blocks.target_value_blocks.writable_slice();
            var target_index_blocks = bar.target_index_blocks.?.writable_slice();

            bar.source_b.ring_buffer_set(&blocks.source_value_blocks[1], &source_blocks_b);
            defer bar.source_b.ring_buffer_clear();

            var source_a_remaining = source_a.remaining();
            var source_b_remaining = source_b.remaining_in_memory();

            // // Loop through the CPU work until we have nothing left.
            while (source_a_remaining > 0 or source_b_remaining > 0) {
                // FIXME: We can store our key here (or even a full value) across blips, to assert we're starting
                // from the correct place each time!
                // const peek_key_a = if (source_a.peek()) |value| key_from_value(&value) else null;
                // const peek_key_b = if (source_b.peek()) |value| key_from_value(&value) else null;
                // assert(bar.last_blip_merge_keys[0] == null or bar.last_blip_merge_keys[0] == peek_key_a);
                // assert(bar.last_blip_merge_keys[1] == null or bar.last_blip_merge_keys[1] == peek_key_b);

                // std.log.info(">>>>>>>>>>>>> Merge a starting on: {?}", .{if (source_a.peek()) |*val| key_from_value(val) else null});
                // std.log.info(">>>>>>>>>>>>> Merge b starting on: {?}", .{if (source_b.peek()) |*val| key_from_value(val) else null});

                log.info("blip_merge(): remaining: values_a: {} and values_b: {}", .{ source_a_remaining, source_b_remaining });

                // Set the index block if needed.
                if (bar.table_builder.state == .no_blocks) {
                    const index_block = target_index_blocks.head_ptr().block;
                    log.info("blip_merge(): Setting target index block.", .{});
                    @memset(index_block, 0); // FIXME: We don't need to zero the whole block; just the part of the padding that's not covered by alignment.
                    bar.table_builder.set_index_block(index_block);
                }

                // Set the value block if needed.
                if (bar.table_builder.state == .index_block) {
                    const value_block = target_value_blocks.head_ptr().block;
                    log.info("blip_merge(): Setting target value block.", .{});
                    @memset(value_block, 0); // FIXME: We don't need to zero the whole block; just the part of the padding that's not covered by alignment.
                    bar.table_builder.set_data_block(value_block);
                }

                if (source_a_remaining == 0) {
                    assert(false);
                    // source_b.copy(&bar.table_builder);
                } else if (source_b_remaining == 0) {
                    if (bar.drop_tombstones) {
                        compaction.copy_drop_tombstones();
                    } else {
                        assert(false);
                        // source_a.copy(&bar.table_builder);
                    }
                } else {
                    assert(source_a_remaining > 0 or source_b_remaining > 0);
                    compaction.merge_values();
                }

                // std.log.info(">>>>>>>>>>>>> Merge a should resume from: {?}", .{if (source_a.peek()) |*val| key_from_value(val) else null});
                // std.log.info(">>>>>>>>>>>>> Merge b should resume from: {?}", .{if (source_b.peek()) |*val| key_from_value(val) else null});

                //     // bar.last_blip_merge_keys[0] = if (source_a.peek()) |value| key_from_value(&value) else null;
                //     // bar.last_blip_merge_keys[1] = if (source_b.peek()) |value| key_from_value(&value) else null;

                //     // FIXME: Setting these nicely.
                const source_values_processed = (source_a_remaining - source_a.remaining()) + (source_b_remaining - source_b.remaining_in_memory());
                std.log.info("source_b_processed this tick: {}", .{source_b_remaining - source_b.remaining_in_memory()});
                assert(source_values_processed > 0);

                beat.source_values_processed += source_values_processed;
                bar.source_values_processed += source_values_processed;
                source_a_remaining = source_a.remaining();
                source_b_remaining = source_b.remaining_in_memory();
                std.log.info("Processed {} source values this tick", .{source_values_processed});

                // When checking if we're done, there are two things we need to consider:
                // 1. Have we finished our input entirely? If so, we flush what we have - it's
                //    likely to be a partial block but that's OK.
                // 2. Have we reached our per_beat_input_goal? If so, we'll flush at the next
                //    complete value block.
                //
                // This means that we'll potentially overrun our per_beat_input_goal by up to
                // a full value block.
                source_exhausted_bar = bar.source_values_processed == bar.compaction_tables_value_count;
                source_exhausted_beat = beat.source_values_processed >= bar.per_beat_input_goal;

                log.info("blip_merge(): merged {} so far, goal {}. (source_exhausted_bar: {}, source_exhausted_beat: {}) (bar.source_values_processed: {}, bar.compaction_tables_value_count: {})", .{
                    beat.source_values_processed,
                    bar.per_beat_input_goal,
                    source_exhausted_bar,
                    source_exhausted_beat,
                    bar.source_values_processed,
                    bar.compaction_tables_value_count,
                });

                switch (compaction.check_and_finish_blocks(source_exhausted_bar, &target_index_blocks, &target_value_blocks)) {
                    .unfinished_value_block => continue,
                    .finished_value_block => if (source_exhausted_beat) break,
                    .need_write => {
                        std.log.info("blip_merge(): buffers exhausted, breaking for write.", .{});
                        break;
                    },
                }
            }

            // FIXME: Move these into the slice, so the slice has a .finish()?
            std.log.info("blip_merge(): calling target_index_blocks.write() with {}", .{target_index_blocks.head_index});
            bar.target_index_blocks.?.write(target_index_blocks.head_index);

            std.log.info("blip_merge(): calling target_value_blocks.write() with {}", .{target_value_blocks.head_index});
            blocks.target_value_blocks.write(target_value_blocks.head_index);

            // // FIXME: Check at least one output value.
            // // assert(filled <= target.len);
            // // if (filled == 0) assert(Table.usage == .secondary_index);

            const d = merge.timer.read();
            log.info("blip_merge(): Took {} to CPU merge blocks", .{std.fmt.fmtDuration(d)});

            beat.deactivate_and_assert_and_callback(.merge, .{
                .bar = source_exhausted_bar,
                .beat = source_exhausted_bar or source_exhausted_beat,
            });
        }

        fn check_and_finish_blocks(compaction: *Compaction, force_flush: bool, target_index_blocks: *Helpers.BlockRingBuffer.Slice, target_value_blocks: *Helpers.BlockRingBuffer.Slice) enum {
            unfinished_value_block,
            finished_value_block,
            need_write, // FIXME: Should be a noun
        } {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const bar = &compaction.bar.?;
            const beat = &compaction.beat.?;

            assert(beat.merge != null);

            const table_builder = &bar.table_builder;

            var output_blocks_full = false;
            var finished_value_block = false;

            // Flush the value block if needed.
            if (table_builder.data_block_full() or
                table_builder.index_block_full() or
                (force_flush and !table_builder.data_block_empty()))
            {
                log.info("blip_merge(): Finished target value block: 0x{x}", .{@intFromPtr(table_builder.data_block)});
                table_builder.data_block_finish(.{
                    .cluster = compaction.grid.superblock.working.cluster,
                    .address = compaction.grid.acquire(compaction.beat.?.grid_reservation.?),
                    .snapshot_min = snapshot_min_for_table_output(bar.op_min),
                    .tree_id = compaction.tree_config.id,
                });

                finished_value_block = true;
                target_value_blocks.head_index += 1;
                if (target_value_blocks.head_index == target_value_blocks.count() or force_flush) {
                    output_blocks_full = true;
                }
            }

            // Flush the index block if needed.
            if (table_builder.index_block_full() or
                // If the input is exhausted then we need to flush all blocks before finishing.
                (force_flush and !table_builder.index_block_empty()))
            {
                log.info("blip_merge(): Finished target index block: 0x{x}", .{@intFromPtr(table_builder.index_block)});
                const table = table_builder.index_block_finish(.{
                    .cluster = compaction.grid.superblock.working.cluster,
                    .address = compaction.grid.acquire(compaction.beat.?.grid_reservation.?),
                    .snapshot_min = snapshot_min_for_table_output(bar.op_min),
                    .tree_id = compaction.tree_config.id,
                });

                target_index_blocks.head_index += 1;
                if (target_index_blocks.head_index == target_index_blocks.count() or force_flush) {
                    output_blocks_full = true;
                }

                // Make this table visible at the end of this bar.
                bar.manifest_entries.append_assume_capacity(.{
                    .operation = .insert_to_level_b,
                    .table = table,
                });
            }

            if (output_blocks_full) return .need_write;
            if (finished_value_block) return .finished_value_block;
            return .unfinished_value_block;
        }

        /// Perform write IO to write our target_index_blocks and target_value_blocks to disk.
        pub fn blip_write(compaction: *Compaction, callback: BlipCallback, ptr: *anyopaque) void {
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const bar = &compaction.bar.?;
            const beat = &compaction.beat.?;

            beat.activate_and_assert(.write, callback, ptr);

            assert(beat.write != null);
            const write = &beat.write.?;

            log.info("blip_write(): starting sync", .{});

            assert(write.pending_writes == 0);

            // Write any complete index blocks.
            var target_index_blocks = bar.target_index_blocks.?.readable_slice();

            while (target_index_blocks.head_index < target_index_blocks.count()) {
                const compaction_block = target_index_blocks.pop_ptr();
                log.info("blip_write(): Issuing an index write for 0x{x}", .{@intFromPtr(compaction_block.block)});

                compaction_block.target = compaction;
                compaction.grid.create_block(blip_write_callback, &compaction_block.write, &compaction_block.block);
                write.pending_writes += 1;
            }
            bar.target_index_blocks.?.read(target_index_blocks.count());

            // Write any complete value blocks.
            var target_value_blocks = beat.blocks.?.target_value_blocks.readable_slice();

            while (target_value_blocks.head_index < target_value_blocks.count()) {
                const compaction_block = target_value_blocks.pop_ptr();
                log.info("blip_write(): Issuing a value write for 0x{x}", .{@intFromPtr(compaction_block.block)});

                compaction_block.target = compaction;
                compaction.grid.create_block(blip_write_callback, &compaction_block.write, &compaction_block.block);
                write.pending_writes += 1;
            }
            beat.blocks.?.target_value_blocks.read(target_value_blocks.count());

            const d = write.timer.read();
            log.info("blip_write(): Took {} to create {} blocks", .{ std.fmt.fmtDuration(d), write.pending_writes });
            write.timer.reset();

            // // FIXME: From 2023-12-21
            // // FIXME: The big idea is to make compaction pacing explicit and asserted behaviour rather than just an implicit property of the code

            if (write.pending_writes == 0) {
                compaction.grid.on_next_tick(blip_write_next_tick, &write.next_tick);
            }
        }

        fn blip_write_callback(grid_write: *Grid.Write) void {
            const parent = @fieldParentPtr(Helpers.CompactionBlock, "write", grid_write);
            const compaction: *Compaction = @alignCast(@ptrCast(parent.target));
            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const beat = &compaction.beat.?;

            const duration = beat.write.?.timer.read();
            std.log.info("Write complete for a block - timer at {}", .{std.fmt.fmtDuration(duration)});

            assert(beat.write != null);
            const write = &beat.write.?;
            write.pending_writes -= 1;

            // log.info("blip_write_callback for split {}", .{write_split});
            // Join on all outstanding writes before continuing.
            if (write.pending_writes != 0) return;

            // Call the next tick handler directly. This callback is invoked async, so it's safe
            // from stack overflows.
            blip_write_next_tick(&write.next_tick);
        }

        fn blip_write_next_tick(next_tick: *Grid.NextTick) void {
            const write: *?Beat.Write = @ptrCast(
                @fieldParentPtr(Beat.Write, "next_tick", next_tick),
            );
            const beat = @fieldParentPtr(Beat, "write", write);

            const duration = write.*.?.timer.read();
            log.info("blip_write(): all writes done - took {}.", .{std.fmt.fmtDuration(duration)});
            beat.deactivate_and_assert_and_callback(.write, null);
        }

        pub fn beat_grid_forfeit(compaction: *Compaction) void {
            // FIXME: Big hack - see beat_end comment
            if (compaction.beat == null) {
                return;
            }

            assert(compaction.bar != null);
            assert(compaction.beat != null);

            const beat = &compaction.beat.?;

            beat.assert_all_inactive();
            assert(compaction.bar.?.table_builder.data_block_empty());
            // assert(compaction.bar.?.table_builder.state == .index_block); // Hmmm

            if (beat.grid_reservation) |grid_reservation| {
                log.info("beat_grid_forfeit: forfeiting... {}", .{grid_reservation});
                compaction.grid.forfeit(grid_reservation);
                // We set the whole beat to null later.
            } else {
                assert(compaction.bar.?.move_table);
            }

            // Our beat is done!
            compaction.beat = null;
        }

        /// FIXME: Describe
        pub fn bar_finish(compaction: *Compaction, op: u64, tree: *Tree) void {
            log.info("bar_finish: running for compaction: {s} into level: {}", .{ compaction.tree_config.name, compaction.level_b });

            // If we're the compaction for immutable -> level 0, we need to swap our mutable / immutable
            // tables too. This needs to happen at the end of the first ever bar, which would normally
            // not have any work to do, so put it before our asserts.
            // FIXME: Do this in a better way
            if (compaction.level_b == 0) {
                // Mark the immutable table as flushed, if we were compacting into level 0.
                // FIXME: This is janky; current_block_a_index will be set to 0 above because
                // if there are no remaining values, it sets it like that.
                if (compaction.bar != null) {
                    // FIXME: Hack hackity hack, check and refactor me.
                    // assert(compaction.bar.?.current_block_a_index == 0);
                    compaction.bar.?.tree.table_immutable.mutability.immutable.flushed = true;
                }

                // FIXME: Double check snapshot logic.
                tree.swap_mutable_and_immutable(
                    snapshot_min_for_table_output(op + 1),
                );
            }

            if (compaction.bar == null and op + 1 == constants.lsm_batch_multiple) {
                return;
            }

            // Fixme: hmm
            if (compaction.bar == null) {
                return;
            }

            assert(compaction.beat == null);
            assert(compaction.bar != null);

            const bar = &compaction.bar.?;

            // Assert our input has been fully exhausted.
            assert(bar.source_values_processed == bar.compaction_tables_value_count);
            std.log.info("Processed a total of {} values this bar, out of {}", .{ bar.source_values_processed, bar.compaction_tables_value_count });

            // Each compaction's manifest updates are deferred to the end of the last
            // bar to ensure:
            // - manifest log updates are ordered deterministically relative to one another, and
            // - manifest updates are not visible until after the blocks are all on disk.
            const manifest = &bar.tree.manifest;
            const level_b = compaction.level_b;
            const snapshot_max = snapshot_max_for_table_input(bar.op_min);

            if (bar.move_table) {
                // If no compaction is required, don't update snapshot_max.
            } else {
                // These updates MUST precede insert_table() and move_table() since they use
                // references to modify the ManifestLevel in-place.
                switch (bar.table_info_a) {
                    .immutable => {},
                    .disk => |table_info| {
                        manifest.update_table(level_b - 1, snapshot_max, table_info);
                    },
                }
                for (bar.range_b.tables.const_slice()) |table| {
                    manifest.update_table(level_b, snapshot_max, table);
                }
            }

            for (bar.manifest_entries.slice()) |*entry| {
                switch (entry.operation) {
                    .insert_to_level_b => manifest.insert_table(level_b, &entry.table),
                    .move_to_level_b => manifest.move_table(level_b - 1, level_b, &entry.table),
                }
            }

            // Our bar is done!
            compaction.bar = null;
        }

        /// If we can just move the table, don't bother with merging.
        fn move_table(compaction: *Compaction) void {
            const bar = &compaction.bar.?;
            assert(bar.move_table);

            log.info(
                "{s}: Moving table: level_b={}",
                .{ compaction.tree_config.name, compaction.level_b },
            );

            const snapshot_max = snapshot_max_for_table_input(bar.op_min);
            const table_a = bar.table_info_a.disk.table_info;
            assert(table_a.snapshot_max >= snapshot_max);

            bar.manifest_entries.append_assume_capacity(.{
                .operation = .move_to_level_b,
                .table = table_a.*,
            });
        }

        // TODO: Support for LSM snapshots would require us to only remove blocks
        // that are invisible.
        fn release_table_blocks(compaction: *Compaction, index_block: BlockPtrConst) void {
            // Release the table's block addresses in the Grid as it will be made invisible.
            // This is safe; compaction.index_block_b holds a copy of the index block for a
            // table in Level B. Additionally, compaction.index_block_a holds
            // a copy of the index block for the Level A table being compacted.

            const grid = compaction.grid;
            const index_schema = schema.TableIndex.from(index_block);
            for (index_schema.data_addresses_used(index_block)) |address| grid.release(address);
            grid.release(Table.block_address(index_block));
        }

        // TODO: Add benchmarks for these CPU merge methods. merge_values() is the most general,
        // and could handle both what copy_drop_tombstones() and Iterator.copy() do, but we expect
        // copy() -> copy_drop_tombstones() -> merge_values() in terms of performance.

        // Looking for fn copy()? It exists as a method on either TableMemory.Iterator or
        // ValueBlocksIterator. Potentially, the value block case could be more optimal than
        // looping through an iterator (just a straight memcpy) but this should be benchmarked!

        /// Copy values from table_a to table_b, dropping tombstones as we go.
        fn copy_drop_tombstones(compaction: *Compaction) void {
            const bar = &compaction.bar.?;

            log.info("blip_merge: Merging via copy_drop_tombstones()", .{});
            assert(bar.source_b.remaining_in_memory() == 0);
            assert(bar.table_builder.value_count < Table.layout.block_value_count_max);

            // Copy variables locally to ensure a tight loop.
            // TODO: Actually benchmark this.
            var source_a_local = bar.source_a;
            const values_out = bar.table_builder.data_block_values();
            var values_out_index = bar.table_builder.value_count;

            // Merge as many values as possible.
            while (source_a_local.next()) |value_a| {
                if (tombstone(&value_a)) {
                    // TODO: What's the impact of this check? We could invert it since Table.usage
                    // is comptime known.
                    assert(Table.usage != .secondary_index);
                    continue;
                }
                values_out[values_out_index] = value_a;
                values_out_index += 1;

                if (values_out_index == values_out.len) break;
            }

            // Copy variables back out.
            bar.source_a = source_a_local;
            bar.table_builder.value_count = values_out_index;
        }

        /// Merge values from table_a and table_b, with table_a taking precedence. Tombstones may
        /// or may not be dropped depending on bar.drop_tombstones.
        fn merge_values(compaction: *Compaction) void {
            const bar = &compaction.bar.?;
            const drop_tombstones = bar.drop_tombstones;

            log.info("blip_merge: Merging via merge_values()", .{});
            assert(bar.source_a.remaining() > 0);
            assert(bar.source_b.remaining_in_memory() > 0);
            assert(bar.table_builder.value_count < Table.layout.block_value_count_max);

            // Copy variables locally to ensure a tight loop.
            // TODO: Actually benchmark this.
            var source_a_local = bar.source_a;
            var source_b_local = bar.source_b;
            const values_out = bar.table_builder.data_block_values();
            var values_out_index = bar.table_builder.value_count;

            var value_a = source_a_local.next();
            var value_b = source_b_local.next();

            // Merge as many values as possible.
            while (values_out_index < values_out.len) {
                // This is wrong as written! We'll drop a value!!
                if (value_a == null or value_b == null) break;

                switch (std.math.order(key_from_value(&value_a.?), key_from_value(&value_b.?))) {
                    .lt => {
                        if (drop_tombstones and
                            tombstone(&value_a.?))
                        {
                            assert(Table.usage != .secondary_index);
                            continue;
                        }
                        values_out[values_out_index] = value_a.?;
                        // std.log.info("Output stream lt: {}", .{key_from_value(&values_out[values_out_index])});
                        values_out_index += 1;

                        value_a = source_a_local.next();
                    },
                    .gt => {
                        values_out[values_out_index] = value_b.?;
                        // std.log.info("Output stream gt: {}", .{key_from_value(&values_out[values_out_index])});
                        values_out_index += 1;

                        value_b = source_b_local.next();
                    },
                    .eq => {
                        if (Table.usage == .secondary_index) {
                            // Secondary index optimization --- cancel out put and remove.
                            assert(tombstone(&value_a.?) != tombstone(&value_b.?));
                            continue;
                        } else if (drop_tombstones) {
                            if (tombstone(&value_a.?)) {
                                continue;
                            }
                        }

                        values_out[values_out_index] = value_a.?;
                        // std.log.info("Output stream eq: {}", .{key_from_value(&values_out[values_out_index])});
                        values_out_index += 1;

                        value_a = source_a_local.next();
                        value_b = source_b_local.next();
                    },
                }
            }

            // Copy variables back out.
            bar.source_a = source_a_local;
            bar.source_b = source_b_local;
            bar.table_builder.value_count = values_out_index;
        }
    };
}

fn snapshot_max_for_table_input(op_min: u64) u64 {
    return snapshot_min_for_table_output(op_min) - 1;
}

pub fn snapshot_min_for_table_output(op_min: u64) u64 {
    assert(op_min > 0);
    assert(op_min % @divExact(constants.lsm_batch_multiple, 2) == 0);
    return op_min + @divExact(constants.lsm_batch_multiple, 2);
}

/// Returns the first op of the compaction (Compaction.op_min) for a given op/beat.
///
/// After this compaction finishes:
/// - `op_min + half_bar_beat_count - 1` will be the input tables' snapshot_max.
/// - `op_min + half_bar_beat_count` will be the output tables' snapshot_min.
///
/// Each half-bar has a separate op_min (for deriving the output snapshot_min) instead of each full
/// bar because this allows the output tables of the first half-bar's compaction to be prefetched
/// against earlier — hopefully while they are still warm in the cache from being written.
///
///
/// These charts depict the commit/compact ops over a series of
/// commits and compactions (with lsm_batch_multiple=8).
///
/// Legend:
///
///   ┼   full bar (first half-bar start)
///   ┬   half bar (second half-bar start)
///       This is incremented at the end of each compact().
///   .   op is in mutable table (in memory)
///   ,   op is in immutable table (in memory)
///   #   op is on disk
///   ✓   checkpoint() may follow compact()
///
///   0 2 4 6 8 0 2 4 6
///   ┼───┬───┼───┬───┼
///   .       ╷       ╷     init(superblock.commit_min=0)⎤ Compaction is effectively a noop for the
///   ..      ╷       ╷     commit;compact( 1) start/end ⎥ first bar because there are no tables on
///   ...     ╷       ╷     commit;compact( 2) start/end ⎥ disk yet, and no immutable table to
///   ....    ╷       ╷     commit;compact( 3) start/end ⎥ flush.
///   .....   ╷       ╷     commit;compact( 4) start/end ⎥
///   ......  ╷       ╷     commit;compact( 5) start/end ⎥ This applies:
///   ....... ╷       ╷     commit;compact( 6) start/end ⎥ - when the LSM is starting on a freshly
///   ........╷       ╷     commit;compact( 7) start    ⎤⎥   formatted data file, and also
///   ,,,,,,,,.       ╷  ✓         compact( 7)       end⎦⎦ - when the LSM is recovering from a crash
///   ,,,,,,,,.       ╷     commit;compact( 8) start/end     (see below).
///   ,,,,,,,,..      ╷     commit;compact( 9) start/end
///   ,,,,,,,,...     ╷     commit;compact(10) start/end
///   ,,,,,,,,....    ╷     commit;compact(11) start/end
///   ,,,,,,,,.....   ╷     commit;compact(12) start/end
///   ,,,,,,,,......  ╷     commit;compact(13) start/end
///   ,,,,,,,,....... ╷     commit;compact(14) start/end
///   ,,,,,,,,........╷     commit;compact(15) start    ⎤
///   ########,,,,,,,,╷  ✓         compact(15)       end⎦
///   ########,,,,,,,,.     commit;compact(16) start/end
///   ┼───┬───┼───┬───┼
///   0 2 4 6 8 0 2 4 6
///   ┼───┬───┼───┬───┼                                    Recover with a checkpoint taken at op 15.
///   ########        ╷     init(superblock.commit_min=7)  At op 15, ops 8…15 are in memory, so they
///   ########.       ╷     commit        ( 8) start/end ⎤ were dropped by the crash.
///   ########..      ╷     commit        ( 9) start/end ⎥
///   ########...     ╷     commit        (10) start/end ⎥ But compaction is not run for ops 8…15
///   ########....    ╷     commit        (11) start/end ⎥ because it was already performed
///   ########.....   ╷     commit        (12) start/end ⎥ before the checkpoint.
///   ########......  ╷     commit        (13) start/end ⎥
///   ########....... ╷     commit        (14) start/end ⎥ We can begin to compact again at op 16,
///   ########........╷     commit        (15) start    ⎤⎥ because those compactions (if previously
///   ########,,,,,,,,╷  ✓                (15)       end⎦⎦ performed) are not included in the
///   ########,,,,,,,,.     commit;compact(16) start/end   checkpoint.
///   ┼───┬───┼───┬───┼
///   0 2 4 6 8 0 2 4 6
///
/// Notice how in the checkpoint recovery example above, we are careful not to `compact(op)` twice
/// for any op (even if we crash/recover), since that could lead to differences between replicas'
/// storage. The last bar of `commit()`s is always only in memory, so it is safe to repeat.
pub fn compaction_op_min(op: u64) u64 {
    _ = op;
    // return op - op % half_bar_beat_count;
}

// The masking and clever bits are stolen from std.RingBuffer.
// Invariants:
// Number of blocks must be even, minimum of 2.
// Internally, ValueStream is implemented as a ring buffer. There are two pointers, a read
// pointer and a write pointer.
// When starting off, it looks something like this:
//
// |  ␣  ␣  ␣  ␣  ␣  ␣  ␣  ␣  ␣  ␣  |
//   R̂Ŵ
//
// Pushing fills up and increments the write pointer:
// |  b  b  b  b  ␣  ␣  ␣  ␣  ␣  ␣  |
//   R̂            Ŵ
//
// Confirming reads increment the read pointer (just doing a read_slice() will get you the same
// contents over again):
// |  b  b  b  b  ␣  ␣  ␣  ␣  ␣  ␣  |
//       R̂        Ŵ
//
// More data can be pushed, up to the current read pointer:
// |  b  b  b  b  B  B  B  B  B  B  |
//      ŴR̂
//
// Why is this useful? When doing intra-tree-level pipelining, we can only read in values assuming
// they'll be used. We don't know how many actual values have been consumed until the merge step
// runs, but we schedule our reads _before_ doing any merges.
//
// In fact, the filling stage of our pipeline looks as follows, in order:
// 0: read()
// 1: read(), merge()
// 2: read(), write(), merge()
//
// While there is a barrier at the end, the synchronous part of the read() and write() steps (ie - _what_ to read and write) are always submitted
// before merging. For this example, pretend table_a is immutable so we only have to worry about reads from one side.
// 0: For the very first read(), this is not a problem; it starts from the beginning and reads in say 3 blocks.
// 1: For the next read(), it will read in the next 3 blocks. The merge will now begin, perhaps it uses 2 blocks - it can only use up to the reads completed in the previous step.
// 2: For the next read(), we know that we now read
// test "value stream: foo" {
//     const allocator = std.testing.allocator;
//     var blocks: [32]BlockPtr = undefined;
//     var stream = BlockRingBuffer.init(&blocks);

//     const block_to_write = try allocate_block(allocator);
//     defer allocator.free(block_to_write);
//     @memset(block_to_write, 1);

//     const ring_slice = stream.reserve();
//     ring_slice.first[0] = block_to_write;
//     ring_slice.first[1] = block_to_write;
//     stream.commit(2);

//     std.log.warn("Ring buffer with {} available slots", .{stream.inner.buffer.len - stream.inner.count});

//     // var block = stream.pop();
//     // std.log.warn("Read: {any}", .{block});
//     // block = stream.pop();
//     // std.log.warn("Read: {any}", .{block});
//     // block = stream.pop();
//     // std.log.warn("Read: {any}", .{block});

//     std.log.warn("Ring buffer with {} available slots", .{stream.inner.buffer.len - stream.inner.count});
//     // stream.write_slice(&blocks_to_write);
//     // const blocks_read = stream.read_slice();
//     // std.log.warn("Read: {any}", .{blocks_read});
//     // assert(false);
// }
