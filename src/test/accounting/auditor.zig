//! The Auditor constructs the expected state of its corresponding StateMachine from requests and
//! replies. It validates replies against its local state.
//!
//! The Auditor expects replies in ascending commit order.
const std = @import("std");
const assert = std.debug.assert;
const log = std.log.scoped(.test_auditor);

const config = @import("../../config.zig");
const tb = @import("../../tigerbeetle.zig");
const vsr = @import("../../vsr.zig");
const RingBuffer = @import("../../ring_buffer.zig").RingBuffer;

// TODO(zig) This won't be necessary in Zig 0.10.
const PriorityQueue = @import("../priority_queue.zig").PriorityQueue;

pub const CreateAccountResultSet = std.enums.EnumSet(tb.CreateAccountResult);
pub const CreateTransferResultSet = std.enums.EnumSet(tb.CreateTransferResult);

/// Batch sizes apply to both `create` and `lookup` operations.
/// (More ids would fit in the `lookup` request, but then the response wouldn't fit.)
const accounts_batch_size_max = @divFloor(config.message_size_max - @sizeOf(vsr.Header), @sizeOf(tb.Account));
const transfers_batch_size_max = @divFloor(config.message_size_max - @sizeOf(vsr.Header), @sizeOf(tb.Transfer));

/// Store expected possible results for an in-flight request.
/// This reply validation takes advantage of the Workload's additional context about the request.
const InFlight = union(enum) {
    create_accounts: [accounts_batch_size_max]CreateAccountResultSet,
    create_transfers: [transfers_batch_size_max]CreateTransferResultSet,
};

/// Each client has a queue.
const InFlightQueue = RingBuffer(InFlight, config.client_request_queue_max, .array);

const PendingExpiry = struct {
    transfer: u128,
    timestamp: u64,
    debit_account_index: usize,
    credit_account_index: usize,
};

const PendingExpiryQueue = PriorityQueue(PendingExpiry, void, struct {
    /// Order by ascending timestamp.
    fn compare(_: void, a: PendingExpiry, b: PendingExpiry) std.math.Order {
        return std.math.order(a.timestamp, b.timestamp);
    }
}.compare);

pub const AccountingAuditor = struct {
    const Self = @This();

    pub const Options = struct {
        accounts_max: usize,
        account_id_permutation: IdPermutation,
        client_count: usize,

        /// This is the maximum number of pending transfers, not counting those that have timed
        /// out.
        ///
        /// NOTE: Transfers that have posted/voided successfully (or not) that have _not_ yet
        /// reached their expiry are still included in this count — see `pending_expiries`.
        transfers_pending_max: usize,
    };

    random: std.rand.Random,
    options: Options,

    /// The timestamp of the last processed reply.
    timestamp: u64 = 0,

    /// The account configuration. Balances are in sync with the remote StateMachine for a
    /// given commit (double-double entry accounting).
    accounts: []tb.Account,

    /// Set to true when `create_accounts` returns `.ok` for an account.
    accounts_created: []bool,

    /// Map pending transfers to the (pending) amount.
    ///
    /// * Added in `on_create_transfers` for pending transfers.
    /// * Removed after a transfer is posted, voided, or timed out.
    ///
    /// All entries in `pending_amounts` have a corresponding entry in `pending_expiries`.
    pending_amounts: std.AutoHashMapUnmanaged(u128, u64),

    /// After a transfer is posted/voided, the entry in `pending_expiries` is untouched.
    /// The timeout will not impact account balances (because the `pending_amounts` entry is
    /// removed), but until timeout the transfer still counts against `transfers_pending_max`.
    pending_expiries: PendingExpiryQueue,

    /// Track the expected result of the in-flight request for each client.
    /// Each member queue corresponds to entries of the client's request queue, but omits
    /// `register` messages.
    in_flight: []InFlightQueue,

    pub fn init(allocator: std.mem.Allocator, random: std.rand.Random, options: Options) !Self {
        assert(options.accounts_max >= 2);
        assert(options.client_count > 0);

        const accounts = try allocator.alloc(tb.Account, options.accounts_max);
        errdefer allocator.free(accounts);
        std.mem.set(tb.Account, accounts, undefined);

        const accounts_created = try allocator.alloc(bool, options.accounts_max);
        errdefer allocator.free(accounts_created);
        std.mem.set(bool, accounts_created, false);

        var pending_amounts = std.AutoHashMapUnmanaged(u128, u64){};
        errdefer pending_amounts.deinit(allocator);
        try pending_amounts.ensureTotalCapacity(allocator, @intCast(u32, options.transfers_pending_max));

        var pending_expiries = PendingExpiryQueue.init(allocator, {});
        errdefer pending_expiries.deinit();
        try pending_expiries.ensureTotalCapacity(options.transfers_pending_max);

        var in_flight = try allocator.alloc(InFlightQueue, options.client_count);
        errdefer allocator.free(in_flight);
        std.mem.set(InFlightQueue, in_flight, .{});

        return Self{
            .random = random,
            .options = options,
            .accounts = accounts,
            .accounts_created = accounts_created,
            .pending_amounts = pending_amounts,
            .pending_expiries = pending_expiries,
            .in_flight = in_flight,
        };
    }

    pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
        allocator.free(self.accounts);
        allocator.free(self.accounts_created);
        self.pending_amounts.deinit(allocator);
        self.pending_expiries.deinit();
        allocator.free(self.in_flight);
    }

    pub fn expect_create_accounts(self: *Self, client_index: usize) []CreateAccountResultSet {
        self.in_flight[client_index].push_assume_capacity(.{ .create_accounts = undefined });
        return self.in_flight[client_index].tail_ptr().?.create_accounts[0..];
    }

    pub fn expect_create_transfers(self: *Self, client_index: usize) []CreateTransferResultSet {
        self.in_flight[client_index].push_assume_capacity(.{ .create_transfers = undefined });
        return self.in_flight[client_index].tail_ptr().?.create_transfers[0..];
    }

    /// Expire pending tranfers that have not been posted or voided.
    fn tick_to_timestamp(self: *Self, timestamp: u64) void {
        assert(self.timestamp < timestamp);

        while (self.pending_expiries.peek()) |expiration| {
            if (timestamp < expiration.timestamp) break;
            defer _ = self.pending_expiries.remove();

            // Ignore the transfer if it was already posted/voided.
            const pending_amount = self.pending_amounts.get(expiration.transfer) orelse continue;
            assert(self.pending_amounts.remove(expiration.transfer));
            assert(self.accounts_created[expiration.debit_account_index]);
            assert(self.accounts_created[expiration.credit_account_index]);

            const dr = &self.accounts[expiration.debit_account_index];
            const cr = &self.accounts[expiration.credit_account_index];
            dr.debits_pending -= pending_amount;
            cr.credits_pending -= pending_amount;
        }

        self.timestamp = timestamp;
    }

    pub fn on_create_accounts(
        self: *Self,
        client_index: usize,
        timestamp: u64,
        accounts: []const tb.Account,
        results: []const tb.CreateAccountsResult,
    ) void {
        assert(accounts.len >= results.len);
        assert(self.timestamp < timestamp);
        defer assert(self.timestamp == timestamp);

        const results_expect = &self.in_flight[client_index].pop().?.create_accounts;
        var results_iterator = IteratorForCreate(tb.CreateAccountsResult).init(results);
        defer assert(results_iterator.results.len == 0);

        for (accounts) |*account, i| {
            const account_timestamp = timestamp - accounts.len + i + 1;
            // TODO Should this be at the end of the loop? (If a timeout & post land on the same
            // timestamp, which wins?)
            self.tick_to_timestamp(account_timestamp);

            const result_actual = results_iterator.take(i) orelse .ok;
            if (!results_expect[i].contains(result_actual)) {
                log.err("on_create_accounts: account={} expect={} result={}", .{
                    account.*,
                    results_expect[i],
                    result_actual,
                });
                @panic("on_create_accounts: unexpected result");
            }

            const account_index = self.account_id_to_index(account.id);
            if (result_actual == .ok) {
                assert(!self.accounts_created[account_index]);
                self.accounts_created[account_index] = true;
                self.accounts[account_index] = account.*;
                self.accounts[account_index].timestamp = account_timestamp;
            }

            if (account_index >= self.accounts.len) {
                assert(result_actual != .ok);
            }
        }

        if (accounts.len == 0) {
            self.tick_to_timestamp(timestamp);
        }
    }

    pub fn on_create_transfers(
        self: *Self,
        client_index: usize,
        timestamp: u64,
        transfers: []const tb.Transfer,
        results: []const tb.CreateTransfersResult,
    ) void {
        assert(transfers.len >= results.len);
        assert(self.timestamp < timestamp);
        defer assert(self.timestamp == timestamp);

        const results_expect = &self.in_flight[client_index].pop().?.create_transfers;
        var results_iterator = IteratorForCreate(tb.CreateTransfersResult).init(results);
        defer assert(results_iterator.results.len == 0);

        for (transfers) |*transfer, i| {
            const transfer_timestamp = timestamp - transfers.len + i + 1;
            // TODO Should this be deferrred to the end of the loop? (If a timeout & post land on
            // the same timestamp, which wins?)
            self.tick_to_timestamp(transfer_timestamp);

            const result_actual = results_iterator.take(i) orelse .ok;
            if (!results_expect[i].contains(result_actual)) {
                log.err("on_create_transfers: transfer={} expect={} result={}", .{
                    transfer.*,
                    results_expect[i],
                    result_actual,
                });
                @panic("on_create_transfers: unexpected result");
            }

            if (result_actual != .ok) continue;

            const dr_index = self.account_id_to_index(transfer.debit_account_id);
            const cr_index = self.account_id_to_index(transfer.credit_account_id);
            const dr = &self.accounts[dr_index];
            const cr = &self.accounts[cr_index];
            assert(self.accounts_created[dr_index]);
            assert(self.accounts_created[cr_index]);

            if (transfer.flags.post_pending_transfer or transfer.flags.void_pending_transfer) {
                if (self.pending_amounts.get(transfer.pending_id)) |pending_amount| {
                    assert(self.pending_amounts.remove(transfer.pending_id));
                    // The transfer may still be in `pending_expiries` — removal would be O(n),
                    // so don't bother.

                    dr.debits_pending -= pending_amount;
                    cr.credits_pending -= pending_amount;
                    if (transfer.flags.post_pending_transfer) {
                        dr.debits_posted += transfer.amount;
                        cr.credits_posted += transfer.amount;
                    }
                } else {
                    // The transfer was already completed by another post/void or timeout.
                }
            } else if (transfer.flags.pending) {
                self.pending_amounts.putAssumeCapacity(transfer.id, transfer.amount);
                self.pending_expiries.add(.{
                    .transfer = transfer.id,
                    .timestamp = transfer_timestamp + transfer.timeout,
                    .debit_account_index = dr_index,
                    .credit_account_index = cr_index,
                }) catch unreachable;
                // PriorityQueue lacks an "unmanaged" API, so verify that the workload hasn't
                // created more pending transfers than permitted.
                assert(self.pending_expiries.len <= self.options.transfers_pending_max);

                dr.debits_pending += transfer.amount;
                cr.credits_pending += transfer.amount;
            } else {
                dr.debits_posted += transfer.amount;
                cr.credits_posted += transfer.amount;
            }
        }

        if (transfers.len == 0) {
            self.tick_to_timestamp(timestamp);
        }
    }

    pub fn on_lookup_accounts(
        self: *Self,
        client_index: usize,
        timestamp: u64,
        ids: []const u128,
        results: []const tb.Account,
    ) void {
        _ = client_index;
        assert(ids.len >= results.len);
        assert(self.timestamp < timestamp);
        defer assert(self.timestamp == timestamp);

        var results_iterator = IteratorForLookup(tb.Account).init(results);
        defer assert(results_iterator.results.len == 0);

        for (ids) |account_id| {
            const account_index = self.account_id_to_index(account_id);
            const account_lookup = results_iterator.take(account_id);

            if (account_index < self.accounts.len and self.accounts_created[account_index]) {
                // If this assertion fails, `lookup_accounts` didn't return an account when it
                // should have.
                assert(account_lookup != null);

                const account_expect = &self.accounts[account_index];
                if (!std.mem.eql(
                    u8,
                    std.mem.asBytes(account_lookup.?),
                    std.mem.asBytes(account_expect),
                )) {
                    log.err("on_lookup_accounts: account data mismatch " ++
                        "account_id={} expect={} lookup={}", .{
                        account_id,
                        account_expect,
                        account_lookup.?,
                    });
                    @panic("on_lookup_accounts: account data mismatch");
                }
            } else {
                // If this assertion fails, `lookup_accounts` returned an account when it shouldn't.
                assert(account_lookup == null);
            }
        }
        self.tick_to_timestamp(timestamp);
    }

    /// Most `lookup_transfers` validation is handled by Workload.
    /// (Workload has more context around transfers, so it can be much stricter.)
    pub fn on_lookup_transfers(
        self: *Self,
        client_index: usize,
        timestamp: u64,
        ids: []const u128,
        results: []const tb.Transfer,
    ) void {
        _ = client_index;
        assert(ids.len >= results.len);
        assert(self.timestamp < timestamp);
        defer assert(self.timestamp == timestamp);

        var results_iterator = IteratorForLookup(tb.Transfer).init(results);
        defer assert(results_iterator.results.len == 0);

        for (ids) |id| {
            const result = results_iterator.take(id);
            assert(result == null or result.?.id == id);
        }
        self.tick_to_timestamp(timestamp);
    }

    /// Returns a random account matching the given criteria.
    /// Returns null when no account matches the given criteria.
    pub fn pick_account(
        self: *const Self,
        match: struct {
            /// Whether the account is known to be created
            /// (we have received an `ok` for the respective `create_accounts`).
            created: ?bool = null,
            /// Don't match this account.
            exclude: ?u128 = null,
            // TODO balance limits
        },
    ) ?*const tb.Account {
        const offset = self.random.uintLessThanBiased(usize, self.accounts.len);
        var i: usize = 0;
        // Iterate `accounts`, starting from a random offset.
        while (i < self.accounts.len) : (i += 1) {
            const account_index = (offset + i) % self.accounts.len;
            if (match.created) |expect_created| {
                if (self.accounts_created[account_index]) {
                    if (!expect_created) continue;
                } else {
                    if (expect_created) continue;
                }
            }

            if (match.exclude) |exclude_id| {
                if (self.accounts[account_index].id == exclude_id) continue;
            }
            return &self.accounts[account_index];
        }
        return null;
    }

    pub fn account_id_to_index(self: *const Self, id: u128) usize {
        // -1 because id=0 is not valid, so index=0→id=1.
        return @intCast(usize, self.options.account_id_permutation.decode(id)) - 1;
    }

    pub fn account_index_to_id(self: *const Self, index: usize) u128 {
        // +1 so that index=0 is encoded as a valid id.
        return self.options.account_id_permutation.encode(index + 1);
    }
};

pub fn IteratorForCreate(comptime Result: type) type {
    assert(Result == tb.CreateAccountsResult or Result == tb.CreateTransfersResult);

    return struct {
        const Self = @This();

        results: []const Result,

        pub fn init(results: []const Result) Self {
            return .{ .results = results };
        }

        pub fn take(self: *Self, event_index: usize) ?std.meta.fieldInfo(Result, .result).field_type {
            if (self.results.len > 0 and self.results[0].index == event_index) {
                defer self.results = self.results[1..];
                return self.results[0].result;
            } else {
                return null;
            }
        }
    };
}

pub fn IteratorForLookup(comptime Result: type) type {
    assert(Result == tb.Account or Result == tb.Transfer);

    return struct {
        const Self = @This();

        results: []const Result,

        pub fn init(results: []const Result) Self {
            return .{ .results = results };
        }

        pub fn take(self: *Self, id: u128) ?*const Result {
            if (self.results.len > 0 and self.results[0].id == id) {
                defer self.results = self.results[1..];
                return &self.results[0];
            } else {
                return null;
            }
        }
    };
}

/// Permuting indexes (or other encoded data) into ids:
///
/// * tests different patterns of ids (e.g. random, ascending, descending), and
/// * allows the original index to recovered from the id, enabling less stateful testing.
///
pub const IdPermutation = union(enum) {
    /// Ascending indexes become ascending ids.
    identity: void,
    /// Ascending indexes become descending ids.
    reflect: void,
    /// Ascending indexes alternate between ascending/descending (e.g. 1,100,3,98,…).
    zigzag: void,
    /// Ascending indexes become UUIDs.
    random: [32]u8,

    pub fn encode(self: *const IdPermutation, data: u128) u128 {
        return switch (self.*) {
            .identity => data,
            .reflect => std.math.maxInt(u128) - data,
            .zigzag => {
                if (data % 2 == 0) {
                    return data;
                } else {
                    // -1 to stay odd.
                    return std.math.maxInt(u128) - data - 1;
                }
            },
            .random => |seed| {
                var id: u128 = undefined;
                std.crypto.stream.chacha.ChaCha8IETF.xor(
                    std.mem.asBytes(&id),
                    std.mem.asBytes(&data),
                    0,
                    seed,
                    [_]u8{0} ** 12,
                );
                return id;
            },
        };
    }

    pub fn decode(self: *const IdPermutation, id: u128) u128 {
        return self.encode(id);
    }
};

test "IdPermutation" {
    var prng = std.rand.DefaultPrng.init(123);
    const random = prng.random();

    for ([_]IdPermutation{
        .{ .identity = {} },
        .{ .reflect = {} },
        .{ .zigzag = {} },
        .{ .random = [_]u8{3} ** 32 },
    }) |permutation| {
        var i: u128 = 0;
        while (i < 20) : (i += 1) {
            const r = random.int(u128);
            try std.testing.expectEqual(r, permutation.decode(permutation.encode(r)));
            try std.testing.expectEqual(r, permutation.encode(permutation.decode(r)));
            try std.testing.expectEqual(i, permutation.decode(permutation.encode(i)));
            try std.testing.expectEqual(i, permutation.encode(permutation.decode(i)));
        }
    }
}
