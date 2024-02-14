//! Continuous Fuzzing Orchestrator.
//!
//! We have a number of machines which run
//!
//!     git clone https://github.com/tigerbeetle/tigerbeetle && cd tigerbeetle
//!     while True:
//!         git fetch origin && git reset --hard origin/main
//!         ./zig/zig build scripts -- cfo
//!
//! By modifying this script, we can make those machines do interesting things.
//!
//! The primary use-case is fuzzing: `cfo` runs a random fuzzer, and, if it finds a failure, it is
//! recorded in devhubdb.

const std = @import("std");
const builtin = @import("builtin");
const log = std.log;
const assert = std.debug.assert;

const stdx = @import("../stdx.zig");
const flags = @import("../flags.zig");
const fatal = flags.fatal;
const Shell = @import("../shell.zig");

pub const CliArgs = struct {};

pub fn main(shell: *Shell, gpa: std.mem.Allocator, cli_args: CliArgs) !void {
    _ = cli_args;
    _ = gpa;
    assert(try shell.exec_status_ok("git --version", .{}));
    assert(try shell.exec_status_ok("gh --version", .{}));

    const revision_sha = shell.exec_stdout("git rev-parse HEAD", .{});
    const revision_ord = shell.exec_stdout("git rev-list --count --first-parent HEAD", .{});

    const random = std.crypto.random;

    try shell.project_root.deleteTree("working");
    try shell.project_root.makePath("working", .{});
    shell.pushd("working");
    defer shell.popd();

    var devhubdb = try DevHubDB.init(shell.cwd, gpa);
    defer devhubdb.deinit();

    try shell.exec("git clone https://github.com/tigerbeetle/tigerbeetle", .{});
    shell.exec("git reset --hard {commit}", .{ .commit = revision_sha });

    assert(try shell.dir_exists("tigerbeetle"));
    assert(try shell.dir_exists("devhubdb"));

    const timer = try std.time.Timer.start();

    const FuzzerRun = struct {
        seed: u64,
        started: usize,
        fuzzer: Fuzzer,
        child: std.ChildProcess,
    };

    const fuzzer_concurrency = 10;
    var fuzzer_process: [fuzzer_concurrency]?FuzzerRun = .{null} ** fuzzer_concurrency;
    for (0..10 * 60) |iteration| {
        if (timer.read() > 10 * std.time.ns_per_min) break;

        const fuzzer = random.enumValue(Fuzzer);
        const seed = random.int(u64);

        for (&runs) |*run| {
            if (run.* == null) {
                run.* = .{
                    .seed = seed,
                    .started = iteration,
                    .fuzzer = .ewah,
                    .child = try shell.spawn("zig/zig build fuzz -- --seed={d} ewah", .{seed}),
                };
            }
        }

        std.time.sleep(1 * std.time.ns_per_s);
        for (&runs) |*run_maybe| {
            const run = run_maybe.?;
            run.child.
            if (run.* == null) {
                run.* = .{
                    .seed = seed,
                    .started = iteration,
                    .fuzzer = .ewah,
                    .child = try shell.spawn("zig/zig build fuzz -- --seed={d} ewah", .{seed}),
                };
            }
        }
    }

    _ = devhubdb;
    _ = revision_ord;
}

fn append_revision(
    shell: *Shell,
    gpa: std.mem.Allocator,
    path: []const u8,
    failures: []Failure,
) !void {
    errdefer log.err("failed to update {s}", .{path});

    var arena_allocator = std.heap.ArenaAllocator.init(gpa);
    defer arena_allocator.deinit();

    const arena = arena_allocator.allocator();

    const max_bytes = 1024 * 1024;
    const text = try shell.cwd.readFileAlloc(arena, path, max_bytes);

    var failures = try std.json.parseFromSliceLeaky([]Failure, arena, text, .{});

    for (seeds.revisions) |revision_existing| {
        if (revision_existing.sha == revision.sha) {
            break;
        }
    } else {
        seeds.revisions = std.mem.concat(arena, seeds.revisions, &.{revision});
        std.mem.sort(BadSeeds.Revision, seeds.revisions, void, BadSeeds.less_than);
    }
}

fn merge_failures(
    arena: std.mem.Allocator,
    current: []const Failure,
    new: []const Failure,
) !union(enum) { updated: []const Failure, up_to_date } {
    _ = new;
    _ = current;
    _ = arena;
}

const Fuzzer = enum { ewah };

const Failure = struct {
    ord: u32,
    sha: u160,
    fuzzer: Fuzzer,
    seed: u64,
    command: []const u8,
};
