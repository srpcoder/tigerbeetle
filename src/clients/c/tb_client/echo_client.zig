const std = @import("std");
const stdx = @import("../../../stdx.zig");
const assert = std.debug.assert;
const mem = std.mem;

const constants = @import("../../../constants.zig");
const vsr = @import("../../../vsr.zig");
const Header = vsr.Header;

const IOPS = @import("../../../iops.zig").IOPS;
const RingBuffer = @import("../../../ring_buffer.zig").RingBuffer;
const MessagePool = @import("../../../message_pool.zig").MessagePool;
const Message = @import("../../../message_pool.zig").MessagePool.Message;

pub fn EchoClient(comptime StateMachine_: type, comptime MessageBus: type) type {
    return struct {
        const Self = @This();

        // Exposing the same types the real client does:
        const Client = @import("../../../vsr/client.zig").Client(StateMachine_, MessageBus);
        pub const StateMachine = Client.StateMachine;
        pub const Request = Client.Request;

        id: u128,
        cluster: u128,
        messages_available: u32 = constants.client_request_queue_max,
        inflight: ?Request = null,
        message_pool: *MessagePool,

        pub fn init(
            allocator: mem.Allocator,
            id: u128,
            cluster: u128,
            replica_count: u8,
            message_pool: *MessagePool,
            message_bus_options: MessageBus.Options,
        ) !Self {
            _ = allocator;
            _ = replica_count;
            _ = message_bus_options;

            return Self{
                .id = id,
                .cluster = cluster,
                .message_pool = message_pool,
            };
        }

        pub fn deinit(self: *Self, allocator: std.mem.Allocator) void {
            _ = allocator;
            // Drains all pending requests before deiniting.
            self.reply();
        }

        pub fn tick(self: *Self) void {
            self.reply();
        }

        pub fn request(
            self: *Self,
            callback: Request.Callback,
            user_data: u128,
            operation: StateMachine.Operation,
            event_data: []const u8,
        ) void {
            const event_size: usize = switch (operation) {
                inline else => |comptime_operation| @sizeOf(StateMachine.Event(comptime_operation)),
            };
            assert(event_data.len % event_size == 0);
            assert(event_data.len <= constants.message_body_size_max);

            const message = self.get_message().build(.request);
            errdefer self.release(message);

            message.header.* = .{
                .client = self.id,
                .request = 0,
                .cluster = self.cluster,
                .command = .request,
                .operation = vsr.Operation.from(Self.StateMachine, operation),
                .size = @intCast(@sizeOf(Header) + event_data.len),
                .release = 1, // TODO Use the real release number.
            };

            stdx.copy_disjoint(.exact, u8, message.body(), event_data);

            assert(self.inflight == null);
            self.inflight = .{
                .message = message,
                .user_data = user_data,
                .callback = callback,
            };
        }

        pub fn inflight_message(self: *const Self) ?*Message.Request {
            if (self.inflight) |inflight| return inflight.message;
            return null;
        }

        pub fn get_message(self: *Self) *Message {
            assert(self.messages_available > 0);
            self.messages_available -= 1;
            return self.message_pool.get_message(null);
        }

        pub fn release(self: *Self, message: *Message) void {
            assert(self.messages_available < constants.client_request_queue_max);
            self.messages_available += 1;
            self.message_pool.unref(message);
        }

        fn reply(self: *Self) void {
            while (self.inflight) |inflight| {
                self.inflight = null;

                const reply_message = self.message_pool.get_message(.request);
                defer self.message_pool.unref(reply_message.base());

                const operation = inflight.message.header.operation.cast(Self.StateMachine);
                stdx.copy_disjoint(
                    .exact,
                    u8,
                    reply_message.buffer,
                    inflight.message.buffer,
                );

                // Similarly to the real client, release the inflight message before invoking the
                // callback. This necessitates a `copy_disjoint` above.
                self.release(inflight.message.base());

                inflight.callback(
                    inflight.user_data,
                    operation,
                    reply_message.body(),
                );
            }
        }
    };
}
