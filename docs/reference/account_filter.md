---
sidebar_position: 4
---

# Account Filter

An `AccountFilter` is a record containing the filter parameters for querying
the [account transfers](operations/get_account_transfers.md)
and the [account historical balances](operations/get_account_history.md).

## Fields

### `account_id`

The unique [identifier](accounts.md#id) of the account for which the results will be retrieved.

Constraints:

* Type is 128-bit unsigned integer (16 bytes)
* Must not be zero or `2^128 - 1`

### `timestamp_min`

The minimum [`Transfer.timestamp`](transfers.md#timestamp) from which results will be returned, inclusive range.
Optional; set to zero to disable the lower-bound filter.

Constraints:

* Type is 64-bit unsigned integer (8 bytes)
* Must not be `2^64 - 1`

### `timestamp_max`

The maximum [`Transfer.timestamp`](transfers.md#timestamp) from which results will be returned, inclusive range.
Optional; set to zero to disable the upper-bound filter.

Constraints:

* Type is 64-bit unsigned integer (8 bytes)
* Must not be `2^64 - 1`

### `limit`

The maximum number of results that can be returned by this query.

Limited by the [maximum message size](../design/client-requests.md#batching-events).

Constraints:

* Type is 32-bit unsigned integer (4 bytes)
* Must not be zero

### `flags`

A bitfield that specifies querying behavior.

Constraints:

* Type is 32-bit unsigned integer (4 bytes)

#### `flags.debits`

Whether or not to include results where the field [`debit_account_id`](transfers.md#debit_account_id)
matches the parameter [`account_id`](#account_id).

#### `flags.credits`

Whether or not to include results where the field [`credit_account_id`](transfers.md#credit_account_id)
matches the parameter [`account_id`](#account_id).

#### `flags.reversed`

Whether the results are sorted by timestamp in chronological or reverse-chronological order.

### `reserved`

This space may be used for additional data in the future.

Constraints:

* Type is 24 bytes
* Must be zero