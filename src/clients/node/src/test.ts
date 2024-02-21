import assert, { AssertionError } from 'assert'
import {
  createClient,
  Account,
  Transfer,
  TransferFlags,
  CreateAccountError,
  CreateTransferError,
  AccountFilter,
  AccountFilterFlags,
  AccountFlags,
  id,
} from '.'

const client = createClient({
  cluster_id: 0n,
  replica_addresses: [process.env.TB_ADDRESS || '3000']
})

// Test data
const Zeroed32Bytes = Buffer.alloc(32, 0)
const Zeroed48Bytes = Buffer.alloc(48, 0)
const accountA: Account = {
  id: 17n,
  debits_pending: 0n,
  debits_posted: 0n,
  credits_pending: 0n,
  credits_posted: 0n,
  user_data_128: 0n,
  user_data_64: 0n,
  user_data_32: 0,
  reserved: 0,
  ledger: 1,
  code: 718,
  flags: 0,
  timestamp: 0n // this will be set correctly by the TigerBeetle server
}
const accountB: Account = {
  id: 19n,
  debits_pending: 0n,
  debits_posted: 0n,
  credits_pending: 0n,
  credits_posted: 0n,
  user_data_128: 0n,
  user_data_64: 0n,
  user_data_32: 0,
  reserved: 0,
  ledger: 1,
  code: 719,
  flags: 0,
  timestamp: 0n // this will be set correctly by the TigerBeetle server
}

const tests: Array<{ name: string, fn: () => Promise<void> }> = []
function test(name: string, fn: () => Promise<void>) {
  tests.push({ name, fn })
}
test.skip = (name: string, fn: () => Promise<void>) => {
  console.log(name + ': SKIPPED')
}

test('id() monotonically increasing', async (): Promise<void> => {
  let idA = id();
  for (let i = 0; i < 10_000_000; i++) {
    // Ensure ID is monotonic between milliseconds if the loop executes too fast.
    if (i % 10_000 == 0) {
      await new Promise(resolve => setTimeout(resolve, 1))
    }

    const idB = id();
    assert.ok(idB > idA, 'id() returned an id that did not monotonically increase');
    idA = idB;
  }
})

test('range check `code` on Account to be u16', async (): Promise<void> => {
  const account = { ...accountA, id: 0n }

  account.code = 65535 + 1
  const codeError = await client.createAccounts([account]).catch(error => error)
  assert.strictEqual(codeError.message, 'code must be a u16.')

  const accounts = await client.lookupAccounts([account.id])
  assert.deepStrictEqual(accounts, [])
})

test('can create accounts', async (): Promise<void> => {
  const errors = await client.createAccounts([accountA])
  assert.deepStrictEqual(errors, [])
})

test('can return error on account', async (): Promise<void> => {
  const errors = await client.createAccounts([accountA, accountB])

  assert.strictEqual(errors.length, 1)
  assert.deepStrictEqual(errors[0], { index: 0, result: CreateAccountError.exists })
})

test('error if timestamp is not set to 0n on account', async (): Promise<void> => {
  const account = { ...accountA, timestamp: 2n, id: 3n }
  const errors = await client.createAccounts([account])

  assert.strictEqual(errors.length, 1)
  assert.deepStrictEqual(errors[0], { index: 0, result: CreateAccountError.timestamp_must_be_zero })
})

test('can lookup accounts', async (): Promise<void> => {
  const accounts = await client.lookupAccounts([accountA.id, accountB.id])

  assert.strictEqual(accounts.length, 2)
  const account1 = accounts[0]
  assert.strictEqual(account1.id, 17n)
  assert.strictEqual(account1.credits_posted, 0n)
  assert.strictEqual(account1.credits_pending, 0n)
  assert.strictEqual(account1.debits_posted, 0n)
  assert.strictEqual(account1.debits_pending, 0n)
  assert.strictEqual(account1.user_data_128, 0n)
  assert.strictEqual(account1.user_data_64, 0n)
  assert.strictEqual(account1.user_data_32, 0)
  assert.strictEqual(account1.code, 718)
  assert.strictEqual(account1.ledger, 1)
  assert.strictEqual(account1.flags, 0)
  assert.ok(account1.timestamp > 0n)

  const account2 = accounts[1]
  assert.strictEqual(account2.id, 19n)
  assert.strictEqual(account2.credits_posted, 0n)
  assert.strictEqual(account2.credits_pending, 0n)
  assert.strictEqual(account2.debits_posted, 0n)
  assert.strictEqual(account2.debits_pending, 0n)
  assert.strictEqual(account2.user_data_128, 0n)
  assert.strictEqual(account2.user_data_64, 0n)
  assert.strictEqual(account2.user_data_32, 0)
  assert.strictEqual(account2.code, 719)
  assert.strictEqual(account2.ledger, 1)
  assert.strictEqual(account2.flags, 0)
  assert.ok(account2.timestamp > 0n)
})

test('can create a transfer', async (): Promise<void> => {
  const transfer: Transfer = {
    id: 1n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 100n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 0,
    ledger: 1,
    code: 1,
    flags: 0,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([transfer])
  assert.deepStrictEqual(errors, [])

  const accounts = await client.lookupAccounts([accountA.id, accountB.id])
  assert.strictEqual(accounts.length, 2)
  assert.strictEqual(accounts[0].credits_posted, 100n)
  assert.strictEqual(accounts[0].credits_pending, 0n)
  assert.strictEqual(accounts[0].debits_posted, 0n)
  assert.strictEqual(accounts[0].debits_pending, 0n)

  assert.strictEqual(accounts[1].credits_posted, 0n)
  assert.strictEqual(accounts[1].credits_pending, 0n)
  assert.strictEqual(accounts[1].debits_posted, 100n)
  assert.strictEqual(accounts[1].debits_pending, 0n)
})

test('can create a two-phase transfer', async (): Promise<void> => {
  let flags = 0
  flags |= TransferFlags.pending
  const transfer: Transfer = {
    id: 2n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 50n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 2e9,
    ledger: 1,
    code: 1,
    flags,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([transfer])
  assert.deepStrictEqual(errors, [])

  const accounts = await client.lookupAccounts([accountA.id, accountB.id])
  assert.strictEqual(accounts.length, 2)
  assert.strictEqual(accounts[0].credits_posted, 100n)
  assert.strictEqual(accounts[0].credits_pending, 50n)
  assert.strictEqual(accounts[0].debits_posted, 0n)
  assert.strictEqual(accounts[0].debits_pending, 0n)

  assert.strictEqual(accounts[1].credits_posted, 0n)
  assert.strictEqual(accounts[1].credits_pending, 0n)
  assert.strictEqual(accounts[1].debits_posted, 100n)
  assert.strictEqual(accounts[1].debits_pending, 50n)

  // Lookup the transfer:
  const transfers = await client.lookupTransfers([transfer.id])
  assert.strictEqual(transfers.length, 1)
  assert.strictEqual(transfers[0].id, 2n)
  assert.strictEqual(transfers[0].debit_account_id, accountB.id)
  assert.strictEqual(transfers[0].credit_account_id, accountA.id)
  assert.strictEqual(transfers[0].amount, 50n)
  assert.strictEqual(transfers[0].user_data_128, 0n)
  assert.strictEqual(transfers[0].user_data_64, 0n)
  assert.strictEqual(transfers[0].user_data_32, 0)
  assert.strictEqual(transfers[0].timeout > 0, true)
  assert.strictEqual(transfers[0].code, 1)
  assert.strictEqual(transfers[0].flags, 2)
  assert.strictEqual(transfers[0].timestamp > 0, true)
})

test('can post a two-phase transfer', async (): Promise<void> => {
  let flags = 0
  flags |= TransferFlags.post_pending_transfer

  const commit: Transfer = {
    id: 3n,
    debit_account_id: BigInt(0),
    credit_account_id: BigInt(0),
    amount: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 2n,// must match the id of the pending transfer
    timeout: 0,
    ledger: 1,
    code: 1,
    flags: flags,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([commit])
  assert.deepStrictEqual(errors, [])

  const accounts = await client.lookupAccounts([accountA.id, accountB.id])
  assert.strictEqual(accounts.length, 2)
  assert.strictEqual(accounts[0].credits_posted, 150n)
  assert.strictEqual(accounts[0].credits_pending, 0n)
  assert.strictEqual(accounts[0].debits_posted, 0n)
  assert.strictEqual(accounts[0].debits_pending, 0n)

  assert.strictEqual(accounts[1].credits_posted, 0n)
  assert.strictEqual(accounts[1].credits_pending, 0n)
  assert.strictEqual(accounts[1].debits_posted, 150n)
  assert.strictEqual(accounts[1].debits_pending, 0n)
})

test('can reject a two-phase transfer', async (): Promise<void> => {
  // Create a two-phase transfer:
  const transfer: Transfer = {
    id: 4n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 50n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 1e9,
    ledger: 1,
    code: 1,
    flags: TransferFlags.pending,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }
  const transferErrors = await client.createTransfers([transfer])
  assert.deepStrictEqual(transferErrors, [])

  // send in the reject
  const reject: Transfer = {
    id: 5n,
    debit_account_id: BigInt(0),
    credit_account_id: BigInt(0),
    amount: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 4n, // must match the id of the pending transfer
    timeout: 0,
    ledger: 1,
    code: 1,
    flags: TransferFlags.void_pending_transfer,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([reject])
  assert.deepStrictEqual(errors, [])

  const accounts = await client.lookupAccounts([accountA.id, accountB.id])
  assert.strictEqual(accounts.length, 2)
  assert.strictEqual(accounts[0].credits_posted, 150n)
  assert.strictEqual(accounts[0].credits_pending, 0n)
  assert.strictEqual(accounts[0].debits_posted, 0n)
  assert.strictEqual(accounts[0].debits_pending, 0n)

  assert.strictEqual(accounts[1].credits_posted, 0n)
  assert.strictEqual(accounts[1].credits_pending, 0n)
  assert.strictEqual(accounts[1].debits_posted, 150n)
  assert.strictEqual(accounts[1].debits_pending, 0n)
})

test('can link transfers', async (): Promise<void> => {
  const transfer1: Transfer = {
    id: 6n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 100n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 0,
    ledger: 1,
    code: 1,
    flags: TransferFlags.linked, // points to transfer2
    timestamp: 0n, // will be set correctly by the TigerBeetle server
  }
  const transfer2: Transfer = {
    id: 6n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 100n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 0,
    ledger: 1,
    code: 1,
    // Does not have linked flag as it is the end of the chain.
    // This will also cause it to fail as this is now a duplicate with different flags
    flags: 0,
    timestamp: 0n, // will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([transfer1, transfer2])
  assert.strictEqual(errors.length, 2)
  assert.deepStrictEqual(errors[0], { index: 0, result: CreateTransferError.linked_event_failed })
  assert.deepStrictEqual(errors[1], { index: 1, result: CreateTransferError.exists_with_different_flags })

  const accounts = await client.lookupAccounts([accountA.id, accountB.id])
  assert.strictEqual(accounts.length, 2)
  assert.strictEqual(accounts[0].credits_posted, 150n)
  assert.strictEqual(accounts[0].credits_pending, 0n)
  assert.strictEqual(accounts[0].debits_posted, 0n)
  assert.strictEqual(accounts[0].debits_pending, 0n)

  assert.strictEqual(accounts[1].credits_posted, 0n)
  assert.strictEqual(accounts[1].credits_pending, 0n)
  assert.strictEqual(accounts[1].debits_posted, 150n)
  assert.strictEqual(accounts[1].debits_pending, 0n)
})

test('cannot void an expired transfer', async (): Promise<void> => {
  // Create a two-phase transfer:
  const transfer: Transfer = {
    id: 6n,
    debit_account_id: accountB.id,
    credit_account_id: accountA.id,
    amount: 50n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 0n,
    timeout: 1,
    ledger: 1,
    code: 1,
    flags: TransferFlags.pending,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }
  const transferErrors = await client.createTransfers([transfer])
  assert.deepStrictEqual(transferErrors, [])

  // Wait for the transfer to expire.
  // TODO: Use `await setTimeout(1000)` when upgrade to Node > 15.
  await new Promise(_ => setTimeout(_, 1000));

  // send in the reject
  const reject: Transfer = {
    id: 7n,
    debit_account_id: BigInt(0),
    credit_account_id: BigInt(0),
    amount: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    pending_id: 6n, // must match the id of the pending transfer
    timeout: 0,
    ledger: 1,
    code: 1,
    flags: TransferFlags.void_pending_transfer,
    timestamp: 0n, // this will be set correctly by the TigerBeetle server
  }

  const errors = await client.createTransfers([reject])
  assert.strictEqual(errors.length, 1)
  assert.deepStrictEqual(errors[0], { index: 0, result: CreateTransferError.pending_transfer_expired })
})

test('can get account transfers', async (): Promise<void> => {
  const accountC: Account = {
    id: 21n,
    debits_pending: 0n,
    debits_posted: 0n,
    credits_pending: 0n,
    credits_posted: 0n,
    user_data_128: 0n,
    user_data_64: 0n,
    user_data_32: 0,
    reserved: 0,
    ledger: 1,
    code: 718,
    flags: AccountFlags.history,
    timestamp: 0n
  }
  const account_errors = await client.createAccounts([accountC])
  assert.deepStrictEqual(account_errors, [])

  var transfers_created : Transfer[] = [];
  // Create transfers where the new account is either the debit or credit account:
  for (var i=0; i<10;i++) {
    transfers_created.push({
      id: BigInt(i + 10000),
      debit_account_id: i % 2 == 0 ? accountC.id : accountA.id,
      credit_account_id: i % 2 == 0 ? accountB.id : accountC.id,
      amount: 100n,
      user_data_128: 0n,
      user_data_64: 0n,
      user_data_32: 0,
      pending_id: 0n,
      timeout: 0,
      ledger: 1,
      code: 1,
      flags: 0,
      timestamp: 0n,
    });
  }

  const transfers_created_result = await client.createTransfers(transfers_created)
  assert.deepStrictEqual(transfers_created_result, [])

  // Query all transfers for accountC:
  var filter: AccountFilter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  var transfers = await client.getAccountTransfers(filter)
  var history = await client.getAccountHistory(filter)
  assert.strictEqual(transfers.length, transfers_created.length)
  assert.strictEqual(history.length, transfers.length)

  var timestamp = 0n;
  var i = 0;
  for (var transfer of transfers) {
    assert.ok(timestamp < transfer.timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query only the debit transfers for accountC, descending:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.debits |  AccountFilterFlags.reversed,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  timestamp = 1n << 64n;
  i = 0;
  for (var transfer of transfers) {
    assert.ok(transfer.timestamp < timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query only the credit transfers for accountC, descending:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.credits |  AccountFilterFlags.reversed,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  timestamp = 1n << 64n;
  i = 0;
  for (var transfer of transfers) {
    assert.ok(transfer.timestamp < timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query the first 5 transfers for accountC:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  timestamp = 0n;
  i = 0;
  for (var transfer of transfers) {
    assert.ok(timestamp < transfer.timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query the next 5 transfers for accountC, with pagination:
  filter = {
    account_id: accountC.id,
    timestamp_min: timestamp + 1n,
    timestamp_max: 0n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  i = 0;
  for (var transfer of transfers) {
    assert.ok(timestamp < transfer.timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query again, no more transfers should be found:
  filter = {
    account_id: accountC.id,
    timestamp_min: timestamp + 1n,
    timestamp_max: 0n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.deepStrictEqual(transfers, [])
  assert.strictEqual(history.length, transfers.length)

  // Query the first 5 transfers for accountC ORDER BY DESC:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits | AccountFilterFlags.reversed,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  timestamp = 1n << 64n;
  i = 0;
  for (var transfer of transfers) {
    assert.ok(timestamp > transfer.timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query the next 5 transfers for accountC, with pagination:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: timestamp - 1n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits | AccountFilterFlags.reversed,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.strictEqual(transfers.length, transfers_created.length / 2)
  assert.strictEqual(history.length, transfers.length)

  i = 0;
  for (var transfer of transfers) {
    assert.ok(timestamp > transfer.timestamp);
    timestamp = transfer.timestamp;

    assert.ok(history[i].timestamp == transfer.timestamp);
    i++;
  }

  // Query again, no more transfers should be found:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: timestamp - 1n,
    limit: transfers_created.length / 2,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits | AccountFilterFlags.reversed,
  }
  transfers = await client.getAccountTransfers(filter)
  history = await client.getAccountHistory(filter)

  assert.deepStrictEqual(transfers, [])
  assert.strictEqual(history.length, transfers.length)

  // Invalid account:
  filter = {
    account_id: 0n,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Invalid timestamp min:
  filter = {
    account_id: accountC.id,
    timestamp_min: (1n << 64n) - 1n, // ulong max value
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Invalid timestamp max:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: (1n << 64n) - 1n, // ulong max value
    limit: 8190,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Invalid timestamp range:
  filter = {
    account_id: accountC.id,
    timestamp_min: (1n << 64n) - 2n, // ulong max - 1
    timestamp_max: 1n,
    limit: 8190,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Zero limit:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 0,
    flags: AccountFilterFlags.credits | AccountFilterFlags.debits,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Empty flags:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: AccountFilterFlags.none,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

  // Invalid flags:
  filter = {
    account_id: accountC.id,
    timestamp_min: 0n,
    timestamp_max: 0n,
    limit: 8190,
    flags: 0xFFFF,
  }
  assert.deepStrictEqual((await client.getAccountTransfers(filter)), [])
  assert.deepStrictEqual((await client.getAccountHistory(filter)), [])

})

async function main () {
  const start = new Date().getTime()
  try {
    for (let i = 0; i < tests.length; i++) {
        await tests[i].fn().then(() => {
        console.log(tests[i].name + ": PASSED")
      }).catch(error => {
        console.log(tests[i].name + ": FAILED")
        throw error
      })
    }
    const end = new Date().getTime()
    console.log('Time taken (s):', (end - start)/1000)
  } finally {
    await client.destroy()
  }
}

main().catch((error: AssertionError) => {
  console.log('operator:', error.operator)
  console.log('stack:', error.stack)
  process.exit(-1);
})
