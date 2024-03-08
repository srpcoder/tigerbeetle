package com.tigerbeetle;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.lang.ProcessBuilder.Redirect;
import java.math.BigInteger;
import java.util.UUID;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Semaphore;
import java.util.stream.Collectors;

import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;
import static org.junit.Assert.assertArrayEquals;
import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotEquals;
import static org.junit.Assert.assertTrue;

/**
 * Integration tests using a TigerBeetle instance.
 */
public class IntegrationTest {
    private static final byte[] clusterId = new byte[16];

    private static Server server;
    private static Client client;

    private static AccountBatch generateAccounts(final byte[] id1, final byte[] id2) {
        final var accounts = new AccountBatch(2);

        accounts.add();
        accounts.setId(id1);
        accounts.setUserData128(100, 0);
        accounts.setUserData64(101);
        accounts.setUserData32(102);
        accounts.setLedger(720);
        accounts.setCode(1);
        accounts.setFlags(AccountFlags.NONE);

        accounts.add();
        accounts.setId(id2);
        accounts.setUserData128(200, 0);
        accounts.setUserData64(201);
        accounts.setUserData32(202);
        accounts.setLedger(720);
        accounts.setCode(2);
        accounts.setFlags(AccountFlags.NONE);

        accounts.beforeFirst();
        return accounts;
    }

    @BeforeClass
    public static void initialize() throws Exception {
        server = new Server();
        client = new Client(clusterId, new String[] {server.address});
    }

    @AfterClass
    public static void cleanup() throws Exception {
        client.close();
        server.close();
    }

    @Test(expected = NullPointerException.class)
    public void testConstructorNullReplicaAddresses() throws Throwable {
        try (final var client = new Client(clusterId, null)) {
            assert false;
        }
    }

    @Test(expected = NullPointerException.class)
    public void testConstructorNullElementReplicaAddresses() throws Throwable {
        final var replicaAddresses = new String[] {"3001", null};
        try (final var client = new Client(clusterId, replicaAddresses)) {
            assert false;
        }
    }

    @Test(expected = IllegalArgumentException.class)
    public void testConstructorEmptyReplicaAddresses() throws Throwable {
        final var replicaAddresses = new String[0];
        try (final var client = new Client(clusterId, replicaAddresses)) {
            assert false;
        }
    }

    @Test
    public void testConstructorReplicaAddressesLimitExceeded() throws Throwable {
        final var replicaAddresses = new String[100];
        for (int i = 0; i < replicaAddresses.length; i++) {
            replicaAddresses[i] = "3000";
        }

        try (final var client = new Client(clusterId, replicaAddresses)) {
            assert false;
        } catch (InitializationException initializationException) {
            assertEquals(InitializationStatus.AddressLimitExceeded.value,
                    initializationException.getStatus());
        }
    }

    @Test
    public void testConstructorEmptyStringReplicaAddresses() throws Throwable {
        final var replicaAddresses = new String[] {"", "", ""};
        try (final var client = new Client(clusterId, replicaAddresses)) {
            assert false;
        } catch (InitializationException initializationException) {
            assertEquals(InitializationStatus.AddressInvalid.value,
                    initializationException.getStatus());
        }
    }

    @Test
    public void testConstructorInvalidReplicaAddresses() throws Throwable {
        final var replicaAddresses = new String[] {"127.0.0.1:99999"};
        try (final var client = new Client(clusterId, replicaAddresses)) {
            assert false;
        } catch (InitializationException initializationException) {
            assertEquals(InitializationStatus.AddressInvalid.value,
                    initializationException.getStatus());
        }
    }

    public void testConstructorCluster() throws Throwable {
        final var clusterId = UInt128.id();
        final var replicaAddresses = new String[] {"3001"};
        try (final var client = new Client(clusterId, replicaAddresses)) {
            assertArrayEquals(clusterId, client.getClusterID());
        }
    }

    @Test(expected = IllegalArgumentException.class)
    public void testConstructorInvalidCluster() throws Throwable {
        final var clusterIdInvalid = new byte[] {0, 0, 0};
        final var replicaAddresses = new String[] {"3001"};
        try (final var client = new Client(clusterIdInvalid, replicaAddresses)) {
            assert false;
        }
    }

    @Test(expected = IllegalArgumentException.class)
    public void testConstructorNegativeConcurrencyMax() throws Throwable {
        final var replicaAddresses = new String[] {"3001"};
        final var concurrencyMax = -1;
        try (final var client = new Client(clusterId, replicaAddresses, concurrencyMax)) {
            assert false;
        }
    }

    @Test
    public void testCreateAccounts() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var accounts = generateAccounts(account1Id, account2Id);

        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertEquals(2, lookupAccounts.getLength());

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);
    }

    @Test
    public void testCreateInvalidAccount() throws Throwable {
        final var zeroedAccounts = new AccountBatch(1);
        zeroedAccounts.add();

        final var createAccountErrors = client.createAccounts(zeroedAccounts);
        assertTrue(createAccountErrors.getLength() == 1);
        assertTrue(createAccountErrors.next());
        assertEquals(CreateAccountResult.IdMustNotBeZero, createAccountErrors.getResult());
    }

    @Test
    public void testCreateAccountsAsync() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var accounts = generateAccounts(account1Id, account2Id);

        CompletableFuture<CreateAccountResultBatch> accountsFuture =
                client.createAccountsAsync(accounts);

        final var createAccountErrors = accountsFuture.get();
        assertTrue(createAccountErrors.getLength() == 0);

        CompletableFuture<AccountBatch> lookupFuture =
                client.lookupAccountsAsync(new IdBatch(account1Id, account2Id));

        final var lookupAccounts = lookupFuture.get();
        assertEquals(2, lookupAccounts.getLength());

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);
    }

    @Test
    public void testCreateTransfers() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        // Creating the accounts.
        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a transfer.
        final var transfers = new TransferBatch(2);

        transfers.add();
        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setFlags(TransferFlags.NONE);
        transfers.setAmount(100);

        final var createTransferErrors = client.createTransfers(transfers);
        assertTrue(createTransferErrors.getLength() == 0);

        // Looking up the accounts.
        final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the first account for the credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the second account for the debit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPosted());

        // Looking up and asserting the transfer.
        final var lookupTransfers = client.lookupTransfers(new IdBatch(transfer1Id, transfer2Id));
        assertEquals(1, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());
    }

    @Test
    public void testCreateTransfersAsync() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        // Creating the accounts.
        CompletableFuture<CreateAccountResultBatch> future = client.createAccountsAsync(accounts);

        final var createAccountErrors = future.get();
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a transfer.
        final var transfers = new TransferBatch(2);

        transfers.add();
        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(100);

        CompletableFuture<CreateTransferResultBatch> transfersFuture =
                client.createTransfersAsync(transfers);
        final var createTransferErrors = transfersFuture.get();
        assertTrue(createTransferErrors.getLength() == 0);

        // Looking up the accounts.
        CompletableFuture<AccountBatch> lookupAccountsFuture =
                client.lookupAccountsAsync(new IdBatch(account1Id, account2Id));
        final var lookupAccounts = lookupAccountsFuture.get();
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the first account for the credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the second account for the debit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPosted());

        // Looking up and asserting the transfer.
        CompletableFuture<TransferBatch> lookupTransfersFuture =
                client.lookupTransfersAsync(new IdBatch(transfer1Id, transfer2Id));
        final var lookupTransfers = lookupTransfersFuture.get();
        assertEquals(1, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(BigInteger.ZERO, lookupTransfers.getTimestamp());
    }

    @Test
    public void testCreateInvalidTransfer() throws Throwable {
        final var zeroedTransfers = new TransferBatch(1);
        zeroedTransfers.add();

        final var createTransfersErrors = client.createTransfers(zeroedTransfers);
        assertTrue(createTransfersErrors.getLength() == 1);
        assertTrue(createTransfersErrors.next());
        assertEquals(CreateTransferResult.IdMustNotBeZero, createTransfersErrors.getResult());
    }

    @Test
    public void testCreatePendingTransfers() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        // Creating the accounts.
        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a pending transfer.
        final var transfers = new TransferBatch(1);
        transfers.add();

        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(100);
        transfers.setFlags(TransferFlags.PENDING);
        transfers.setTimeout(Integer.MAX_VALUE);

        final var createTransfersErrors = client.createTransfers(transfers);
        assertTrue(createTransfersErrors.getLength() == 0);

        // Looking up the accounts.
        var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the first account for the pending credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the second account for the pending debit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());

        // Looking up and asserting the pending transfer.
        var lookupTransfers = client.lookupTransfers(new IdBatch(transfer1Id));
        assertEquals(1, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());

        // Creating a post_pending transfer.
        final var confirmTransfers = new TransferBatch(1);
        confirmTransfers.add();
        confirmTransfers.setId(transfer2Id);
        confirmTransfers.setCreditAccountId(account1Id);
        confirmTransfers.setDebitAccountId(account2Id);
        confirmTransfers.setLedger(720);
        confirmTransfers.setCode((short) 1);
        confirmTransfers.setAmount(100);
        confirmTransfers.setFlags(TransferFlags.POST_PENDING_TRANSFER);
        confirmTransfers.setPendingId(transfer1Id);

        final var createPostTransfersErrors = client.createTransfers(confirmTransfers);
        assertEquals(0, createPostTransfersErrors.getLength());

        // Looking up the accounts again for the updated balance.
        lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the pending credit was posted for the first account.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the pending debit was posted for the second account.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPosted());

        // Looking up and asserting the post_pending transfer.
        final var lookupVoidTransfers = client.lookupTransfers(new IdBatch(transfer2Id));
        assertEquals(1, lookupVoidTransfers.getLength());

        confirmTransfers.beforeFirst();

        assertTrue(confirmTransfers.next());
        assertTrue(lookupVoidTransfers.next());
        assertTransfers(confirmTransfers, lookupVoidTransfers);
        assertNotEquals(0L, lookupVoidTransfers.getTimestamp());
    }

    @Test
    public void testCreatePendingTransfersAndVoid() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        // Creating the accounts.
        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a pending transfer.
        final var transfers = new TransferBatch(1);
        transfers.add();

        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(100);
        transfers.setFlags(TransferFlags.PENDING);
        transfers.setTimeout(Integer.MAX_VALUE);

        final var createTransfersErrors = client.createTransfers(transfers);
        assertTrue(createTransfersErrors.getLength() == 0);

        // Looking up the accounts.
        var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the first account for the pending credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the second account for the pending credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());

        // Looking up and asserting the pending transfer.
        var lookupTransfers = client.lookupTransfers(new IdBatch(transfer1Id));
        assertEquals(1, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());

        // Creating a void_pending transfer.
        final var voidTransfers = new TransferBatch(2);
        voidTransfers.add();
        voidTransfers.setId(transfer2Id);
        voidTransfers.setCreditAccountId(account1Id);
        voidTransfers.setDebitAccountId(account2Id);
        voidTransfers.setLedger(720);
        voidTransfers.setCode((short) 1);
        voidTransfers.setAmount(100);
        voidTransfers.setFlags(TransferFlags.VOID_PENDING_TRANSFER);
        voidTransfers.setPendingId(transfer1Id);

        final var createVoidTransfersErrors = client.createTransfers(voidTransfers);
        assertEquals(0, createVoidTransfersErrors.getLength());

        // Looking up the accounts again for the updated balance.
        lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the pending credit was voided for the first account.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the pending debit was voided for the second account.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Looking up and asserting the void_pending transfer.
        final var lookupVoidTransfers = client.lookupTransfers(new IdBatch(transfer2Id));
        assertEquals(1, lookupVoidTransfers.getLength());

        voidTransfers.beforeFirst();

        assertTrue(voidTransfers.next());
        assertTrue(lookupVoidTransfers.next());
        assertTransfers(voidTransfers, lookupVoidTransfers);
        assertNotEquals(0L, lookupVoidTransfers.getTimestamp());
    }

    @Test
    public void testCreatePendingTransfersAndVoidExpired() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        // Creating the accounts.
        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a pending transfer.
        final var transfers = new TransferBatch(1);
        transfers.add();

        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(100);
        transfers.setFlags(TransferFlags.PENDING);
        transfers.setTimeout(1);

        final var createTransfersErrors = client.createTransfers(transfers);
        assertTrue(createTransfersErrors.getLength() == 0);

        // Looking up the accounts.
        final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertTrue(lookupAccounts.getLength() == 2);

        accounts.beforeFirst();

        // Asserting the first account for the pending credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

        // Asserting the second account for the pending credit.
        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());

        // Looking up and asserting the pending transfer.
        final var lookupTransfers = client.lookupTransfers(new IdBatch(transfer1Id));
        assertEquals(1, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());

        // We need to wait 1s for the server to expire the transfer,
        // however `Thread.sleep` does not have nanoseconds resolution and may finish earlier than
        // the server timeout, so adding an extra delay to avoid flaky tests.
        final var TIMEOUT_MS = 1000;
        final var currentMilis = System.currentTimeMillis();
        Thread.sleep(TIMEOUT_MS + 1);
        assertTrue(System.currentTimeMillis() - currentMilis > TIMEOUT_MS);

        // Creating a void_pending transfer.
        final var voidTransfers = new TransferBatch(2);
        voidTransfers.add();
        voidTransfers.setId(transfer2Id);
        voidTransfers.setCreditAccountId(account1Id);
        voidTransfers.setDebitAccountId(account2Id);
        voidTransfers.setLedger(720);
        voidTransfers.setCode((short) 1);
        voidTransfers.setAmount(100);
        voidTransfers.setFlags(TransferFlags.VOID_PENDING_TRANSFER);
        voidTransfers.setPendingId(transfer1Id);

        final var createVoidTransfersErrors = client.createTransfers(voidTransfers);
        assertEquals(1, createVoidTransfersErrors.getLength());
        assertTrue(createVoidTransfersErrors.next());
        assertEquals(CreateTransferResult.PendingTransferExpired,
                createVoidTransfersErrors.getResult());

        // TODO(batiati)
        // Check the accounts again for the updated balance when we implement transfers
        // expiration.
    }

    @Test
    public void testCreateLinkedTransfers() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var transfer1Id = UInt128.id();
        final var transfer2Id = UInt128.id();

        final var accounts = generateAccounts(account1Id, account2Id);

        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        final var transfers = new TransferBatch(2);
        transfers.add();
        transfers.setId(transfer1Id);
        transfers.setCreditAccountId(account1Id);
        transfers.setDebitAccountId(account2Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(100);
        transfers.setFlags(TransferFlags.LINKED);

        transfers.add();
        transfers.setId(transfer2Id);
        transfers.setCreditAccountId(account2Id);
        transfers.setDebitAccountId(account1Id);
        transfers.setLedger(720);
        transfers.setCode((short) 1);
        transfers.setAmount(49);
        transfers.setFlags(TransferFlags.NONE);

        final var createTransfersErrors = client.createTransfers(transfers);
        assertTrue(createTransfersErrors.getLength() == 0);

        final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
        assertEquals(2, lookupAccounts.getLength());

        accounts.beforeFirst();

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(100), lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.valueOf(49), lookupAccounts.getDebitsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());

        assertTrue(accounts.next());
        assertTrue(lookupAccounts.next());
        assertAccounts(accounts, lookupAccounts);

        assertEquals(BigInteger.valueOf(49), lookupAccounts.getCreditsPosted());
        assertEquals(BigInteger.valueOf(100), lookupAccounts.getDebitsPosted());
        assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPending());
        assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPending());

        final var lookupTransfers = client.lookupTransfers(new IdBatch(transfer1Id, transfer2Id));
        assertEquals(2, lookupTransfers.getLength());

        transfers.beforeFirst();

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());
        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());

        assertTrue(transfers.next());
        assertTrue(lookupTransfers.next());

        assertTransfers(transfers, lookupTransfers);
        assertNotEquals(0L, lookupTransfers.getTimestamp());
    }

    @Test
    public void testCreateAccountTooMuchData() throws Throwable {
        final int TOO_MUCH_DATA = 10_000;
        final var accounts = new AccountBatch(TOO_MUCH_DATA);
        for (int i = 0; i < TOO_MUCH_DATA; i++) {
            accounts.add();
            accounts.setId(UInt128.id());
            accounts.setCode(1);
            accounts.setLedger(1);
        }

        try {
            client.createAccounts(accounts);
            assert false;
        } catch (RequestException requestException) {
            assertEquals(PacketStatus.TooMuchData.value, requestException.getStatus());
        }
    }

    @Test
    public void testCreateAccountTooMuchDataAsync() throws Throwable {
        final int TOO_MUCH_DATA = 10_000;
        final var accounts = new AccountBatch(TOO_MUCH_DATA);
        for (int i = 0; i < TOO_MUCH_DATA; i++) {
            accounts.add();
            accounts.setId(UInt128.id());
            accounts.setCode(1);
            accounts.setLedger(1);
        }

        try {
            CompletableFuture<CreateAccountResultBatch> future =
                    client.createAccountsAsync(accounts);
            assert future != null;

            future.get();
            assert false;
        } catch (ExecutionException executionException) {
            assertTrue(executionException.getCause() instanceof RequestException);

            final var requestException = (RequestException) executionException.getCause();
            assertEquals(PacketStatus.TooMuchData.value, requestException.getStatus());
        }
    }

    @Test
    public void testCreateTransferTooMuchData() throws Throwable {
        final int TOO_MUCH_DATA = 10_000;
        final var transfers = new TransferBatch(TOO_MUCH_DATA);

        for (int i = 0; i < TOO_MUCH_DATA; i++) {
            transfers.add();
            transfers.setId(UInt128.id());
            transfers.setDebitAccountId(UInt128.id());
            transfers.setDebitAccountId(UInt128.id());
            transfers.setCode(1);
            transfers.setLedger(1);
        }

        try {
            client.createTransfers(transfers);
            assert false;
        } catch (RequestException requestException) {
            assertEquals(PacketStatus.TooMuchData.value, requestException.getStatus());
        }
    }

    @Test
    public void testCreateTransferTooMuchDataAsync() throws Throwable {
        final int TOO_MUCH_DATA = 10_000;
        final var transfers = new TransferBatch(TOO_MUCH_DATA);

        for (int i = 0; i < TOO_MUCH_DATA; i++) {
            transfers.add();
            transfers.setId(UInt128.id());
            transfers.setDebitAccountId(UInt128.id());
            transfers.setDebitAccountId(UInt128.id());
            transfers.setCode(1);
            transfers.setLedger(1);
        }

        try {
            CompletableFuture<CreateTransferResultBatch> future =
                    client.createTransfersAsync(transfers);
            assert future != null;

            future.get();
            assert false;

        } catch (ExecutionException executionException) {
            assertTrue(executionException.getCause() instanceof RequestException);

            final var requestException = (RequestException) executionException.getCause();
            assertEquals(PacketStatus.TooMuchData.value, requestException.getStatus());
        }
    }

    /**
     * This test asserts that the client can handle parallel threads up to concurrencyMax.
     */
    @Test
    public void testConcurrentTasks() throws Throwable {
        // Defining the CONCURRENCY_MAX equals to TASKS_COUNT
        // The goal here is to allow to all requests being submitted at once.
        final int CONCURRENCY_MAX = 100;
        final int TASKS_COUNT = CONCURRENCY_MAX;
        final var barrier = new CountDownLatch(TASKS_COUNT);

        try (final var client =
                new Client(clusterId, new String[] {server.getAddress()}, CONCURRENCY_MAX)) {
            final var account1Id = UInt128.id();
            final var account2Id = UInt128.id();
            final var accounts = generateAccounts(account1Id, account2Id);

            final var createAccountErrors = client.createAccounts(accounts);
            assertTrue(createAccountErrors.getLength() == 0);

            final var tasks = new TransferTask[TASKS_COUNT];
            for (int i = 0; i < TASKS_COUNT; i++) {
                // Starting multiple threads submitting transfers.
                tasks[i] = new TransferTask(client, account1Id, account2Id, barrier,
                        new CountDownLatch(0));
                tasks[i].start();
            }

            // Wait for all threads:
            for (int i = 0; i < TASKS_COUNT; i++) {
                tasks[i].join();
                assertTrue(tasks[i].result.getLength() == 0);
            }

            // Asserting if all transfers were submitted correctly.
            final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
            assertEquals(2, lookupAccounts.getLength());

            accounts.beforeFirst();

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * TASKS_COUNT), lookupAccounts.getCreditsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * TASKS_COUNT), lookupAccounts.getDebitsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        }
    }

    /**
     * This test asserts that parallel threads will respect client's concurrencyMax.
     */
    @Test
    public void testConcurrencyExceeded() throws Throwable {
        // Defining a ratio between concurrent threads and client's concurrencyMax
        // The goal here is to force to have more threads than the client can process
        // simultaneously.
        final int TASKS_COUNT = 32;
        final int CONCURRENCY_MAX = 2;
        final var barrier = new CountDownLatch(TASKS_COUNT);

        try (final var client =
                new Client(clusterId, new String[] {server.getAddress()}, CONCURRENCY_MAX)) {
            final var account1Id = UInt128.id();
            final var account2Id = UInt128.id();
            final var accounts = generateAccounts(account1Id, account2Id);

            final var createAccountErrors = client.createAccounts(accounts);
            assertTrue(createAccountErrors.getLength() == 0);

            final var tasks = new TransferTask[TASKS_COUNT];
            for (int i = 0; i < TASKS_COUNT; i++) {
                // Starting multiple threads submitting transfers.
                tasks[i] = new TransferTask(client, account1Id, account2Id, barrier,
                        new CountDownLatch(0));
                tasks[i].start();
            }

            // Wait for all threads:
            int succeededCount = 0;
            int failedCount = 0;
            for (int i = 0; i < TASKS_COUNT; i++) {
                tasks[i].join();
                if (tasks[i].exception == null) {
                    assertTrue(tasks[i].result.getLength() == 0);
                    succeededCount += 1;
                } else {
                    assertEquals(ConcurrencyExceededException.class, tasks[i].exception.getClass());
                    failedCount += 1;
                }
            }

            // At least max_concurrency tasks must succeed.
            assertTrue(succeededCount >= CONCURRENCY_MAX);
            assertTrue(succeededCount + failedCount == TASKS_COUNT);

            // Asserting if all transfers were submitted correctly.
            final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
            assertEquals(2, lookupAccounts.getLength());

            accounts.beforeFirst();

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * succeededCount),
                    lookupAccounts.getCreditsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * succeededCount),
                    lookupAccounts.getDebitsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        }
    }

    /**
     * This test asserts that client.close() will wait for all ongoing request to complete And new
     * threads trying to submit a request after the client was closed will fail with
     * IllegalStateException.
     */
    @Test
    public void testCloseWithConcurrentTasks() throws Throwable {
        // The goal here is to queue many concurrent requests,
        // so we have a good chance of testing "client.close()" not only before/after
        // calling "submit()", but also during the native call.
        //
        // Unfortunately this is a hacky test, but a reasonable one:
        // Since our JNI module does not expose the acquire_packet function,
        // we cannot insert a lock/wait in between "acquire_packet" and "submit"
        // in order to cause and assert each variant.
        final int TASKS_COUNT = 256;
        final int CONCURRENCY_MAX = TASKS_COUNT;
        final var enterBarrier = new CountDownLatch(TASKS_COUNT);
        final var exitBarrier = new CountDownLatch(1);

        try (final var client =
                new Client(clusterId, new String[] {server.getAddress()}, CONCURRENCY_MAX)) {
            final var account1Id = UInt128.id();
            final var account2Id = UInt128.id();
            final var accounts = generateAccounts(account1Id, account2Id);

            final var createAccountErrors = client.createAccounts(accounts);
            assertTrue(createAccountErrors.getLength() == 0);

            final var tasks = new TransferTask[TASKS_COUNT];
            for (int i = 0; i < TASKS_COUNT; i++) {

                // Starting multiple threads submitting transfers.
                tasks[i] =
                        new TransferTask(client, account1Id, account2Id, enterBarrier, exitBarrier);
                tasks[i].start();
            }

            // Waits until one thread finish.
            exitBarrier.await();

            // And then close the client while threads are still working
            // Some of them have already submitted the request, while others will fail
            // due to "shutdown".
            client.close();

            int failedCount = 0;
            int succeededCount = 0;

            for (int i = 0; i < TASKS_COUNT; i++) {

                // The client.close must wait until all submitted requests have completed
                // Asserting that either the task succeeded or failed while waiting.
                tasks[i].join();

                final var succeeded = tasks[i].result != null && tasks[i].result.getLength() == 0;

                // Can fail due to client closed.
                final var failed = tasks[i].exception != null
                        && tasks[i].exception instanceof IllegalStateException;

                assertTrue(failed || succeeded);

                if (failed) {
                    failedCount += 1;
                } else if (succeeded) {
                    succeededCount += 1;
                }
            }

            assertTrue(succeededCount + failedCount == TASKS_COUNT);
        }
    }

    /**
     * This test asserts that submit a request after the client was closed will fail with
     * IllegalStateException.
     */
    @Test
    public void testClose() throws Throwable {
        try {
            // As we call client.close() explicitly,
            // we don't need to use a try-with-resources block here.
            final var client = new Client(clusterId, new String[] {server.getAddress()});

            // Creating accounts.
            final var account1Id = UInt128.id();
            final var account2Id = UInt128.id();
            final var accounts = generateAccounts(account1Id, account2Id);

            final var createAccountErrors = client.createAccounts(accounts);
            assertTrue(createAccountErrors.getLength() == 0);

            // Closing the client.
            client.close();

            // Creating a transfer with a closed client.
            final var transfers = new TransferBatch(2);

            transfers.add();
            transfers.setId(UInt128.id());
            transfers.setCreditAccountId(account1Id);
            transfers.setDebitAccountId(account2Id);
            transfers.setLedger(720);
            transfers.setCode((short) 1);
            transfers.setFlags(TransferFlags.NONE);
            transfers.setAmount(100);

            client.createTransfers(transfers);
            assert false;

        } catch (Throwable any) {
            assertEquals(IllegalStateException.class, any.getClass());
        }
    }

    /**
     * This test asserts that async tasks will respect client's concurrencyMax.
     */
    @Test
    public void testAsyncTasks() throws Throwable {
        final int TASKS_COUNT = 1_000_000;
        final int CONCURRENCY_MAX = 8192;
        final var semaphore = new Semaphore(CONCURRENCY_MAX);

        final var executor = Executors.newFixedThreadPool(4);

        try (final var client =
                new Client(clusterId, new String[] {server.getAddress()}, CONCURRENCY_MAX)) {

            final var account1Id = UInt128.id();
            final var account2Id = UInt128.id();
            final var accounts = generateAccounts(account1Id, account2Id);

            final var createAccountErrors = client.createAccounts(accounts);
            assertTrue(createAccountErrors.getLength() == 0);

            final var tasks = new CompletableFuture[TASKS_COUNT];
            for (int i = 0; i < TASKS_COUNT; i++) {

                final var transfers = new TransferBatch(1);
                transfers.add();

                transfers.setId(UInt128.id());
                transfers.setCreditAccountId(account1Id);
                transfers.setDebitAccountId(account2Id);
                transfers.setLedger(720);
                transfers.setCode((short) 1);
                transfers.setAmount(100);

                // Starting async batch.
                semaphore.acquire();
                tasks[i] = client.createTransfersAsync(transfers).thenApplyAsync((result) -> {
                    semaphore.release();
                    return result;
                }, executor);
            }

            // Wait for all tasks.
            CompletableFuture.allOf(tasks).join();

            for (int i = 0; i < TASKS_COUNT; i++) {
                @SuppressWarnings("unchecked")
                final var future = (CompletableFuture<CreateTransferResultBatch>) tasks[i];
                final var result = future.get();
                assertEquals(0, result.getLength());
            }

            // Asserting if all transfers were submitted correctly.
            final var lookupAccounts = client.lookupAccounts(new IdBatch(account1Id, account2Id));
            assertEquals(2, lookupAccounts.getLength());

            accounts.beforeFirst();

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * TASKS_COUNT), lookupAccounts.getCreditsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getDebitsPosted());

            assertTrue(accounts.next());
            assertTrue(lookupAccounts.next());
            assertAccounts(accounts, lookupAccounts);

            assertEquals(BigInteger.valueOf(100 * TASKS_COUNT), lookupAccounts.getDebitsPosted());
            assertEquals(BigInteger.ZERO, lookupAccounts.getCreditsPosted());
        }
    }

    @Test
    public void testAccountTransfers() throws Throwable {
        final var account1Id = UInt128.id();
        final var account2Id = UInt128.id();
        final var accounts = generateAccounts(account1Id, account2Id);

        // Enabling AccountFlags.HISTORY:
        while (accounts.next()) {
            accounts.setFlags(accounts.getFlags() | AccountFlags.HISTORY);
        }
        accounts.beforeFirst();

        // Creating the accounts.
        final var createAccountErrors = client.createAccounts(accounts);
        assertTrue(createAccountErrors.getLength() == 0);

        // Creating a transfer.
        final var transfers = new TransferBatch(10);
        for (int i = 0; i < 10; i++) {
            transfers.add();
            transfers.setId(UInt128.id());

            // Swap the debit and credit accounts:
            if (i % 2 == 0) {
                transfers.setCreditAccountId(account1Id);
                transfers.setDebitAccountId(account2Id);
            } else {
                transfers.setCreditAccountId(account2Id);
                transfers.setDebitAccountId(account1Id);
            }

            transfers.setLedger(720);
            transfers.setCode((short) 1);
            transfers.setFlags(TransferFlags.NONE);
            transfers.setAmount(100);
        }

        final var createTransferErrors = client.createTransfers(transfers);
        assertTrue(createTransferErrors.getLength() == 0);

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id OR credit_account_id=$account1Id
            // ORDER BY timestamp ASC`.
            final var filter = new AccountFilter();
            filter.setAccountId(account1Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            final var accountTransfers = client.getAccountTransfers(filter);
            final var accountHistory = client.getAccountHistory(filter);
            assertTrue(accountTransfers.getLength() == 10);
            assertTrue(accountHistory.getLength() == 10);
            long timestamp = 0;
            while (accountTransfers.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers.getTimestamp(), timestamp) > 0);
                timestamp = accountTransfers.getTimestamp();

                assertTrue(accountHistory.next());
                assertEquals(accountTransfers.getTimestamp(), accountHistory.getTimestamp());
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account2Id OR credit_account_id=$account2Id
            // ORDER BY timestamp DESC`.
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(true);
            final var accountTransfers = client.getAccountTransfers(filter);
            final var accountHistory = client.getAccountHistory(filter);

            assertTrue(accountTransfers.getLength() == 10);
            assertTrue(accountHistory.getLength() == 10);
            long timestamp = Long.MIN_VALUE; // MIN_VALUE is the unsigned MAX_VALUE.
            while (accountTransfers.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers.getTimestamp(), timestamp) < 0);
                timestamp = accountTransfers.getTimestamp();

                assertTrue(accountHistory.next());
                assertEquals(accountTransfers.getTimestamp(), accountHistory.getTimestamp());
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id
            // ORDER BY timestamp ASC`.
            final var filter = new AccountFilter();
            filter.setAccountId(account1Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(false);
            filter.setReversed(false);
            final var accountTransfers = client.getAccountTransfers(filter);
            final var accountHistory = client.getAccountHistory(filter);

            assertTrue(accountTransfers.getLength() == 5);
            assertTrue(accountHistory.getLength() == 5);
            long timestamp = 0;
            while (accountTransfers.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers.getTimestamp(), timestamp) > 0);
                timestamp = accountTransfers.getTimestamp();

                assertTrue(accountHistory.next());
                assertEquals(accountTransfers.getTimestamp(), accountHistory.getTimestamp());
            }
        }

        {
            // Querying transfers where:
            // `credit_account_id=$account2Id
            // ORDER BY timestamp DESC`.
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(1);
            filter.setTimestampMax(-2L); // -2L == ulong max - 1
            filter.setLimit(8190);
            filter.setDebits(false);
            filter.setCredits(true);
            filter.setReversed(true);
            final var accountTransfers = client.getAccountTransfers(filter);
            final var accountHistory = client.getAccountHistory(filter);

            assertTrue(accountTransfers.getLength() == 5);
            assertTrue(accountHistory.getLength() == 5);

            long timestamp = Long.MIN_VALUE; // MIN_VALUE is the unsigned MAX_VALUE.
            while (accountTransfers.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers.getTimestamp(), timestamp) < 0);
                timestamp = accountTransfers.getTimestamp();

                assertTrue(accountHistory.next());
                assertEquals(accountTransfers.getTimestamp(), accountHistory.getTimestamp());
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id OR credit_account_id=$account1Id
            // ORDER BY timestamp ASC LIMIT 5`.
            final var filter = new AccountFilter();
            filter.setAccountId(account1Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(5);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);

            // First 5 items:
            final var accountTransfers1 = client.getAccountTransfers(filter);
            final var accountHistory1 = client.getAccountHistory(filter);

            assertTrue(accountTransfers1.getLength() == 5);
            assertTrue(accountHistory1.getLength() == 5);

            long timestamp = 0;
            while (accountTransfers1.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers1.getTimestamp(), timestamp) > 0);
                timestamp = accountTransfers1.getTimestamp();

                assertTrue(accountHistory1.next());
                assertEquals(accountTransfers1.getTimestamp(), accountHistory1.getTimestamp());
            }

            // Next 5 items from this timestamp:
            filter.setTimestampMin(timestamp + 1);
            final var accountTransfers2 = client.getAccountTransfers(filter);
            final var accountHistory2 = client.getAccountHistory(filter);

            assertTrue(accountTransfers2.getLength() == 5);
            assertTrue(accountHistory2.getLength() == 5);

            while (accountTransfers2.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers2.getTimestamp(), timestamp) > 0);
                timestamp = accountTransfers2.getTimestamp();

                assertTrue(accountHistory2.next());
                assertEquals(accountTransfers2.getTimestamp(), accountHistory2.getTimestamp());
            }

            // No more results after that timestamp:
            filter.setTimestampMin(timestamp + 1);
            final var accountTransfers3 = client.getAccountTransfers(filter);
            final var accountHistory3 = client.getAccountHistory(filter);

            assertTrue(accountTransfers3.getLength() == 0);
            assertTrue(accountHistory3.getLength() == 0);
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account2Id OR credit_account_id=$account2Id
            // ORDER BY timestamp DESC LIMIT 5`.
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(5);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(true);

            // First 5 items:
            final var accountTransfers1 = client.getAccountTransfers(filter);
            final var accountHistory1 = client.getAccountHistory(filter);

            assertTrue(accountTransfers1.getLength() == 5);
            assertTrue(accountTransfers1.getLength() == 5);

            long timestamp = Long.MIN_VALUE; // MIN_VALUE is the unsigned MAX_VALUE.
            while (accountTransfers1.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers1.getTimestamp(), timestamp) < 0);
                timestamp = accountTransfers1.getTimestamp();

                assertTrue(accountHistory1.next());
                assertEquals(accountTransfers1.getTimestamp(), accountHistory1.getTimestamp());
            }

            // Next 5 items from this timestamp:
            filter.setTimestampMax(timestamp - 1);
            final var accountTransfers2 = client.getAccountTransfers(filter);
            final var accountHistory2 = client.getAccountHistory(filter);

            assertTrue(accountTransfers2.getLength() == 5);
            assertTrue(accountHistory2.getLength() == 5);

            while (accountTransfers2.next()) {
                assertTrue(Long.compareUnsigned(accountTransfers2.getTimestamp(), timestamp) < 0);
                timestamp = accountTransfers2.getTimestamp();

                assertTrue(accountHistory2.next());
                assertEquals(accountTransfers2.getTimestamp(), accountHistory2.getTimestamp());
            }

            // No more results before that timestamp:
            filter.setTimestampMax(timestamp - 1);
            final var accountTransfers3 = client.getAccountTransfers(filter);
            final var accountHistory3 = client.getAccountHistory(filter);

            assertTrue(accountTransfers3.getLength() == 0);
            assertTrue(accountHistory3.getLength() == 0);
        }

        // For those tests it doesn't matter using the sync or async version. We use the async
        // version here for test coverage purposes, but there's no need to duplicate the tests.

        {
            // Empty filter:
            final var filter = new AccountFilter();
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Invalid account:
            final var filter = new AccountFilter();
            filter.setAccountId(0);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Invalid timestamp min:
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(-1L); // -1L == ulong max value
            filter.setTimestampMax(0);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Invalid timestamp max:
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(-1L); // -1L == ulong max value
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Invalid timestamp min > max:
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(-2L); // -2L == ulong max - 1
            filter.setTimestampMax(1);
            filter.setLimit(8190);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Zero limit:
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(0);
            filter.setDebits(true);
            filter.setCredits(true);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }

        {
            // Zero flags:
            final var filter = new AccountFilter();
            filter.setAccountId(account2Id);
            filter.setTimestampMin(0);
            filter.setTimestampMax(0);
            filter.setLimit(0);
            filter.setDebits(false);
            filter.setCredits(false);
            filter.setReversed(false);
            assertTrue(client.getAccountTransfersAsync(filter).get().getLength() == 0);
            assertTrue(client.getAccountHistoryAsync(filter).get().getLength() == 0);
        }
    }

    private static void assertAccounts(AccountBatch account1, AccountBatch account2) {
        assertArrayEquals(account1.getId(), account2.getId());
        assertArrayEquals(account1.getUserData128(), account2.getUserData128());
        assertEquals(account1.getUserData64(), account2.getUserData64());
        assertEquals(account1.getUserData32(), account2.getUserData32());
        assertEquals(account1.getLedger(), account2.getLedger());
        assertEquals(account1.getCode(), account2.getCode());
        assertEquals(account1.getFlags(), account2.getFlags());
    }

    private static void assertTransfers(TransferBatch transfer1, TransferBatch transfer2) {
        assertArrayEquals(transfer1.getId(), transfer2.getId());
        assertArrayEquals(transfer1.getDebitAccountId(), transfer2.getDebitAccountId());
        assertArrayEquals(transfer1.getCreditAccountId(), transfer2.getCreditAccountId());
        assertEquals(transfer1.getAmount(), transfer2.getAmount());
        assertArrayEquals(transfer1.getPendingId(), transfer2.getPendingId());
        assertArrayEquals(transfer1.getUserData128(), transfer2.getUserData128());
        assertEquals(transfer1.getUserData64(), transfer2.getUserData64());
        assertEquals(transfer1.getUserData32(), transfer2.getUserData32());
        assertEquals(transfer1.getTimeout(), transfer2.getTimeout());
        assertEquals(transfer1.getLedger(), transfer2.getLedger());
        assertEquals(transfer1.getCode(), transfer2.getCode());
        assertEquals(transfer1.getFlags(), transfer2.getFlags());
    }

    private static class TransferTask extends Thread {
        public final Client client;
        public CreateTransferResultBatch result;
        public Throwable exception;
        private byte[] account1Id;
        private byte[] account2Id;
        private CountDownLatch enterBarrier;
        private CountDownLatch exitBarrier;

        public TransferTask(Client client, byte[] account1Id, byte[] account2Id,
                CountDownLatch enterBarrier, CountDownLatch exitBarrier) {
            this.client = client;
            this.result = null;
            this.exception = null;
            this.account1Id = account1Id;
            this.account2Id = account2Id;
            this.enterBarrier = enterBarrier;
            this.exitBarrier = exitBarrier;
        }

        @Override
        public synchronized void run() {

            final var transfers = new TransferBatch(1);
            transfers.add();

            transfers.setId(UInt128.asBytes(UUID.randomUUID()));
            transfers.setCreditAccountId(account1Id);
            transfers.setDebitAccountId(account2Id);
            transfers.setLedger(720);
            transfers.setCode((short) 1);
            transfers.setAmount(100);

            try {
                enterBarrier.countDown();
                enterBarrier.await();
                result = client.createTransfers(transfers);
            } catch (Throwable e) {
                exception = e;
            } finally {
                exitBarrier.countDown();
            }
        }
    }

    private static class Server implements AutoCloseable {

        public static final String TB_FILE = "./0_0.tigerbeetle.tests";
        public static final String TB_SERVER = "../../../zig-out/bin/tigerbeetle";

        private final Process process;
        private String address;

        public Server() throws IOException, Exception, InterruptedException {

            cleanUp();

            String exe;
            switch (JNILoader.OS.getOS()) {
                case windows:
                    exe = TB_SERVER + ".exe";
                    break;
                default:
                    exe = TB_SERVER;
                    break;
            }

            final var format = Runtime.getRuntime().exec(new String[] {exe, "format", "--cluster=0",
                    "--replica=0", "--replica-count=1", TB_FILE});
            if (format.waitFor() != 0) {
                final var reader =
                        new BufferedReader(new InputStreamReader(format.getErrorStream()));
                final var error = reader.lines().collect(Collectors.joining(". "));
                throw new Exception("Format failed. " + error);
            }

            this.process = new ProcessBuilder()
                    .command(new String[] {exe, "start", "--addresses=0", "--cache-grid=512MB",
                            TB_FILE})
                    .redirectOutput(Redirect.PIPE).redirectError(Redirect.DISCARD).start();

            final var stdout = process.getInputStream();
            try (final var reader = new BufferedReader(new InputStreamReader(stdout))) {
                this.address = reader.readLine().trim();
            }
        }

        public String getAddress() {
            return address;
        }

        @Override
        public void close() throws Exception {
            cleanUp();
        }

        private void cleanUp() throws Exception {
            try {
                if (process != null && process.isAlive()) {
                    process.destroy();
                }

                final var file = new File("./" + TB_FILE);
                file.delete();
            } catch (Throwable any) {
                throw new Exception("Cleanup has failed");
            }
        }
    }
}
