using Microsoft.VisualStudio.TestTools.UnitTesting;
using System;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

namespace TigerBeetle.Tests;

[TestClass]
public class IntegrationTests
{
    private static Account[] GenerateAccounts() => new[]
    {
            new Account
            {
                Id = ID.Create(),
                UserData128 = 1000,
                UserData64 = 1001,
                UserData32 = 1002,
                Flags = AccountFlags.None,
                Ledger = 1,
                Code = 1,
            },
            new Account
            {
                Id = ID.Create(),
                UserData128 = 1000,
                UserData64 = 1001,
                UserData32 = 1002,
                Flags = AccountFlags.None,
                Ledger = 1,
                Code = 2,
            },
    };

    // Created by the test initializer:
    private static TBServer server = null!;
    private static Client client = null!;

    [ClassInitialize]
    public static void Initialize(TestContext _)
    {
        server = new TBServer();
        client = new Client(0, new string[] { server.Address });
    }

    [ClassCleanup]
    public static void Cleanup()
    {
        client.Dispose();
        server.Dispose();
    }

    [TestMethod]
    [ExpectedException(typeof(ArgumentNullException))]
    public void ConstructorWithNullReplicaAddresses()
    {
        string[]? addresses = null;
        _ = new Client(0, addresses!, 1);
    }

    [TestMethod]
    public void ConstructorWithNullReplicaAddressElement()
    {
        try
        {
            var addresses = new string?[] { "3000", null };
            _ = new Client(0, addresses!, 1);
            Assert.Fail();
        }
        catch (InitializationException exception)
        {
            Assert.AreEqual(InitializationStatus.AddressInvalid, exception.Status);
        }
    }

    [TestMethod]
    public void ConstructorWithEmptyReplicaAddresses()
    {
        try
        {
            _ = new Client(0, Array.Empty<string>(), 1);
            Assert.Fail();
        }
        catch (InitializationException exception)
        {
            Assert.AreEqual(InitializationStatus.AddressInvalid, exception.Status);
        }
    }

    [TestMethod]
    public void ConstructorWithEmptyReplicaAddressElement()
    {
        try
        {
            _ = new Client(0, new string[] { "" }, 1);
            Assert.Fail();
        }
        catch (InitializationException exception)
        {
            Assert.AreEqual(InitializationStatus.AddressInvalid, exception.Status);
        }
    }

    [TestMethod]
    public void ConstructorWithInvalidReplicaAddresses()
    {
        try
        {
            var addresses = Enumerable.Range(3000, 3100).Select(x => x.ToString()).ToArray();
            _ = new Client(0, addresses, 1);
            Assert.Fail();
        }
        catch (InitializationException exception)
        {
            Assert.AreEqual(InitializationStatus.AddressLimitExceeded, exception.Status);
        }
    }

    [TestMethod]
    [ExpectedException(typeof(ArgumentOutOfRangeException))]
    public void ConstructorWithZeroConcurrencyMax()
    {
        _ = new Client(0, new string[] { "3000" }, 0);
    }

    [TestMethod]
    [ExpectedException(typeof(ArgumentOutOfRangeException))]
    public void ConstructorWithNegativeConcurrencyMax()
    {
        _ = new Client(0, new string[] { "3000" }, -1);
    }

    [TestMethod]
    public void ConstructorWithInvalidConcurrencyMax()
    {
        try
        {
            _ = new Client(0, new string[] { "3000" }, 99_999);
            Assert.Fail();
        }
        catch (InitializationException exception)
        {
            Assert.AreEqual(InitializationStatus.ConcurrencyMaxInvalid, exception.Status);
        }
    }

    [TestMethod]
    public void ConstructorAndFinalizer()
    {
        // No using here, we want to test the finalizer
        var client = new Client(1, new string[] { "3000" }, 32);
        Assert.IsTrue(client.ClusterID == 1);
    }

    [TestMethod]
    public void CreateAccount()
    {
        var accounts = GenerateAccounts();

        var okResult = client.CreateAccount(accounts[0]);
        Assert.IsTrue(okResult == CreateAccountResult.Ok);

        var lookupAccount = client.LookupAccount(accounts[0].Id);
        Assert.IsNotNull(lookupAccount);
        AssertAccount(accounts[0], lookupAccount.Value);

        var existsResult = client.CreateAccount(accounts[0]);
        Assert.IsTrue(existsResult == CreateAccountResult.Exists);
    }

    [TestMethod]
    public async Task CreateAccountAsync()
    {
        var accounts = GenerateAccounts();

        var okResult = await client.CreateAccountAsync(accounts[0]);
        Assert.IsTrue(okResult == CreateAccountResult.Ok);

        var lookupAccount = await client.LookupAccountAsync(accounts[0].Id);
        Assert.IsNotNull(lookupAccount);
        AssertAccount(accounts[0], lookupAccount.Value);

        var existsResult = await client.CreateAccountAsync(accounts[0]);
        Assert.IsTrue(existsResult == CreateAccountResult.Exists);
    }

    [TestMethod]
    public void CreateAccounts()
    {
        var accounts = GenerateAccounts();

        var results = client.CreateAccounts(accounts);
        Assert.IsTrue(results.Length == 0);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);
    }

    [TestMethod]
    public async Task CreateAccountsAsync()
    {
        var accounts = GenerateAccounts();

        var results = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(results.Length == 0);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);
    }

    [TestMethod]
    public void CreateTransfers()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
        };

        var transferResults = client.CreateTransfers(new[] { transfer });
        Assert.IsTrue(transferResults.Length == 0);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        var lookupTransfers = client.LookupTransfers(new UInt128[] { transfer.Id });
        Assert.IsTrue(lookupTransfers.Length == 1);
        AssertTransfer(transfer, lookupTransfers[0]);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer.Amount);
    }

    [TestMethod]
    public async Task CreateTransfersAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
        };

        var transferResults = await client.CreateTransfersAsync(new[] { transfer });
        Assert.IsTrue(transferResults.Length == 0);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        var lookupTransfers = await client.LookupTransfersAsync(new UInt128[] { transfer.Id });
        Assert.IsTrue(lookupTransfers.Length == 1);
        AssertTransfer(transfer, lookupTransfers[0]);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer.Amount);
    }

    [TestMethod]
    public void CreateTransfer()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
        };

        var successResult = client.CreateTransfer(transfer);
        Assert.IsTrue(successResult == CreateTransferResult.Ok);

        var lookupTransfer = client.LookupTransfer(transfer.Id);
        Assert.IsTrue(lookupTransfer != null);
        AssertTransfer(transfer, lookupTransfer!.Value);

        var existsResult = client.CreateTransfer(transfer);
        Assert.IsTrue(existsResult == CreateTransferResult.Exists);
    }

    [TestMethod]
    public async Task CreateTransferAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
        };

        var successResult = await client.CreateTransferAsync(transfer);
        Assert.IsTrue(successResult == CreateTransferResult.Ok);

        var lookupTransfer = await client.LookupTransferAsync(transfer.Id);
        Assert.IsTrue(lookupTransfer != null);
        AssertTransfer(transfer, lookupTransfer!.Value);

        var existsResult = await client.CreateTransferAsync(transfer);
        Assert.IsTrue(existsResult == CreateTransferResult.Exists);
    }

    [TestMethod]
    public void CreatePendingTransfers()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = uint.MaxValue,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = client.CreateTransfer(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            PendingId = transfer.Id,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.PostPendingTransfer,
        };

        var postResult = client.CreateTransfer(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.Ok);

        lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
    }

    [TestMethod]
    public async Task CreatePendingTransfersAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = uint.MaxValue,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = await client.CreateTransferAsync(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            PendingId = transfer.Id,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.PostPendingTransfer,
        };

        var postResult = await client.CreateTransferAsync(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.Ok);

        lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
    }

    [TestMethod]
    public void CreatePendingTransfersAndVoid()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = uint.MaxValue,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = client.CreateTransfer(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.VoidPendingTransfer,
            PendingId = transfer.Id,
        };

        var postResult = client.CreateTransfer(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.Ok);

        lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
    }

    [TestMethod]
    public async Task CreatePendingTransfersAndVoidAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = uint.MaxValue,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = await client.CreateTransferAsync(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            PendingId = transfer.Id,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.VoidPendingTransfer,
        };

        var postResult = await client.CreateTransferAsync(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.Ok);

        lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
    }

    [TestMethod]

    public void CreatePendingTransfersAndVoidExpired()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = 1,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = client.CreateTransfer(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        // Waiting for the transfer to expire:
        Thread.Sleep(1000);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.VoidPendingTransfer,
            PendingId = transfer.Id,
        };

        var postResult = client.CreateTransfer(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.PendingTransferExpired);
    }

    [TestMethod]
    public async Task CreatePendingTransfersAndVoidExpiredAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Timeout = 1,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Pending,
        };

        var result = await client.CreateTransferAsync(transfer);
        Assert.IsTrue(result == CreateTransferResult.Ok);

        var lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, (UInt128)0);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, transfer.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (UInt128)0);

        // Waiting for the transfer to expire:
        // Do not use Task.Delay here as it seems to be less precise.
        Thread.Sleep(1000);

        var postTransfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            PendingId = transfer.Id,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.VoidPendingTransfer,
        };

        var postResult = await client.CreateTransferAsync(postTransfer);
        Assert.IsTrue(postResult == CreateTransferResult.PendingTransferExpired);
    }


    [TestMethod]
    public void CreateLinkedTransfers()
    {
        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer1 = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Linked,
        };

        var transfer2 = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[1].Id,
            DebitAccountId = accounts[0].Id,
            Amount = 49,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.None,
        };

        var transferResults = client.CreateTransfers(new[] { transfer1, transfer2 });
        Assert.IsTrue(transferResults.All(x => x.Result == CreateTransferResult.Ok));

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        var lookupTransfers = client.LookupTransfers(new UInt128[] { transfer1.Id, transfer2.Id });
        Assert.IsTrue(lookupTransfers.Length == 2);
        AssertTransfer(transfer1, lookupTransfers[0]);
        AssertTransfer(transfer2, lookupTransfers[1]);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer1.Amount);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, transfer2.Amount);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, transfer2.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer1.Amount);
    }

    [TestMethod]
    public async Task CreateLinkedTransfersAsync()
    {
        var accounts = GenerateAccounts();
        var accountResults = await client.CreateAccountsAsync(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var transfer1 = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.Linked,
        };

        var transfer2 = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[1].Id,
            DebitAccountId = accounts[0].Id,
            Amount = 49,
            Ledger = 1,
            Code = 1,
            Flags = TransferFlags.None,
        };

        var transferResults = await client.CreateTransfersAsync(new[] { transfer1, transfer2 });
        Assert.IsTrue(transferResults.All(x => x.Result == CreateTransferResult.Ok));

        var lookupAccounts = await client.LookupAccountsAsync(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        var lookupTransfers = await client.LookupTransfersAsync(new UInt128[] { transfer1.Id, transfer2.Id });
        Assert.IsTrue(lookupTransfers.Length == 2);
        AssertTransfer(transfer1, lookupTransfers[0]);
        AssertTransfer(transfer2, lookupTransfers[1]);

        Assert.AreEqual(lookupAccounts[0].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].CreditsPosted, transfer1.Amount);
        Assert.AreEqual(lookupAccounts[0].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, transfer2.Amount);

        Assert.AreEqual(lookupAccounts[1].CreditsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].CreditsPosted, transfer2.Amount);
        Assert.AreEqual(lookupAccounts[1].DebitsPending, (UInt128)0);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, transfer1.Amount);
    }


    [TestMethod]
    public void CreateAccountTooMuchData()
    {
        const int TOO_MUCH_DATA = 10_000;
        var accounts = new Account[TOO_MUCH_DATA];
        for (int i = 0; i < TOO_MUCH_DATA; i++)
        {
            accounts[i] = new Account
            {
                Id = ID.Create(),
                Code = 1,
                Ledger = 1
            };
        }

        try
        {
            _ = client.CreateAccounts(accounts);
            Assert.Fail();
        }
        catch (RequestException requestException)
        {
            Assert.AreEqual(PacketStatus.TooMuchData, requestException.Status);
        }
    }

    [TestMethod]

    public async Task CreateAccountTooMuchDataAsync()
    {
        const int TOO_MUCH_DATA = 10_000;
        var accounts = new Account[TOO_MUCH_DATA];
        for (int i = 0; i < TOO_MUCH_DATA; i++)
        {
            accounts[i] = new Account
            {
                Id = ID.Create(),
                Code = 1,
                Ledger = 1
            };
        }

        try
        {
            _ = await client.CreateAccountsAsync(accounts);
            Assert.Fail();
        }
        catch (RequestException requestException)
        {
            Assert.AreEqual(PacketStatus.TooMuchData, requestException.Status);
        }
    }

    [TestMethod]
    public void CreateTransferTooMuchData()
    {
        const int TOO_MUCH_DATA = 10_000;
        var transfers = new Transfer[TOO_MUCH_DATA];
        for (int i = 0; i < TOO_MUCH_DATA; i++)
        {
            transfers[i] = new Transfer
            {
                Id = ID.Create(),
                Code = 1,
                Ledger = 1
            };
        }

        try
        {
            _ = client.CreateTransfers(transfers);
            Assert.Fail();
        }
        catch (RequestException requestException)
        {
            Assert.AreEqual(PacketStatus.TooMuchData, requestException.Status);
        }
    }

    [TestMethod]
    public async Task CreateTransferTooMuchDataAsync()
    {
        const int TOO_MUCH_DATA = 10_000;
        var transfers = new Transfer[TOO_MUCH_DATA];
        for (int i = 0; i < TOO_MUCH_DATA; i++)
        {
            transfers[i] = new Transfer
            {
                Id = ID.Create(),
                DebitAccountId = 1,
                CreditAccountId = 2,
                Code = 1,
                Ledger = 1,
                Amount = 100,
            };
        }

        try
        {
            _ = await client.CreateTransfersAsync(transfers);
            Assert.Fail();
        }
        catch (RequestException requestException)
        {
            Assert.AreEqual(PacketStatus.TooMuchData, requestException.Status);
        }
    }


    [TestMethod]
    public void TestGetAccountTransfers()
    {
        var accounts = GenerateAccounts();
        accounts[0].Flags |= AccountFlags.History;
        accounts[1].Flags |= AccountFlags.History;

        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        // Creating a transfer.
        var transfers = new Transfer[10];
        for (int i = 0; i < 10; i++)
        {
            transfers[i] = new Transfer
            {
                Id = ID.Create(),

                // Swap the debit and credit accounts:
                CreditAccountId = i % 2 == 0 ? accounts[0].Id : accounts[1].Id,
                DebitAccountId = i % 2 == 0 ? accounts[1].Id : accounts[0].Id,

                Ledger = 1,
                Code = 2,
                Flags = TransferFlags.None,
                Amount = 100
            };
        }

        var createTransferErrors = client.CreateTransfers(transfers);
        Assert.IsTrue(createTransferErrors.Length == 0);

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id OR credit_account_id=$account1Id
            // ORDER BY timestamp ASC`.
            var filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits
            };
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 10);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = 0;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp > timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account2Id OR credit_account_id=$account2Id
            // ORDER BY timestamp DESC`.
            var filter = new AccountFilter
            {
                AccountId = accounts[1].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits | AccountFilterFlags.Reversed
            };
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 10);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = ulong.MaxValue;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp < timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id
            // ORDER BY timestamp ASC`.
            var filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = AccountFilterFlags.Debits
            };
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = 0;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp > timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }
        }

        {
            // Querying transfers where:
            // `credit_account_id=$account2Id
            // ORDER BY timestamp DESC`.
            var filter = new AccountFilter
            {
                AccountId = accounts[1].Id,
                TimestampMin = 1,
                TimestampMax = ulong.MaxValue - 1,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Reversed
            };
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = ulong.MaxValue;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp < timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account1Id OR credit_account_id=$account1Id
            // ORDER BY timestamp ASC LIMIT 5`.
            var filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 5,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits
            };

            // First 5 items:
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = 0;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp > timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }

            // Next 5 items from this timestamp:
            filter.TimestampMin = timestamp + 1;
            account_transfers = client.GetAccountTransfers(filter);
            account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp > timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }

            // No more pages after that:
            filter.TimestampMin = timestamp + 1;
            account_transfers = client.GetAccountTransfers(filter);
            account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 0);
            Assert.IsTrue(account_history.Length == account_transfers.Length);
        }

        {
            // Querying transfers where:
            // `debit_account_id=$account2Id OR credit_account_id=$account2Id
            // ORDER BY timestamp DESC LIMIT 5`.
            var filter = new AccountFilter
            {
                AccountId = accounts[1].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 5,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits | AccountFilterFlags.Reversed
            };

            // First 5 items:
            var account_transfers = client.GetAccountTransfers(filter);
            var account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            ulong timestamp = ulong.MaxValue;
            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp < timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }

            // Next 5 items from this timestamp:
            filter.TimestampMax = timestamp - 1;
            account_transfers = client.GetAccountTransfers(filter);
            account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 5);
            Assert.IsTrue(account_history.Length == account_transfers.Length);

            for (int i = 0; i < account_transfers.Length; i++)
            {
                var transfer = account_transfers[i];
                Assert.IsTrue(transfer.Timestamp < timestamp);
                timestamp = transfer.Timestamp;

                var balance = account_history[i];
                Assert.IsTrue(balance.Timestamp == transfer.Timestamp);
            }

            // No more pages after that:
            filter.TimestampMax = timestamp - 1;
            account_transfers = client.GetAccountTransfers(filter);
            account_history = client.GetAccountHistory(filter);

            Assert.IsTrue(account_transfers.Length == 0);
            Assert.IsTrue(account_history.Length == account_transfers.Length);
        }

        {
            // Empty filter:
            Assert.IsTrue(client.GetAccountTransfers(new AccountFilter { }).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(new AccountFilter { }).Length == 0);

            // Invalid account
            var filter = new AccountFilter
            {
                AccountId = 0,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Invalid timestamp min
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = ulong.MaxValue,
                TimestampMax = 0,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Invalid timestamp max
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = ulong.MaxValue,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Invalid timestamp range
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = ulong.MaxValue - 1,
                TimestampMax = 1,
                Limit = 8190,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Zero limit
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 0,
                Flags = AccountFilterFlags.Credits | AccountFilterFlags.Debits,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Empty flags
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = (AccountFilterFlags)0,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);

            // Invalid flags
            filter = new AccountFilter
            {
                AccountId = accounts[0].Id,
                TimestampMin = 0,
                TimestampMax = 0,
                Limit = 8190,
                Flags = (AccountFilterFlags)0xFFFF,
            };
            Assert.IsTrue(client.GetAccountTransfers(filter).Length == 0);
            Assert.IsTrue(client.GetAccountHistory(filter).Length == 0);
        }
    }

    /// <summary>
    /// This test asserts that a single Client can be shared by multiple concurrent tasks
    /// </summary>

    [TestMethod]
    public void ConcurrencyTest() => ConcurrencyTest(isAsync: false);

    [TestMethod]
    public void ConcurrencyTestAsync() => ConcurrencyTest(isAsync: true);

    private void ConcurrencyTest(bool isAsync)
    {
        const int TASKS_QTY = 1_000_000;
        const int CONCURRENCY_MAX = 8192;

        using var client = new Client(0, new[] { server.Address }, CONCURRENCY_MAX);

        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);


        var tasks = new Task<CreateTransferResult>[TASKS_QTY];
        var semaphore = new SemaphoreSlim(CONCURRENCY_MAX);

        async Task<CreateTransferResult> asyncAction(Transfer transfer)
        {
            try
            {
                await semaphore.WaitAsync();
                return await client.CreateTransferAsync(transfer);
            }
            finally
            {
                _ = semaphore.Release();
            }
        }

        CreateTransferResult syncAction(Transfer transfer)
        {
            try
            {
                semaphore.Wait();
                return client.CreateTransfer(transfer);
            }
            finally
            {
                _ = semaphore.Release();
            }
        }

        for (int i = 0; i < TASKS_QTY; i++)
        {
            var transfer = new Transfer
            {
                Id = ID.Create(),
                CreditAccountId = accounts[0].Id,
                DebitAccountId = accounts[1].Id,
                Amount = 1,
                Ledger = 1,
                Code = 1,
            };

            /// Starts multiple tasks.
            var task = isAsync ? asyncAction(transfer) : Task.Run(() => syncAction(transfer));
            tasks[i] = task;
        }

        Task.WhenAll(tasks).Wait();

        Assert.IsTrue(tasks.All(x => x.Result == CreateTransferResult.Ok));

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        // Assert that all tasks ran to the conclusion

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (uint)TASKS_QTY);
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, 0LU);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, 0LU);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (uint)TASKS_QTY);
    }

    /// <summary>
    /// This test asserts that a single Client can be shared by multiple concurrent tasks
    /// Even if a limited "concurrencyMax" value results in "ConcurrencyExceededException"
    /// </summary>

    [TestMethod]
    public void ConcurrencyExceededTest() => ConcurrencyExceededTest(isAsync: false);

    [TestMethod]
    public void ConcurrencyExceededTestAsync() => ConcurrencyExceededTest(isAsync: true);

    private void ConcurrencyExceededTest(bool isAsync)
    {
        const int TASKS_QTY = 32;
        const int CONCURRENCY_MAX = 2;

        using var client = new Client(0, new[] { server.Address }, CONCURRENCY_MAX);

        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var tasks = new Task<CreateTransferResult>[TASKS_QTY];

        for (int i = 0; i < TASKS_QTY; i++)
        {
            var transfer = new Transfer
            {
                Id = ID.Create(),
                CreditAccountId = accounts[0].Id,
                DebitAccountId = accounts[1].Id,
                Ledger = 1,
                Code = 1,
                Amount = 100,
            };

            /// Starts multiple tasks using a client with a limited concurrencyMax:
            var task = isAsync ? client.CreateTransferAsync(transfer) : Task.Run(() => client.CreateTransfer(transfer));
            tasks[i] = task;
        }

        try
        {
            // Ignoring exceptions from the tasks.
            Task.WhenAll(tasks).Wait();
        }
        catch { }

        // It's expected for some tasks to fail with ConcurrencyExceededException:
        var successCount = tasks.Count(x => !x.IsFaulted && x.Result == CreateTransferResult.Ok);
        var failedCount = tasks.Count(x => x.IsFaulted &&
            AssertException<ConcurrencyExceededException>(x.Exception!));
        Assert.IsTrue(successCount > 0);
        Assert.IsTrue(successCount + failedCount == TASKS_QTY);

        // Asserting that either the task failed or succeeded.
        Assert.IsTrue(tasks.All(x => x.IsFaulted || x.Result == CreateTransferResult.Ok));

        var lookupAccounts = client.LookupAccounts(new[] { accounts[0].Id, accounts[1].Id });
        AssertAccounts(accounts, lookupAccounts);

        // Assert that all tasks ran to the conclusion

        Assert.AreEqual(lookupAccounts[0].CreditsPosted, (ulong)(100 * successCount));
        Assert.AreEqual(lookupAccounts[0].DebitsPosted, 0LU);

        Assert.AreEqual(lookupAccounts[1].CreditsPosted, 0LU);
        Assert.AreEqual(lookupAccounts[1].DebitsPosted, (ulong)(100 * successCount));
    }

    /// <summary>
    /// This test asserts that Client.Dispose() will wait for any ongoing request to complete
    /// And new requests will fail with ObjectDisposedException.
    /// </summary>

    [TestMethod]
    public void ConcurrentTasksDispose() => ConcurrentTasksDispose(isAsync: false);

    [TestMethod]
    public void ConcurrentTasksDisposeAsync() => ConcurrentTasksDispose(isAsync: true);

    private void ConcurrentTasksDispose(bool isAsync)
    {
        const int TASKS_QTY = 32;
        const int CONCURRENCY_MAX = 32;

        using var client = new Client(0, new[] { server.Address }, CONCURRENCY_MAX);

        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        var tasks = new Task<CreateTransferResult>[TASKS_QTY];

        for (int i = 0; i < TASKS_QTY; i++)
        {
            var transfer = new Transfer
            {
                Id = ID.Create(),
                CreditAccountId = accounts[0].Id,
                DebitAccountId = accounts[1].Id,
                Amount = 100,
                Ledger = 1,
                Code = 1,
            };

            /// Starts multiple tasks.
            var task = isAsync ? client.CreateTransferAsync(transfer) : Task.Run(() => client.CreateTransfer(transfer));
            tasks[i] = task;
        }

        // Waiting for just one task, the others may be pending.
        Task.WaitAny(tasks);

        // Disposes the client, waiting all placed requests to finish.
        client.Dispose();

        try
        {
            // Ignoring exceptions from the tasks.
            Task.WhenAll(tasks).Wait();
        }
        catch { }

        // Asserting that either the task failed or succeeded,
        // at least one must be succeeded.
        Assert.IsTrue(tasks.Any(x => !x.IsFaulted && x.Result == CreateTransferResult.Ok));
        Assert.IsTrue(tasks.All(x => x.IsFaulted || x.Result == CreateTransferResult.Ok));
    }

    [TestMethod]
    [ExpectedException(typeof(ObjectDisposedException))]
    public void DisposedClient()
    {
        using var client = new Client(0, new[] { server.Address });

        var accounts = GenerateAccounts();
        var accountResults = client.CreateAccounts(accounts);
        Assert.IsTrue(accountResults.Length == 0);

        client.Dispose();

        var transfer = new Transfer
        {
            Id = ID.Create(),
            CreditAccountId = accounts[0].Id,
            DebitAccountId = accounts[1].Id,
            Amount = 100,
            Ledger = 1,
            Code = 1,
        };

        _ = client.CreateTransfers(new[] { transfer });
        Assert.Fail();
    }


    private static void AssertAccounts(Account[] expected, Account[] actual)
    {
        Assert.AreEqual(expected.Length, actual.Length);
        for (int i = 0; i < actual.Length; i++)
        {
            AssertAccount(actual[i], expected[i]);
        }
    }

    private static void AssertAccount(Account a, Account b)
    {
        Assert.AreEqual(a.Id, b.Id);
        Assert.AreEqual(a.UserData128, b.UserData128);
        Assert.AreEqual(a.UserData64, b.UserData64);
        Assert.AreEqual(a.UserData32, b.UserData32);
        Assert.AreEqual(a.Flags, b.Flags);
        Assert.AreEqual(a.Code, b.Code);
        Assert.AreEqual(a.Ledger, b.Ledger);
    }

    private static void AssertTransfer(Transfer a, Transfer b)
    {
        Assert.AreEqual(a.Id, b.Id);
        Assert.AreEqual(a.DebitAccountId, b.DebitAccountId);
        Assert.AreEqual(a.CreditAccountId, b.CreditAccountId);
        Assert.AreEqual(a.Amount, b.Amount);
        Assert.AreEqual(a.PendingId, b.PendingId);
        Assert.AreEqual(a.UserData128, b.UserData128);
        Assert.AreEqual(a.UserData64, b.UserData64);
        Assert.AreEqual(a.UserData32, b.UserData32);
        Assert.AreEqual(a.Timeout, b.Timeout);
        Assert.AreEqual(a.Flags, b.Flags);
        Assert.AreEqual(a.Code, b.Code);
        Assert.AreEqual(a.Ledger, b.Ledger);
    }

    private static bool AssertException<T>(Exception exception) where T : Exception
    {
        while (exception is AggregateException aggregateException && aggregateException.InnerException != null)
        {
            exception = aggregateException.InnerException;
        }

        return exception is T;
    }
}

internal class TBServer : IDisposable
{
    // Path relative from /TigerBeetle.Test/bin/<framework>/<release>/<platform> :
    private const string PROJECT_ROOT = "../../../../..";
    private const string TB_PATH = PROJECT_ROOT + "/../../../zig-out/bin";
    private const string TB_EXE = "tigerbeetle";
    private const string TB_SERVER = TB_PATH + "/" + TB_EXE;

    private readonly Process process;
    private readonly string dataFile;

    public string Address { get; }

    public TBServer()
    {
        dataFile = Path.GetRandomFileName();

        {
            using var format = new Process();
            format.StartInfo.FileName = TB_SERVER;
            format.StartInfo.Arguments = $"format --cluster=0 --replica=0 --replica-count=1 ./{dataFile}";
            format.StartInfo.RedirectStandardError = true;
            format.Start();
            var formatStderr = format.StandardError.ReadToEnd();
            format.WaitForExit();
            if (format.ExitCode != 0) throw new InvalidOperationException($"format failed, ExitCode={format.ExitCode} stderr:\n{formatStderr}");
        }

        process = new Process();
        process.StartInfo.FileName = TB_SERVER;
        process.StartInfo.Arguments = $"start --addresses=0 --cache-grid=512MB ./{dataFile}";
        process.StartInfo.RedirectStandardInput = true;
        process.StartInfo.RedirectStandardOutput = true;
        process.Start();

        Address = process.StandardOutput.ReadLine()!.Trim();
    }

    public void Dispose()
    {
        process.Kill();
        process.WaitForExit();
        process.Dispose();
        File.Delete($"./{dataFile}");
    }
}
