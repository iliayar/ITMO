package info.kgeorgiy.ja.yaroshevskij.bank.test;

import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.*;
import info.kgeorgiy.ja.yaroshevskij.bank.remote.RemoteBank;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;

import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;

import static org.junit.Assert.*;

public class BankTest extends AbstractBankTest {

    @Test
    public void noPersonsCreated() throws RemoteException {
        for (int i = 0; i < MAX_PERSONS; i++) {
            Person person = getRemotePerson(i);
            assertNull(person);
        }
    }

    @Test
    public void singlePersonCreated_RemoteAndLocalNotNull() throws RemoteException {
        createPerson(0);
        Person remotePerson = getRemotePerson(0);
        Person localPerson = getLocalPerson(0);
        assertNotNull(remotePerson);
        assertNotNull(localPerson);
    }

    @Test
    public void singlePersonCreated_NoAccounts() throws RemoteException {
        createPerson(0);
        for (int i = 0; i < MAX_ACCOUNTS; ++i) {
            Account account = getAccount(0, i);
            assertNull(account);
        }
    }

    @Test
    public void singlePersonMultipleAccountCreated_NotNull() throws RemoteException {
        createPerson(0);
        createMultipleAccounts(0);
        for(int i = 0; i < MAX_ACCOUNTS; i++) {
            Account account = getAccount(0, i);
            assertNotNull(account);
        }
    }

    @Test
    public void multiplePersonsMultipleAccountsCreated_NotNull() throws RemoteException {
        createMultiplePerson();
        for(int i = 0; i < MAX_PERSONS; i++){
            createMultipleAccounts(i);
        }
        for(int i = 0; i < MAX_PERSONS; i++){
            for(int j = 0; j < MAX_ACCOUNTS; j++) {
                Account account = getAccount(i, j);
                assertNotNull(account);
            }
        }
    }

    @Test
    public void multiplePersonsMultipleAccounts_hasDifferentAmount() throws RemoteException {
        createMultiplePerson();
        for(int i = 0; i < MAX_PERSONS; i++) {
            createMultipleAccounts(i);
            for(int j = 0; j < MAX_ACCOUNTS; j++) {
                Account account = getAccount(i, j);
                account.setAmount(i * j);
            }
        }
        for(int i = 0; i < MAX_PERSONS; i++) {
            for(int j = 0; j < MAX_ACCOUNTS; j++) {
                Account account = getAccount(i, j);
                assertEquals(account.getAmount(), i * j);
            }
        }
    }

    @Test
    public void localPersonDontChangeRemote() throws RemoteException {
        createPerson(0);
        createAccount(0, 0);
        Person localPerson = getLocalPerson(0);
        Person remotePerson = getRemotePerson(0);
        Account localAccount = localPerson.getAccount(ACCOUNTS[0]);
        localAccount.setAmount(100);
        Account remoteAccount = remotePerson.getAccount(ACCOUNTS[0]);
        assertEquals(remoteAccount.getAmount(), 0);
    }

    @Test
    public void remotePersonDontChangeLocalPerson() throws RemoteException {
        createPerson(0);
        createAccount(0, 0);
        Person localPerson = getLocalPerson(0);
        Person remotePerson = getRemotePerson(0);
        Account remoteAccount = remotePerson.getAccount(ACCOUNTS[0]);
        remoteAccount.setAmount(100);
        Account localAccount = localPerson.getAccount(ACCOUNTS[0]);
        assertEquals(localAccount.getAmount(), 0);
    }

    @Test
    public void addingAccountDontChangeLocalAndChangeRemote() throws RemoteException {
        createPerson(0);
        createAccount(0, 0);
        Person localPerson = getLocalPerson(0);
        Person remotePerson = getRemotePerson(0);
        createAccount(0, 1);
        Account localAccount1 = localPerson.getAccount(ACCOUNTS[0]);
        Account localAccount2 = localPerson.getAccount(ACCOUNTS[1]);
        Account remoteAccount1 = remotePerson.getAccount(ACCOUNTS[0]);
        Account remoteAccount2 = remotePerson.getAccount(ACCOUNTS[1]);
        assertNotNull(localAccount1);
        assertNull(localAccount2);
        assertNotNull(remoteAccount1);
        assertNotNull(remoteAccount2);
    }

    @Test
    public void parallelAddingAmount() throws RemoteException {
        createPerson(0);
        createAccount(0, 0);
        runParallel(20, i -> {
            try {
                Account account = getAccount(0, 0);
                account.addAmount(1);
            } catch (RemoteException e) {
                // ignored
            }
        });
        Account account = getAccount(0, 0);
        assertEquals(account.getAmount(), 20);
    }

    @Test
    public void parallelCreatingMultipleAccounts() throws RemoteException {
        createPerson(0);
        runParallel(20, i -> {
            try {
                createAccount(0, i);
            } catch (RemoteException e) {
                // ignored
            }
        });
        for(int i = 0; i < 20; i++) {
            Account account = getAccount(0, i);
            assertNotNull(account);
        }
    }
}
