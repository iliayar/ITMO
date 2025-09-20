package info.kgeorgiy.ja.yaroshevskij.bank.test;

import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.*;
import info.kgeorgiy.ja.yaroshevskij.bank.remote.RemoteBank;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;

import java.rmi.NoSuchObjectException;
import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;
import java.rmi.server.UnicastRemoteObject;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.function.Consumer;

public class AbstractBankTest {
    public static final int PORT = 8888;
    protected static final int MAX_PERSONS = 100;
    protected static final int MAX_ACCOUNTS = 200;
    protected static final int SHUTDOWN_TIMEOUT = 5000;

    protected final static String[] FIRST_NAMES = new String[MAX_PERSONS];
    protected final static String[] SECOND_NAMES = new String[MAX_PERSONS];
    protected final static String[] PASSPORTS = new String[MAX_PERSONS];
    protected final static String[] ACCOUNTS = new String[MAX_ACCOUNTS];

    protected static Registry registry;

    protected Bank bank;
    private RemoteBank bankService;

    @BeforeClass
    static public void initPersonsAndAccountsAndCreateRegistry() throws RemoteException {
        for (int i = 0; i < MAX_PERSONS; i++) {
            FIRST_NAMES[i] = "First_" + i;
            SECOND_NAMES[i] = "Second_" + i;
            PASSPORTS[i] = "42" + i;
        }
        for (int i = 0; i < MAX_ACCOUNTS; i++) {
            ACCOUNTS[i] += i + "42";
        }

        try {
            registry = LocateRegistry.createRegistry(PORT);
        } catch (RemoteException e) {
            registry = LocateRegistry.getRegistry(PORT);
        }
    }

    @Before
    public void createBank() {
        try {
            bankService = new RemoteBank(PORT);
            registry.rebind("bank", bankService);
            bank = (Bank) registry.lookup("bank");
        } catch (RemoteException | NotBoundException e) {
            System.err.println("Failed to create bank instance: " + e.getMessage());
        }
    }

    protected void createPerson(int person) throws RemoteException {
        bank.createPerson(FIRST_NAMES[person], SECOND_NAMES[person], PASSPORTS[person]);
    }

    protected void createAccount(int person, int account) throws RemoteException {
        bank.createAccount(getAccountId(person, account));
    }

    protected String getAccountId(int person, int account) {
        return PASSPORTS[person] + ":" + ACCOUNTS[account];
    }

    protected void createMultipleAccounts(int person) throws RemoteException {
        for(int i = 0; i < MAX_ACCOUNTS; i++) {
            createAccount(person, i);
        }
    }

    protected void createMultiplePerson() throws RemoteException {
        for(int i = 0; i < MAX_PERSONS; i++) {
            createPerson(i);
        }
    }

    protected Person getRemotePerson(int person) throws RemoteException {
        return bank.getRemotePerson(PASSPORTS[person]);
    }

    protected Person getLocalPerson(int person) throws RemoteException {
        return bank.getLocalPerson(PASSPORTS[person]);
    }

    protected Account getAccount(int person, int account) throws RemoteException {
        return bank.getAccount(getAccountId(person, account));
    }

    protected void runParallel(int count, Consumer<Integer> callable) {
        ExecutorService pool = Executors.newFixedThreadPool(count);
        for(int i = 0; i < count; i++) {
            int finalI = i;
            pool.submit(() -> callable.accept(finalI));
        }
        pool.shutdown();
        try {
            if (!pool.awaitTermination(SHUTDOWN_TIMEOUT, TimeUnit.MILLISECONDS)) {
                pool.shutdownNow();
            }
        } catch (InterruptedException e) {
            // ignored
        }
    }
}
