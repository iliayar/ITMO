package info.kgeorgiy.ja.yaroshevskij.bank.remote;

import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Account;

import java.rmi.RemoteException;

public class AbstractAccount implements Account {
    private final String id;
    private int amount;

    AbstractAccount(String id, int amount) {
        this.id = id;
        this.amount = amount;
    }

    AbstractAccount(String id) {
        this(id, 0);
    }

    @Override
    public String getId() {
        return id;
    }

    @Override
    public synchronized int getAmount() {
        return amount;
    }

    @Override
    public synchronized void setAmount(int amount) {
        this.amount = amount;
    }

    @Override
    public synchronized void addAmount(int amount) throws RemoteException {
        this.amount += amount;
    }
}
