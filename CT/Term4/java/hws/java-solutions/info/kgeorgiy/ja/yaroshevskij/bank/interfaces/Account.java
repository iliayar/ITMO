package info.kgeorgiy.ja.yaroshevskij.bank.interfaces;

import java.rmi.Remote;
import java.rmi.RemoteException;

public interface Account extends Remote {

    String getId() throws RemoteException;

    int getAmount() throws RemoteException;

    void setAmount(int amount) throws RemoteException;
    void addAmount(int amount) throws RemoteException;
}
