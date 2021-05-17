package info.kgeorgiy.ja.yaroshevskij.bank.interfaces;

import java.rmi.Remote;
import java.rmi.RemoteException;

public interface Bank extends Remote {

    void createPerson(String firstName, String lastName, String id) throws RemoteException;
    void createAccount(String accountId) throws RemoteException;

    Person getRemotePerson(String passport) throws RemoteException;
    Person getLocalPerson(String passport) throws RemoteException;
    Account getAccount(String accountId) throws RemoteException;

}
