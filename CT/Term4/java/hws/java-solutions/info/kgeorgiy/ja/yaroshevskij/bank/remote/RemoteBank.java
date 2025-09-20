package info.kgeorgiy.ja.yaroshevskij.bank.remote;

import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.*;

import java.rmi.Remote;
import java.rmi.RemoteException;
import java.rmi.server.UnicastRemoteObject;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class RemoteBank extends UnicastRemoteObject implements Bank {

    private final int port;
    private final Map<String, RemotePerson> persons;
    private final Map<String, RemoteAccount> accounts;

    public RemoteBank(int port) throws RemoteException {
        super();
        this.port = port;
        this.persons = new ConcurrentHashMap<>();
        this.accounts = new ConcurrentHashMap<>();
    }

    @Override
    public Person getRemotePerson(String passport) throws RemoteException {
        return persons.get(passport);
    }

    @Override
    public Person getLocalPerson(String passport) throws RemoteException {
        AbstractPerson person = persons.get(passport);
        if (person == null) {
            return null;
        }
        return new LocalPerson(person);
    }

    @Override
    public void createPerson(String firstName, String lastName, String id) throws RemoteException {
        RemotePerson person = new RemotePerson(firstName, lastName, id);
        UnicastRemoteObject.exportObject(person, port);
        persons.put(id, person);
    }

    @Override
    public void createAccount(String accountId) throws RemoteException {
        String[] passportAndSubIds = accountId.split(":");
        if (passportAndSubIds.length != 2) {
            throw new RemoteException("Invalid bank account Id. Must be <passport>:<subId>");
        }

        String passport = passportAndSubIds[0];
        String subId = passportAndSubIds[1];
        RemoteAccount account = new RemoteAccount(subId);
        RemotePerson person = persons.get(passport);
        if (person == null) {
            throw new RemoteException("Person with related passport doesn't exists");
        }
        UnicastRemoteObject.exportObject(account, port);
        person.addAccount(account);
        accounts.put(accountId, account);
    }

    @Override
    public Account getAccount(String accountId) throws RemoteException {
        return accounts.get(accountId);
    }

}
