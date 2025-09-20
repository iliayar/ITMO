package info.kgeorgiy.ja.yaroshevskij.bank;


import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Account;
import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Bank;
import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Person;

import java.rmi.NotBoundException;
import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;

public final class Client {
    private final static int PORT = 8888;
    private final static String USAGE = "Usage: Client firstName lastName passport account amount";

    public static void main(final String... args) throws RemoteException {
        if (args == null || args.length < 5) {
            System.err.println(USAGE);
            return;
        }
        for (int i = 0; i < 5; ++i) {
            if (args[i] == null) {
                System.err.println(USAGE);
                return;
            }
        }

        try {
            String firstName = args[0];
            String lastName = args[1];
            String passport = args[2];
            String subId = args[3];
            int amountDiff = Integer.parseInt(args[4]);
            int newAmount = new Client().run(PORT, firstName, lastName, passport, subId, amountDiff);
            System.out.println(newAmount);
        } catch (NumberFormatException e) {
            System.err.println(USAGE);
        } catch (RemoteException e) {
            System.err.println("Failed to connect to bank: " + e.getMessage());
        } catch (NotBoundException e) {
            System.err.println("Bank is not available: " + e.getMessage());
        } catch (IllegalArgumentException e) {
            System.err.println(USAGE);
            System.err.println(e.getMessage());
        }
    }

    public int run(int port, String firstName, String lastName, String passport, String subId,
                   int amountDiff) throws RemoteException, NotBoundException {
        Registry registry = LocateRegistry.getRegistry(port);
        final Bank bank = (Bank) registry.lookup("bank");
        String accountId = passport + ":" + subId;
        Person person = bank.getRemotePerson(passport);
        if (person == null) {
            bank.createPerson(firstName, lastName, passport);
            person = bank.getRemotePerson(passport);
        }
        if (!person.getFirstName().equals(firstName)
                || !person.getLastName().equals(lastName)
                || !person.getPassport().equals(passport)) {
            throw new IllegalArgumentException("Invalid person's credentials");
        }
        Account account = person.getAccount(subId);
        if (account == null) {
            bank.createAccount(accountId);
            account = person.getAccount(subId);
        }
        account.addAmount(amountDiff);
        return bank.getAccount(accountId).getAmount();
    }
}
