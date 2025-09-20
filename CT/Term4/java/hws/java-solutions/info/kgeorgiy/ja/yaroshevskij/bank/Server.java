package info.kgeorgiy.ja.yaroshevskij.bank;


import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Bank;
import info.kgeorgiy.ja.yaroshevskij.bank.remote.RemoteBank;

import java.rmi.RemoteException;
import java.rmi.registry.LocateRegistry;
import java.rmi.registry.Registry;

public final class Server {
    private final static int DEFAULT_PORT = 8888;

    public static void main(final String... args) {
        final int port = args.length > 0 ? Integer.parseInt(args[0]) : DEFAULT_PORT;
        try {
            new Server().run(port);
            System.out.println("Server started");
        } catch (final RemoteException e) {
            System.err.println("Cannot export object: " + e.getMessage());
            e.printStackTrace();
            System.exit(1);
        }
    }

    public Bank run(int port) throws RemoteException {
        Registry registry = LocateRegistry.createRegistry(port);
        final Bank bank = new RemoteBank(port);
        registry.rebind("bank", bank);
        return bank;
    }
}
