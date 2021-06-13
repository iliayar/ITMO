package info.kgeorgiy.ja.yaroshevskij.bank.test;

import info.kgeorgiy.ja.yaroshevskij.bank.Client;
import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Account;
import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Person;
import org.junit.Test;

import java.rmi.RemoteException;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertNotNull;

public class ClientTest extends AbstractBankTest {

    @Test
    public void dontChangeWithInvalidArguments() throws RemoteException {
        createPerson(0);
        createPerson(1);
        createAccount(0, 0);
        String[][] arguments = {
                {},
                {null, null, null, null, null},
                {FIRST_NAMES[0], SECOND_NAMES[0], null, ACCOUNTS[0], String.valueOf(100)},
                {FIRST_NAMES[0], SECOND_NAMES[1], PASSPORTS[0], ACCOUNTS[0], String.valueOf(100)},
                {FIRST_NAMES[0], SECOND_NAMES[0], PASSPORTS[1], ACCOUNTS[0], String.valueOf(100)},
        };
        for (String[] args : arguments) {
            Client.main(args);
            Account account = getAccount(0, 0);
            assertEquals(account.getAmount(), 0);
        }
    }

    @Test
    public void changeWithValidArguments() throws RemoteException {
        Client.main(FIRST_NAMES[0], SECOND_NAMES[0], PASSPORTS[0], ACCOUNTS[0], String.valueOf(100));
        Person person = getRemotePerson(0);
        Account account = getAccount(0, 0);
        assertNotNull(person);
        assertNotNull(account);
        assertEquals(account.getAmount(), 100);
    }
}
