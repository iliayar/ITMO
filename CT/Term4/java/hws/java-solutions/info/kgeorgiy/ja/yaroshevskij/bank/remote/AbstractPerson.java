package info.kgeorgiy.ja.yaroshevskij.bank.remote;

import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Account;
import info.kgeorgiy.ja.yaroshevskij.bank.interfaces.Person;

import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

public class AbstractPerson implements Person {

    private final Map<String, AbstractAccount> accounts;
    private final String firstName;
    private final String lastName;
    private final String passport;

    AbstractPerson(String firstName, String lastName, String passport, Collection<AbstractAccount> accounts) {
        this.firstName = firstName;
        this.lastName = lastName;
        this.passport = passport;
        this.accounts = new ConcurrentHashMap<>();
        for (AbstractAccount account : accounts) {
            this.accounts.put(account.getId(), account);
        }

    }

    AbstractPerson(String firstName, String lastName, String passport) {
        this(firstName, lastName, passport, List.of());
    }

    @Override
    public String getFirstName() {
        return firstName;
    }

    @Override
    public String getLastName() {
        return lastName;
    }

    @Override
    public String getPassport() {
        return passport;
    }

    @Override
    public Account getAccount(String id) {
        return accounts.get(id);
    }

    public void addAccount(AbstractAccount account) {
        accounts.put(account.getId(), account);
    }

    public Collection<AbstractAccount> getAccounts() {
        return accounts.values();
    }
}
