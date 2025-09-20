package info.kgeorgiy.ja.yaroshevskij.bank.remote;

import java.io.Serializable;
import java.util.stream.Collectors;

public class LocalPerson extends AbstractPerson implements Serializable {
    LocalPerson(AbstractPerson person) {
        super(person.getFirstName(), person.getLastName(), person.getPassport(),
                person.getAccounts().stream().map(LocalAccount::new).collect(Collectors.toList()));
    }
}
