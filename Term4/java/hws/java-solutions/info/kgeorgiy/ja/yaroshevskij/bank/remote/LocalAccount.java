package info.kgeorgiy.ja.yaroshevskij.bank.remote;

import java.io.Serializable;

public class LocalAccount extends AbstractAccount implements Serializable {
    LocalAccount(AbstractAccount account) {
        super(account.getId(), account.getAmount());
    }
}
