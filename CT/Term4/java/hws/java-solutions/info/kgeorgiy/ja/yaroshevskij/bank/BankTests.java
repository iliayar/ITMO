package info.kgeorgiy.ja.yaroshevskij.bank;

import info.kgeorgiy.ja.yaroshevskij.bank.test.BankTest;
import info.kgeorgiy.ja.yaroshevskij.bank.test.ClientTest;
import org.junit.Assert;
import org.junit.internal.TextListener;
import org.junit.runner.JUnitCore;
import org.junit.runner.Result;
import org.junit.runner.notification.Failure;


public class BankTests {

    static final int FAILURE_CODE = 1;

    public static void main(String[] args) {
        JUnitCore junit = new JUnitCore();
        junit.addListener(new TextListener(System.out));
        Result result = junit.run(BankTest.class, ClientTest.class);
        for(Failure failure : result.getFailures()) {
            System.out.println(failure.toString());
        }
        if(!result.wasSuccessful()) {
            System.exit(FAILURE_CODE);
        } else {
            System.exit(0);
        }
    }
}
