package ru.akirakozov.sd;

/**
 * Example from:
 * https://www.tutorialspoint.com/design_pattern/observer_pattern.htm
 */
public class ObserverPatternDemo {
    public static void main(String[] args) {
        Subject subject = new Subject();

        new Observer.HexaObserver(subject);
        new Observer.OctalObserver(subject);
        new Observer.BinaryObserver(subject);

        System.out.println("First state change: 15");
        subject.setState(15);
        System.out.println("Second state change: 10");
        subject.setState(10);
    }
}
