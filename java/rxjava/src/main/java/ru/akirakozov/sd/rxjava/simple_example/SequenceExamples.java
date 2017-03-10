package ru.akirakozov.sd.rxjava.simple_example;


import rx.Observable;

/**
 * @author akirakozov
 */
public class SequenceExamples {

    public static void main(String[] args) {
        Observable.
                just("Alexnder", "Mary", "Petr", "Timur", "Pavel", "Piter")
                .filter(s -> s.startsWith("P"))
                .map(s -> s.toUpperCase())
                .take(2)
                .subscribe(System.out::println);
    }
}
