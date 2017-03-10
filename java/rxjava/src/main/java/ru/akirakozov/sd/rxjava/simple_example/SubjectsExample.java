package ru.akirakozov.sd.rxjava.simple_example;

import rx.Subscription;
import rx.subjects.PublishSubject;
import rx.subjects.ReplaySubject;
import rx.subjects.Subject;

/**
 * @author akirakozov
 */
public class SubjectsExample {

    public static void main(String[] args) {
        //publishSubject();
        //replaySubject();
        //limitedReplaySubjects();
        unsubscribeExample();
    }

    private static void unsubscribeExample() {
        Subject<Integer, Integer> values = ReplaySubject.create();
        Subscription subscription = values.subscribe(
                v -> System.out.println(v),
                e -> System.err.println(e),
                () -> System.out.println("Done")
        );
        values.onNext(0);
        values.onNext(1);
        subscription.unsubscribe();
        values.onNext(2);
    }

    private static void limitedReplaySubjects() {
        ReplaySubject<Integer> s = ReplaySubject.createWithSize(2);
        s.onNext(0);
        s.onNext(1);
        s.onNext(2);
        s.subscribe(v -> System.out.println("Late: " + v));
        s.onNext(3);
    }

    private static void publishSubject() {
        PublishSubject<Integer> subject = PublishSubject.create();
        subject.onNext(1);
        subject.subscribe(System.out::println);
        subject.onNext(2);
        subject.onNext(3);
        subject.onNext(4);
    }

    private static void replaySubject() {
        ReplaySubject<Integer> s = ReplaySubject.create();
        s.subscribe(v -> System.out.println("Early:" + v));
        s.onNext(0);
        s.onNext(1);
        s.subscribe(v -> System.out.println("Late: " + v));
        s.onNext(2);
    }

}
