package ru.akirakozov.sd.rxjava.reactive_mongo_driver;

import com.mongodb.rx.client.MongoClient;
import com.mongodb.rx.client.MongoClients;
import com.mongodb.rx.client.MongoCollection;
import org.bson.Document;
import rx.Observable;

/**
 * @author akirakozov
 */
public class ReactiveMongoDriverExample {

    public static MongoClient client = createMongoClient();

    public static void main(String[] args) throws InterruptedException {
        MongoCollection<Document> collection = client.getDatabase("rxtest").getCollection("user");
        Observable<User> user = getAllUsers(collection);
        user.subscribe(System.out::println);
    }


    public static Observable<User> getAllUsers(MongoCollection<Document> collection) {
        return collection.find().toObservable().map(d -> new User(d));
    }

    private static MongoClient createMongoClient() {
        return MongoClients.create("mongodb://localhost:27017");
    }
}

