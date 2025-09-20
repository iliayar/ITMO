package ru.akirakozov.sd.rxjava.reactive_mongo_driver;

import org.bson.Document;

/**
 * @author akirakozov
 */
public class User {
    public final int id;
    public final String name;
    public final String login;


    public User(Document doc) {
        this(doc.getDouble("id").intValue(), doc.getString("name"), doc.getString("login"));
    }

    public User(int id, String name, String login) {
        this.id = id;
        this.name = name;
        this.login = login;
    }

    @Override
    public String toString() {
        return "User{" +
                "id=" + id +
                ", name='" + name + '\'' +
                ", login='" + login + '\'' +
                '}';
    }
}
