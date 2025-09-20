package ru.akirakozov.sd.refactoring;

import ru.akirakozov.sd.refactoring.database.*;

/**
 * @author akirakozov
 */
public class Main {
  public static void main(String[] args) throws Exception {
    try (SQLite db = new SQLite("test.db")) {
      db.init();
      App app = new App(db);
      app.start();
      app.join();
    }
  }
}
