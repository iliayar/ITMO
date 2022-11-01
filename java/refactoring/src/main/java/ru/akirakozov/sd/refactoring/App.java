package ru.akirakozov.sd.refactoring;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;
import ru.akirakozov.sd.refactoring.servlet.AddProductServlet;
import ru.akirakozov.sd.refactoring.servlet.GetProductsServlet;
import ru.akirakozov.sd.refactoring.servlet.QueryServlet;

import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.Statement;

public class App {

  private static final int DEFAULT_PORT = 8081;

  private int port;
  private Server server;

  public App(int port) {
    this.port = port;
  }

  public App() {
    this(DEFAULT_PORT);
  }

  public void Start() throws Exception {
    try (Connection c = DriverManager.getConnection("jdbc:sqlite:test.db")) {
      String sql = "CREATE TABLE IF NOT EXISTS PRODUCT" + "(ID INTEGER PRIMARY KEY AUTOINCREMENT NOT NULL,"
          + " NAME           TEXT    NOT NULL, " + " PRICE          INT     NOT NULL)";
      Statement stmt = c.createStatement();

      stmt.executeUpdate(sql);
      stmt.close();
    }

    server = new Server(port);

    ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
    context.setContextPath("/");
    server.setHandler(context);

    context.addServlet(new ServletHolder(new AddProductServlet()), "/add-product");
    context.addServlet(new ServletHolder(new GetProductsServlet()), "/get-products");
    context.addServlet(new ServletHolder(new QueryServlet()), "/query");

    server.start();
  }

  public void Stop() throws Exception {
    if (server == null) {
      throw new Exception("Server is not running");
    }

    server.stop();
  }

  public void Wait() throws Exception {
    if (server == null) {
      throw new Exception("Server is not running");
    }

    server.join();
  }

}
