package ru.akirakozov.sd.refactoring;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.servlet.AddProductServlet;
import ru.akirakozov.sd.refactoring.servlet.GetProductsServlet;
import ru.akirakozov.sd.refactoring.servlet.QueryServlet;

public class App {

  private static final int DEFAULT_PORT = 8081;

  private int port;
  private Server server;

  private Database database;

  public App(Database database, int port) {
    this.port = port;
    this.database = database;
  }

  public App(Database database) {
    this(database, DEFAULT_PORT);
  }

  public void start() throws Exception {
    database.init();
    
    server = new Server(port);

    ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
    context.setContextPath("/");
    server.setHandler(context);

    context.addServlet(new ServletHolder(new AddProductServlet(database)), "/add-product");
    context.addServlet(new ServletHolder(new GetProductsServlet(database)), "/get-products");
    context.addServlet(new ServletHolder(new QueryServlet(database)), "/query");

    server.start();
  }

  public void stop() throws Exception {
    if (server == null) {
      throw new Exception("Server is not running");
    }

    server.stop();
  }

  public void join() throws Exception {
    if (server == null) {
      throw new Exception("Server is not running");
    }

    server.join();
  }

}
