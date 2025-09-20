package ru.akirakozov.sd.refactoring;

import org.eclipse.jetty.server.Server;
import org.eclipse.jetty.servlet.ServletContextHandler;
import org.eclipse.jetty.servlet.ServletHolder;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.servlet.AbstractGetHtmlServlet;
import ru.akirakozov.sd.refactoring.servlet.AddProductServlet;
import ru.akirakozov.sd.refactoring.servlet.GetProductsServlet;
import ru.akirakozov.sd.refactoring.servlet.QueryServlet;
import ru.akirakozov.sd.refactoring.templates.HTMLTemplate;
import ru.akirakozov.sd.refactoring.templates.Template;

public class App {

  private static final int DEFAULT_PORT = 8081;

  private Server server;
  private Database database;

  public App(Database database, int port) throws Exception {
    this.database = database;

    init(port);
  }

  public App(Database database) throws Exception {
    this(database, DEFAULT_PORT);
  }

  public void start() throws Exception {
    server.start();
  }

  public void stop() throws Exception {
    server.stop();
  }

  public void join() throws Exception {
    server.join();
  }

  private void init(int port) throws Exception {
    database.init();

    server = new Server(port);

    ServletContextHandler context = new ServletContextHandler(ServletContextHandler.SESSIONS);
    context.setContextPath("/");
    server.setHandler(context);

    addServlet(context, new AddProductServlet(database), "/add-product");
    addServlet(context, new GetProductsServlet(database), "/get-products");
    addServlet(context, new QueryServlet(database), "/query");
  }

  private void addServlet(ServletContextHandler context, AbstractGetHtmlServlet servlet, String path) {
    context.addServlet(new ServletHolder(servlet), path);
  }

}
