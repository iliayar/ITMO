package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;
import ru.akirakozov.sd.refactoring.templates.Template;

import java.io.IOException;

/**
 * @author akirakozov
 */
public class QueryServlet extends HttpServlet {

  private Database database;
  private Template template;

  public QueryServlet(Database database, Template template) {
    this.database = database;
    this.template = template;
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    String command = request.getParameter("command");

    if ("max".equals(command)) {
      try {
        Product product = database.getMaxPrice();
        response.getWriter().write(template.getMaxPrice(product));
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("min".equals(command)) {
      try {
        Product product = database.getMinPrice();
        response.getWriter().write(template.getMinPrice(product));
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("sum".equals(command)) {
      try {
        long sum = database.getSumPrice();
        response.getWriter().write(template.getSumPrice(sum));
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("count".equals(command)) {
      try {
        int count = database.getProductsCount();
        response.getWriter().write(template.getProductsCount(count));
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else {
      response.getWriter().println("Unknown command: " + command);
    }

    response.setContentType("text/html");
    response.setStatus(HttpServletResponse.SC_OK);
  }

}
