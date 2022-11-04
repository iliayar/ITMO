package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;

import java.io.IOException;

/**
 * @author akirakozov
 */
public class QueryServlet extends HttpServlet {

  Database database;

  public QueryServlet(Database database) {
    this.database = database;
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    String command = request.getParameter("command");

    if ("max".equals(command)) {
      try {
        Product product = database.getMaxPrice();
        response.getWriter().println("<html><body>");
        response.getWriter().println("<h1>Product with max price: </h1>");
        response.getWriter().println(product.getName() + "\t" + product.getPrice() + "</br>");
        response.getWriter().println("</body></html>");
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("min".equals(command)) {
      try {
        Product product = database.getMinPrice();
        response.getWriter().println("<html><body>");
        response.getWriter().println("<h1>Product with min price: </h1>");
        response.getWriter().println(product.getName() + "\t" + product.getPrice() + "</br>");
        response.getWriter().println("</body></html>");
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("sum".equals(command)) {
      try {
        long sum = database.getSumPrice();
        response.getWriter().println("<html><body>");
        response.getWriter().println("Summary price: ");
        response.getWriter().println(sum);
        response.getWriter().println("</body></html>");
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    } else if ("count".equals(command)) {
      try {
        int count = database.getProductsCount();
        response.getWriter().println("<html><body>");
        response.getWriter().println("Number of products: ");
        response.getWriter().println(count);
        response.getWriter().println("</body></html>");
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
