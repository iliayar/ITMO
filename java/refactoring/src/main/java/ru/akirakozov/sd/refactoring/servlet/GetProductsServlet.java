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
public class GetProductsServlet extends HttpServlet {

  Database database;

  public GetProductsServlet(Database database) {
    this.database = database;
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    try {
      response.getWriter().println("<html><body>");

      for (Product product : database.getProducts()) {
        response.getWriter().println(product.getName() + "\t" + product.getPrice() + "</br>");
      }

      response.getWriter().println("</body></html>");
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    response.setContentType("text/html");
    response.setStatus(HttpServletResponse.SC_OK);
  }
}
