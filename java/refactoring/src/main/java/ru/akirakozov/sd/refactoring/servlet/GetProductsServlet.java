package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServlet;
import javax.servlet.http.HttpServletRequest;
import javax.servlet.http.HttpServletResponse;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;
import ru.akirakozov.sd.refactoring.templates.Template;

import java.io.IOException;
import java.util.List;

/**
 * @author akirakozov
 */
public class GetProductsServlet extends HttpServlet {

  private Database database;
  private Template template;

  public GetProductsServlet(Database database, Template template) {
    this.database = database;
    this.template = template;
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    try {
      List<Product> products = database.getProducts();
      response.getWriter().write(template.getListProducts(products));
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    response.setContentType("text/html");
    response.setStatus(HttpServletResponse.SC_OK);
  }
}
