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
public class AddProductServlet extends HttpServlet {

  private Database database;
  private Template template;

  public AddProductServlet(Database database, Template template) {
    this.database = database;
    this.template = template;
  }

  @Override
  protected void doGet(HttpServletRequest request, HttpServletResponse response) throws IOException {
    String name = request.getParameter("name");
    long price = Long.parseLong(request.getParameter("price"));

    try {
      database.addProduct(new Product(name, price));
      response.getWriter().write(template.getOkResponse());
    } catch (Exception e) {
      throw new RuntimeException(e);
    }

    response.setContentType("text/html");
    response.setStatus(HttpServletResponse.SC_OK);
  }
}
