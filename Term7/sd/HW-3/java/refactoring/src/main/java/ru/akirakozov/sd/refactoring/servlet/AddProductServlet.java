package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServletRequest;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;

/**
 * @author akirakozov
 */
public class AddProductServlet extends AbstractGetHtmlServlet {

  public AddProductServlet(Database database) {
    super(database);
  }

  @Override
  protected String handle(HttpServletRequest request) throws Exception {
    String name = request.getParameter("name");
    long price = Long.parseLong(request.getParameter("price"));

    database.addProduct(new Product(name, price));
    return template.getOkResponse();
  }
}
