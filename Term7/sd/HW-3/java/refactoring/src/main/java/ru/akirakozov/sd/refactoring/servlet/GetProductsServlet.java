package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServletRequest;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;

import java.util.List;

/**
 * @author akirakozov
 */
public class GetProductsServlet extends AbstractGetHtmlServlet {

  public GetProductsServlet(Database database) {
    super(database);
  }

  @Override
  protected String handle(HttpServletRequest request) throws Exception {
    List<Product> products = database.getProducts();
    return template.getListProducts(products);
  }
}
