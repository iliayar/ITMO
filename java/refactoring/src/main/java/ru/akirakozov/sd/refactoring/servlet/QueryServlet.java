package ru.akirakozov.sd.refactoring.servlet;

import javax.servlet.http.HttpServletRequest;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;


/**
 * @author akirakozov
 */
public class QueryServlet extends AbstractGetHtmlServlet {

  public QueryServlet(Database database) {
    super(database);
  }

  @Override
  protected String handle(HttpServletRequest request) throws Exception {
    String command = request.getParameter("command");

    if ("max".equals(command)) {
      Product product = database.getMaxPrice();
      return template.getMaxPrice(product);
    } else if ("min".equals(command)) {
      Product product = database.getMinPrice();
      return template.getMinPrice(product);
    } else if ("sum".equals(command)) {
      long sum = database.getSumPrice();
      return template.getSumPrice(sum);
    } else if ("count".equals(command)) {
      int count = database.getProductsCount();
      return template.getProductsCount(count);
    } else {
      return template.unknownCommand(command);
    }
  }
}
