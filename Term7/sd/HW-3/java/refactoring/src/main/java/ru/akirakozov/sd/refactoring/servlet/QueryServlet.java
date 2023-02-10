package ru.akirakozov.sd.refactoring.servlet;

import java.util.HashMap;
import java.util.Map;

import javax.servlet.http.HttpServletRequest;

import ru.akirakozov.sd.refactoring.database.Database;
import ru.akirakozov.sd.refactoring.models.Product;


/**
 * @author akirakozov
 */
public class QueryServlet extends AbstractGetHtmlServlet {

  Map<String, CommandHandler> handlers;

  public QueryServlet(Database database) {
    super(database);

    handlers = new HashMap<>();
    handlers.put("max", new MaxHandler());
    handlers.put("min", new MinHandler());
    handlers.put("sum", new SumHandler());
    handlers.put("count", new CountHandler());
  }

  @Override
  protected String handle(HttpServletRequest request) throws Exception {
    String command = request.getParameter("command");

    if (handlers.containsKey(command)) {
      return handlers.get(command).handle();
    }

    return template.unknownCommand(command);
  }

  private interface CommandHandler {
    String handle() throws Exception;
  }

  private class MaxHandler implements CommandHandler {
    @Override
    public String handle() throws Exception {
      Product product = database.getMaxPrice();
      return template.getMaxPrice(product);
    }
  }

  private class MinHandler implements CommandHandler {
    @Override
    public String handle() throws Exception {
      Product product = database.getMinPrice();
      return template.getMinPrice(product);
    }
  }

  private class SumHandler implements CommandHandler {
    @Override
    public String handle() throws Exception {
      long sum = database.getSumPrice();
      return template.getSumPrice(sum);
    }
  }

  private class CountHandler implements CommandHandler {
    @Override
    public String handle() throws Exception {
      int count = database.getProductsCount();
      return template.getProductsCount(count);
    }
  }
}
