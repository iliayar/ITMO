package ru.akirakozov.sd.refactoring.templates;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import ru.akirakozov.sd.refactoring.Utils;
import ru.akirakozov.sd.refactoring.models.Product;

public class HTMLTemplate implements Template {

  private final String htmlOkResponse;

  private final String htmlGetProduct;
  private final String htmlGetProductItem;

  private final String htmlMaxPrice;
  private final String htmlMinPrice;
  private final String htmlSumPrice;
  private final String htmlProductsCount;

  public HTMLTemplate() {

    htmlOkResponse = loadHTMLTemplate("ok");

    htmlGetProduct = loadHTMLTemplate("get_product");
    htmlGetProductItem = loadHTMLTemplate("get_product_item");

    htmlMaxPrice = loadHTMLTemplate("max_price");
    htmlMinPrice = loadHTMLTemplate("min_price");
    htmlSumPrice = loadHTMLTemplate("sum_price");
    htmlProductsCount = loadHTMLTemplate("products_count");
  }

  @Override
  public String getOkResponse() {
    return htmlOkResponse;
  }

  @Override
  public String getListProducts(List<Product> products) {
    StringBuilder items = new StringBuilder();

    for (Product product : products) {
      items.append(formatProduct(htmlGetProductItem, product));
    }

    ResponseBuilder builder = new ResponseBuilder(htmlGetProduct);
    builder.param("items", items.toString());
    return builder.getResponse();
  }

  @Override
  public String getMaxPrice(Product product) {
    return formatProduct(htmlMaxPrice, product);
  }

  @Override
  public String getMinPrice(Product product) {
    return formatProduct(htmlMinPrice, product);
  }

  @Override
  public String getSumPrice(long sum) {
    ResponseBuilder builder = new ResponseBuilder(htmlSumPrice);
    builder.param("sum", String.valueOf(sum));
    return builder.getResponse();
  }

  @Override
  public String getProductsCount(int count) {
    ResponseBuilder builder = new ResponseBuilder(htmlProductsCount);
    builder.param("count", String.valueOf(count));
    return builder.getResponse();
  }

  private String loadHTMLTemplate(String filename) {
    ClassLoader classLoader = getClass().getClassLoader();
    return Utils.getResource(classLoader, "html/" + filename + ".html");
  }

  private String formatProduct(String template, Product product) {
    ResponseBuilder builder = new ResponseBuilder(template);
    builder.param("name", product.getName());
    builder.param("price", String.valueOf(product.getPrice()));
    return builder.getResponse();
  }

  private static class ResponseBuilder {
    private String response;

    public ResponseBuilder(String template) {
      this.response = template;
    }

    public void param(String key, String value) {
      response = response.replace("{" + key + "}", value);
    }

    public String getResponse() {
      return response;
    }
  }

}
