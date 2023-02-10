package ru.akirakozov.sd.refactoring.templates;

import java.util.List;

import ru.akirakozov.sd.refactoring.models.Product;

public interface Template {

  String getOkResponse();

  String getListProducts(List<Product> products);

  String getMaxPrice(Product product);
  String getMinPrice(Product product);
  String getSumPrice(long sum);
  String getProductsCount(int count);

  String unknownCommand(String command);

}
