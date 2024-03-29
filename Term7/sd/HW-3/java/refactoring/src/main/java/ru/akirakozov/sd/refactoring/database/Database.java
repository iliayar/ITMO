package ru.akirakozov.sd.refactoring.database;

import java.util.List;

import ru.akirakozov.sd.refactoring.models.Product;

public interface Database {

  void init() throws Exception;

  void addProduct(Product product) throws Exception;

  List<Product> getProducts() throws Exception;

  int getProductsCount() throws Exception;

  long getSumPrice() throws Exception;
  
  Product getMinPrice() throws Exception;

  Product getMaxPrice() throws Exception;

}
