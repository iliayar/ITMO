package ru.akirakozov.sd.refactoring.database;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import ru.akirakozov.sd.refactoring.models.Product;

public class SQLite implements Database, AutoCloseable {

  private String sqlCreateTable;
  private String sqlAddProduct;
  private String sqlGetProducts;

  private String sqlGetProductsCount;
  private String sqlGetSumPrice;
  private String sqlGetMaxPrice;
  private String sqlGetMinPrice;

  private Connection connection;

  public SQLite(String filename) throws Exception {
    this.connection = DriverManager.getConnection("jdbc:sqlite:" + filename);

    sqlCreateTable = loadSQLScript("create_table");
    sqlAddProduct = loadSQLScript("add_product");
    sqlGetProducts = loadSQLScript("get_products");

    sqlGetProductsCount = loadSQLScript("get_products_count");
    sqlGetSumPrice = loadSQLScript("get_sum_price");
    sqlGetMaxPrice = loadSQLScript("get_max_price");
    sqlGetMinPrice = loadSQLScript("get_min_price");
  }

  @Override
  public void addProduct(Product product) throws Exception {
    try (PreparedStatement stmt = connection.prepareStatement(sqlAddProduct)) {
      stmt.setString(1, product.getName());
      stmt.setLong(2, product.getPrice());
      stmt.executeUpdate();
    }
  }

  @Override
  public List<Product> getProducts() throws Exception {
    return withExecutingQuery(sqlGetProducts, result -> {
      List<Product> res = new ArrayList<>();

      while (result.next()) {
        res.add(getProductFromResult(result));
      }

      return res;
    });
  }

  @Override
  public int getProductsCount() throws Exception {
    return withExecutingQuerySingleRow(sqlGetProductsCount, result -> {
      return Integer.valueOf(result.getInt(1));
    }).intValue();
  }

  @Override
  public long getSumPrice() throws Exception {
    return withExecutingQuerySingleRow(sqlGetSumPrice, result -> {
      return Long.valueOf(result.getLong(1));
    }).longValue();
  }

  @Override
  public Product getMinPrice() throws Exception {
    return withExecutingQuerySingleRow(sqlGetMinPrice, result -> {
      return getProductFromResult(result);
    });
  }

  @Override
  public Product getMaxPrice() throws Exception {
    return withExecutingQuerySingleRow(sqlGetMaxPrice, result -> {
      return getProductFromResult(result);
    });
  }

  @Override
  public void init() throws Exception {
    try (Statement stmt = connection.createStatement()) {
      stmt.executeUpdate(sqlCreateTable);
    }
  }

  @Override
  public void close() throws Exception {
    connection.close();
  }

  private String loadSQLScript(String filename) {
    ClassLoader classLoader = getClass().getClassLoader();
    InputStream inputStream = classLoader.getResourceAsStream("sql/" + filename + ".sql");
    BufferedReader input = new BufferedReader(new InputStreamReader(inputStream));

    String script = input.lines().collect(Collectors.joining("\n"));
    return script;
  }

  private Product getProductFromResult(ResultSet result) throws Exception {
    String name = result.getString("Name");
    long price = result.getLong("Price");
    return new Product(name, price);
  }

  private<R> R withExecutingQuery(String query, CheckedFunction<ResultSet, R> fun) throws Exception {
    try (Statement stmt = connection.createStatement()) {
      try (ResultSet result = stmt.executeQuery(query)) {
          return fun.apply(result);
      }
    }
  }

  private <R> R withExecutingQuerySingleRow(String query, CheckedFunction<ResultSet, R> fun) throws Exception {
    return withExecutingQuery(query, result -> {
      if (result.next()) {
        return fun.apply(result);
      }
      throw new RuntimeException("No rows in result");
    });
  }

  @FunctionalInterface
  private interface CheckedFunction<T, R> {
    R apply(T t) throws Exception;
  }

}
