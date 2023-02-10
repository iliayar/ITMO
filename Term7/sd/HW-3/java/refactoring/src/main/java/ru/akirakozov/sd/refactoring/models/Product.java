package ru.akirakozov.sd.refactoring.models;


public class Product {

  public Product(String name, long price) {
    this.name = name;
    this.price = price;
  }

  public String getName() {
    return name;
  }

  public long getPrice() {
    return price;
  }

  private String name;
  private long price;
}
