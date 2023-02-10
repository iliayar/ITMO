package ru.akirakozov.sd.mvc.model;

import java.util.Comparator;

/**
 * @author akirakozov
 */
public class Product {
    public static final PriceComparator PRICE_COMPARATOR = new PriceComparator();
    private int id;
    private String name;
    private int price;

    private static class PriceComparator implements Comparator<Product> {
        public int compare(Product p1, Product p2) {
            return p1.getPrice() - p2.getPrice();
        }
    }

    public Product() {
    }

    public Product(int id, String name, int price) {
        this.id = id;
        this.name = name;
        this.price = price;
    }

    public int getId() {
        return id;
    }

    public void setId(int id) {
        this.id = id;
    }

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getPrice() {
        return price;
    }

    public void setPrice(int price) {
        this.price = price;
    }

}
