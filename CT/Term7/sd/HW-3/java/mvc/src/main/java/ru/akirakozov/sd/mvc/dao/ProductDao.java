package ru.akirakozov.sd.mvc.dao;

import ru.akirakozov.sd.mvc.model.Product;

import java.util.List;
import java.util.Optional;

/**
 * @author akirakozov
 */
public interface ProductDao {
    int addProduct(Product product);

    List<Product> getProducts();

    Optional<Product> getProductWithMaxPrice();
    Optional<Product> getProductWithMinPrice();
}
