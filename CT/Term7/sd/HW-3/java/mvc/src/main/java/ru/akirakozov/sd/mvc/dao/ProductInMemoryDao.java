package ru.akirakozov.sd.mvc.dao;

import ru.akirakozov.sd.mvc.model.Product;

import java.util.List;
import java.util.Optional;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.concurrent.atomic.AtomicInteger;

/**
 * @author akirakozov
 */
public class ProductInMemoryDao implements ProductDao {
    private final AtomicInteger lastId = new AtomicInteger(0);
    private final List<Product> products = new CopyOnWriteArrayList<>();

    public int addProduct(Product product) {
        int id = lastId.incrementAndGet();
        product.setId(id);
        products.add(product);
        return id;
    }

    public List<Product> getProducts() {
        return List.copyOf(products);
    }

    public Optional<Product> getProductWithMaxPrice() {
        return products.stream().max(Product.PRICE_COMPARATOR);
    }

    public Optional<Product> getProductWithMinPrice() {
        return products.stream().min(Product.PRICE_COMPARATOR);
    }
}
