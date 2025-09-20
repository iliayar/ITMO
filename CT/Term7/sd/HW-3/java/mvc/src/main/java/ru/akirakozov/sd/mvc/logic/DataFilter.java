package ru.akirakozov.sd.mvc.logic;

import ru.akirakozov.sd.mvc.dao.ProductDao;
import ru.akirakozov.sd.mvc.model.Product;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * @author akirakozov
 */
public abstract class DataFilter {
    private static Map<String, DataFilter> filters = createFiltersMap();

    private static HashMap<String, DataFilter> createFiltersMap() {
        HashMap<String, DataFilter> filters = new HashMap<>();
        filters.put("all", new AllFilter());
        filters.put("max", new MaxFilter());
        filters.put("min", new MinFilter());
        return filters;
    }

    public abstract List<Product> filter(ProductDao productDao);

    private static class AllFilter extends DataFilter {
        public List<Product> filter(ProductDao productDao) {
            return productDao.getProducts();
        }
    };

    private static class MaxFilter extends DataFilter {
        public List<Product> filter(ProductDao productDao) {
            return productDao.getProductWithMaxPrice()
                    .map(List::of)
                    .orElse(List.of());
        }
    };

    private static class MinFilter extends DataFilter {
        public List<Product> filter(ProductDao productDao) {
            return productDao.getProductWithMinPrice()
                    .map(List::of)
                    .orElse(List.of());
        }
    };

    public static Optional<DataFilter> getFilterByName(String name) {
        return Optional.ofNullable(filters.get(name));
    }
}
