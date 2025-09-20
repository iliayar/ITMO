package ru.akirakozov.sd.mvc.config;

import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import ru.akirakozov.sd.mvc.dao.ProductDao;
import ru.akirakozov.sd.mvc.dao.ProductInMemoryDao;

/**
 * @author akirakozov
 */
@Configuration
public class InMemoryDaoContextConfiguration {
    @Bean
    public ProductDao productDao() {
        return new ProductInMemoryDao();
    }
}
