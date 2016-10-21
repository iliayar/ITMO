package ru.akirakozov.sd.mvc.config;

import org.springframework.context.annotation.Bean;
import org.springframework.jdbc.datasource.DriverManagerDataSource;
import ru.akirakozov.sd.mvc.dao.ProductJdbcDao;

import javax.sql.DataSource;

/**
 * @author akirakozov
 */
public class JdbcDaoContextConfiguration {
    @Bean
    public ProductJdbcDao productJdbcDao(DataSource dataSource) {
        ProductJdbcDao dao = new ProductJdbcDao();
        dao.setDataSource(dataSource);
        return dao;
    }

    @Bean
    public DataSource dataSource() {
        DriverManagerDataSource dataSource = new DriverManagerDataSource();
        dataSource.setDriverClassName("org.sqlite.JDBC");
        dataSource.setUrl("jdbc:sqlite:product.db");
        dataSource.setUsername("");
        dataSource.setPassword("");
        return dataSource;
    }
}
