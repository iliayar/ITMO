package ru.akirakozov.sd.aop;

import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.context.annotation.EnableAspectJAutoProxy;
import ru.akirakozov.sd.aop.aspect.LoggingAnnotatedMethodsAspect;
import ru.akirakozov.sd.aop.aspect.LoggingExceptionAspect;
import ru.akirakozov.sd.aop.aspect.LoggingExecutionTimeAspect;
import ru.akirakozov.sd.aop.dao.CustomerInMemoryDao;
import ru.akirakozov.sd.aop.domain.CustomerManager;
import ru.akirakozov.sd.aop.domain.CustomerManagerImpl;

/**
 * @author akirakozov
 */
@Configuration
@EnableAspectJAutoProxy
public class ContextConfiguration {
    @Bean
    public CustomerManager customerManager() {
        return new CustomerManagerImpl(new CustomerInMemoryDao());
    }

    @Bean
    public LoggingExecutionTimeAspect aspect() {
        return new LoggingExecutionTimeAspect();
    }
}
