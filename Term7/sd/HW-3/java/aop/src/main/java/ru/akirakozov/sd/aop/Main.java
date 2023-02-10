package ru.akirakozov.sd.aop;

import org.springframework.context.ApplicationContext;
import org.springframework.context.annotation.AnnotationConfigApplicationContext;
import ru.akirakozov.sd.aop.domain.Customer;
import ru.akirakozov.sd.aop.domain.CustomerManager;

/**
 * @author akirakozov
 */
public class Main {

    public static void main(String[] args) {
        ApplicationContext ctx =
                new AnnotationConfigApplicationContext(ContextConfiguration.class);

        CustomerManager customerManager = ctx.getBean(CustomerManager.class);
        int id = customerManager.addCustomer(new Customer("Petr"));
        Customer customer = customerManager.findCustomer(id);

        System.out.println("Found customer name: " + customer.name);
    }
}
