package ru.akirakozov.sd.aop.domain;

/**
 * @author akirakozov
 */
public interface CustomerManager {
    int addCustomer(Customer customer);
    Customer findCustomer(int id);
}
