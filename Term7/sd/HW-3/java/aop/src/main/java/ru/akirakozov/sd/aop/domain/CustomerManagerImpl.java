package ru.akirakozov.sd.aop.domain;

import ru.akirakozov.sd.aop.aspect.Profile;
import ru.akirakozov.sd.aop.dao.CustomerInMemoryDao;

/**
 * @author akirakozov
 */
public class CustomerManagerImpl implements CustomerManager {
    CustomerInMemoryDao customerDao = new CustomerInMemoryDao();

    public CustomerManagerImpl(CustomerInMemoryDao customerDao) {
        this.customerDao = customerDao;
    }

    @Profile
    public int addCustomer(Customer customer) {
        return customerDao.addCustomer(customer);
    }

    @Profile
    public Customer findCustomer(int id) {
        return customerDao.findCustomer(id);
    }
}
