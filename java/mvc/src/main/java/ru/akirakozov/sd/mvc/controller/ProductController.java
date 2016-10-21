package ru.akirakozov.sd.mvc.controller;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Controller;
import org.springframework.ui.ModelMap;
import org.springframework.web.bind.annotation.ModelAttribute;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RequestMethod;
import org.springframework.web.bind.annotation.RequestParam;
import ru.akirakozov.sd.mvc.dao.ProductDao;
import ru.akirakozov.sd.mvc.model.Filter;
import ru.akirakozov.sd.mvc.model.Product;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Optional;

/**
 * @author akirakozov
 */
@Controller
public class ProductController {
    @Autowired
    private ProductDao productDao;

    @RequestMapping(value = "/add-product", method = RequestMethod.POST)
    public String addQuestion(@ModelAttribute("product") Product product) {
        productDao.addProduct(product);
        return "redirect:/get-products";
    }

    @RequestMapping(value = "/get-products", method = RequestMethod.GET)
    public String getProducts(ModelMap map) {
        prepareModelMap(map, productDao.getProducts());
        return "index";
    }

    @RequestMapping(value = "/filter-products", method = RequestMethod.GET)
    public String getProducts(@RequestParam String filter, ModelMap map) {
        if ("all".equals(filter)) {
            prepareModelMap(map, productDao.getProducts());
        } else {
            Optional<Product> product = Optional.empty();
            if ("max".equals(filter)) {
                product = productDao.getProductWithMaxPrice();
            } else if ("min".equals(filter)) {
                product = productDao.getProductWithMinPrice();
            }
            if (product.isPresent()) {
                prepareModelMap(map, Arrays.asList(product.get()));
            } else {
                prepareModelMap(map, new ArrayList<Product>());
            }
        }

        return "index";
    }

    private void prepareModelMap(ModelMap map, List<Product> products) {
        map.addAttribute("products", products);
        map.addAttribute("product", new Product());
        map.addAttribute("filter", new Filter());
    }
}
