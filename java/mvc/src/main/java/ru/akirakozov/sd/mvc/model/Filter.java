package ru.akirakozov.sd.mvc.model;

/**
 * @author akirakozov
 */
public class Filter {
    private String filter;

    public Filter() {}
    public Filter(String filter) {
        this.filter = filter;
    }

    public String getFilter() {
        return filter;
    }

    public void setFilter(String filter) {
        this.filter = filter;
    }
}
