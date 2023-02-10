package ru.akirakozov.sd.aop.dao;

/**
 * @author akirakozov
 */
public class EntityNotFoundException extends RuntimeException {
    public EntityNotFoundException(String message) {
        super(message);
    }
}
