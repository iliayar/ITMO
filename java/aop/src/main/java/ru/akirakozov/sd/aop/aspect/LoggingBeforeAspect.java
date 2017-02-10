package ru.akirakozov.sd.aop.aspect;

import org.aspectj.lang.JoinPoint;
import org.aspectj.lang.annotation.Aspect;
import org.aspectj.lang.annotation.Before;

/**
 * @author akirakozov
 */
@Aspect
public class LoggingBeforeAspect {
    @Before("execution(* ru.akirakozov.sd.aop.domain.CustomerManager.addCustomer(..))")
    public void logBefore(JoinPoint joinPoint) {
        System.out.println("logBefore() is running!");
        System.out.println("hijacked : " + joinPoint.getSignature().getName());
        System.out.println("******");
    }
}
