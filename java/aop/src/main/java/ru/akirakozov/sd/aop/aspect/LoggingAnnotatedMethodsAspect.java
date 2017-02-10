package ru.akirakozov.sd.aop.aspect;

import org.aspectj.lang.ProceedingJoinPoint;
import org.aspectj.lang.annotation.Around;
import org.aspectj.lang.annotation.Aspect;

/**
 * @author akirakozov
 */
@Aspect
public class LoggingAnnotatedMethodsAspect {

    @Around("@annotation(ru.akirakozov.sd.aop.aspect.Profile) && execution(* *(..))")
    public Object logExecutionTime(ProceedingJoinPoint joinPoint) throws Throwable {
        long startNs = System.nanoTime();
        System.out.println("Start method " + joinPoint.getSignature().getName());

        Object result = joinPoint.proceed(joinPoint.getArgs());

        System.out.println("Finish method " + joinPoint.getSignature().getName()
                + ", execution time in ns: " + (System.nanoTime() - startNs));

        return result;
    }
}
