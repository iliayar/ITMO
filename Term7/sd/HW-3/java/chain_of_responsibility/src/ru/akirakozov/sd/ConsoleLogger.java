package ru.akirakozov.sd;

/**
 * Example from:
 * https://www.tutorialspoint.com/design_pattern/chain_of_responsibility_pattern.htm
 */
public class ConsoleLogger extends AbstractLogger {

    public ConsoleLogger(int level){
        this.level = level;
    }

    @Override
    protected void write(String message) {
        System.out.println("Standard Console::Logger: " + message);
    }
}
