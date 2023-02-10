package ru.akirakozov.sd;

/**
 * Example from:
 * https://www.tutorialspoint.com/design_pattern/chain_of_responsibility_pattern.htm
 */
public class ErrorLogger extends AbstractLogger {

    public ErrorLogger(int level){
        this.level = level;
    }

    @Override
    protected void write(String message) {
        System.out.println("Error Console::Logger: " + message);
    }
}
