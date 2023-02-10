package ru.akirakozov.sd;

/**
 * Example from:
 * https://www.tutorialspoint.com/design_pattern/chain_of_responsibility_pattern.htm
 */
public class FileLogger extends AbstractLogger {

    public FileLogger(int level){
        this.level = level;
    }

    @Override
    protected void write(String message) {
        System.out.println("File::Logger: " + message);
    }
}
