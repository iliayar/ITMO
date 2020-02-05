package expression;

public class IntegerOverflowException extends Exception {

    private String operation;

    public IntegerOverflowException(String operation) {
        this.operation = operation;
    }

    @Override
    public String getMessage() {
        return "Overflow happens when: " + operation;
    }

}
