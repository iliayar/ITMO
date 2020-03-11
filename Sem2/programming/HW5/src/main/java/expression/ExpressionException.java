package expression;

public class ExpressionException extends RuntimeException {

    String msg;

    public ExpressionException(String msg) {
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return msg;
    }
}
