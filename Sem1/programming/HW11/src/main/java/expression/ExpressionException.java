package expression;

public class ExpressionException extends RuntimeException {
	private static final long serialVersionUID = 1L;
	String msg;

    public ExpressionException(String msg) {
        this.msg = msg;
    }

    @Override
    public String getMessage() {
        return msg;
    }
}
