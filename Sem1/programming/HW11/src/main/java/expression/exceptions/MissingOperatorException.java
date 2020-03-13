package expression.exceptions;

import expression.ExpressionException;
import expression.parser.ParserException;

public class MissingOperatorException extends ParserException {
    public MissingOperatorException(String message) {
        super(message);
    }
    public MissingOperatorException(ExpressionException e) {
        super(e.getMessage());
    }

    @Override
    public String getMessage() {
        return "Operator was stolen" + super.getMessage();
    }
}
