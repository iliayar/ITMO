package expression.exceptions;

import expression.ExpressionException;
import expression.parser.ParserException;

public class MissingOperatorException extends ParserException {
    public MissingOperatorException(String message) {
        super(message);
    }

    @Override
    public String getMessage() {
        return "Operator was stolen" + super.getMessage();
    }
}
