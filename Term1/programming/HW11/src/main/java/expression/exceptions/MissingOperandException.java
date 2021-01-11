package expression.exceptions;

import expression.ExpressionException;
import expression.parser.ParserException;

public class MissingOperandException extends ParserException {
    public MissingOperandException(String message) {
        super(message);
    }
    public MissingOperandException(ExpressionException e) {
        super(e.getMessage());
    }

    @Override
    public String getMessage() {
        return "Operand was stolen" + super.getMessage();
    }
}
