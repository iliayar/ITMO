package expression.exceptions;

import expression.ExpressionException;
import expression.parser.ParserException;

public class MissingBracketException extends ParserException {
    public MissingBracketException(String message) {
        super(message);
    }

    @Override
    public String getMessage() {
        return "Bracket was stolen" + super.getMessage();
    }
}
