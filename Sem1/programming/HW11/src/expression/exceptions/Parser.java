package expression.exceptions;

import expression.ExpressionException;
import expression.TripleExpression;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public interface Parser {
    TripleExpression parse(String expression) throws ExpressionException;
}
