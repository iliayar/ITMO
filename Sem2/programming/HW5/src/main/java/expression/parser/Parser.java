package expression.parser;

import expression.ITripleExpression;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public interface Parser {
    ITripleExpression parse(String expression) throws /* Change me */ Exception;
}
