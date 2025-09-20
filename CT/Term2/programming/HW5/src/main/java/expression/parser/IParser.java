package expression.parser;

import expression.ITripleExpression;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public interface IParser {
    ITripleExpression parse(String expression) throws  ParserException;
}
