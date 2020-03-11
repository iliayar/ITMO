package expression;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public interface TripleExpression extends ToMiniString {
    Number evaluate(Number x, Number y, Number z);
}
