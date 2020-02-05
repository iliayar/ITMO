package expression;

import java.math.BigInteger;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public interface TripleExpression extends ToMiniString {
    int evaluate(int x, int y, int z);
//    long evaluate(long x, long y, long z);

}
