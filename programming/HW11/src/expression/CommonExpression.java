package expression;

import java.math.BigInteger;

public interface CommonExpression extends Expression, TripleExpression {
    final int MOD = 133711;
    final int BASE = 31;

    int getPrior();
    boolean isCommutative();
    boolean isIntSafe();

    BigInteger evaluate(BigInteger x, BigInteger y, BigInteger z);
}
