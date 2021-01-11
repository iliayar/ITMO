package expression;

import java.math.BigInteger;

public interface CommonExpression<T extends Number> extends IExpression<T>, ITripleExpression<T> {
    int MOD = 133711;
    int BASE = 31;

    int getPrior();
    boolean isCommutative();
    boolean isIntSafe();

    String getSymbol();

    CommonExpression getFirst();
    CommonExpression getSecond();

}
