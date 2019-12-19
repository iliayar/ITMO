package expression;

public interface CommonExpression extends Expression, TripleExpression {
    final int MOD = 133711;
    final int BASE = 31;

    int getPrior();
    boolean isCommutative();
    boolean isIntSafe();
//    int evaluate(int x, int y, int z);
    long evaluate(long x, long y, long z);

}
