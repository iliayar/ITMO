package expression;

public interface Expression extends ToMiniString {

    int evaluate(int x) throws IntegerOverflowException, DivisonByZeroException;
//    String toString();
//    boolean equals(Expression expr);

}
