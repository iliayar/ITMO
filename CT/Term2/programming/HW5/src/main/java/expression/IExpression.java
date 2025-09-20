package expression;

public interface IExpression<T extends Number> extends ToMiniString {

    T evaluate(T x);
//    String toString();
//    boolean equals(Expression expr);

}
