package expression;

public interface ITripleExpression<T extends Number> extends ToMiniString {
    T evaluate(T x, T y, T z);
}
