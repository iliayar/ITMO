package expression;

import java.math.BigInteger;

public interface Calculator<T extends Number> {
    public T divide(T a, T b);

    public T add(T a, T b);

    public T negate(T a);

    public T multiply(T a, T b);

    public T subtract(T a, T b);

    public T parseNumber(String s);

    public T valueOf(int n);

    public int compareTo(T n, T a);

    public T count(T a);

    public T min(T a, T b);

    public T max(T a, T b);
}
