package expression;

import java.math.BigInteger;

public interface Calculator<T extends Number > {

    public T add(T a, T b);

    public T divide(T a, T b);

    public T multiply(T a, T b);

    public T substract(T a, T b);

    public T negate(T a);

    public T parseNumber(String s);

}
