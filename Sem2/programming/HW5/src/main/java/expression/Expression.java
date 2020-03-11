package expression;

public interface Expression extends ToMiniString {

    <T extends Number> T evaluate(T x);
//    String toString();
//    boolean equals(Expression expr);

}
