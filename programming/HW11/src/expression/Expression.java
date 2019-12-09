package expression;

public interface Expression extends ToMiniString {

    public int evaluate(int x);
    public String toString();
    public boolean equals(Expression expr);

}
