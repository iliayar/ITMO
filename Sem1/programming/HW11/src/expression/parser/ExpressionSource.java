package expression.parser;

public interface ExpressionSource {
    boolean hasNext();
    char next();
    String error(final String message);
}
