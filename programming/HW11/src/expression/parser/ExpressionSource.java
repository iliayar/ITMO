package expression.parser;

public interface ExpressionSource {
    boolean hasNext();
    char next();
    ExpressionException error(final String message);
}
