package expression.parser;

public interface ExpressionSource {
    boolean hasNext();
    char next();
    ParserException error(final String message);
}
