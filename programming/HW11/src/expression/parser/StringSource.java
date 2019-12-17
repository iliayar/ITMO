package expression.parser;

public class StringSource implements ExpressionSource {
    private final String src;
    private int index;

    public StringSource(String src) {
        this.src = src;
    }

    @Override
    public boolean hasNext() {
        return src.length() > index;
    }

    @Override
    public char next() {
        if(index >= src.length()) {
            return '\0';
        }
        return src.charAt(index++);
    }

    @Override
    public ExpressionException error(String message) {
        if(index >= src.length()) {
            return  new ExpressionException(message + " but index out of range");
        }
        return new ExpressionException(message + " at " + index + ", which is \'" + src.charAt(index) + "\'");
    }
}
