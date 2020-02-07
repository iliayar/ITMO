package expression.parser;

public class StringSource implements ExpressionSource {
    private final String src;
    private int index;

    public StringSource(String src) {
        this.src = src;
    }

    @Override
    public boolean hasNext() {
//        System.err.println("hasNext " + src.charAt(index));
        return src.length() > index;
    }

    @Override
    public char next() {
        if(index >= src.length()) {
            return '\0';
        }
//        System.err.println("Next char after " + src.charAt(index));
        return src.charAt(index++);
    }


    @Override
    public ParserException error(String message) {
        if(index-1 >= src.length()) {
            return  new ParserException(message + " and end of string reached");
        }
        return new ParserException(message + " at " + (index-1) + ", which is \'" + src.charAt(index-1) + "\'");
    }
}
