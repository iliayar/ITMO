package expression.parser;

import expression.TripleExpression;

public abstract class BaseParser implements expression.exceptions.Parser {
    protected ExpressionSource src;
    protected char ch;

//    public BaseParser(ExpressionSource src) {
//        this.src = src;
//    }

    protected void nextChar() {
        ch = src.hasNext() ? src.next() : '\0';
    }

    protected boolean test(char expect) {
//        System.err.println("Testing " + expect + " found " + ch);
        if(ch == expect) {
            nextChar();
            return true;
        }
        return false;
    }

    protected void expect(final String s) {
        for(int i = 0; i < s.length(); ++i) {
            expect(s.charAt(i));
        }
    }

    protected void expect(final char c) {
        if(ch != c) {
            throw error("Expected \'" + c + "\'");
        }
        nextChar();
    }

    protected ParserException error(String message) {
        return src.error(message);
    }

    protected boolean between(final char from, final char to) {
        return from <= ch && ch <= to;
    }

    protected boolean in(final String s) {
        return s.indexOf(ch) != -1;
    }

    public abstract TripleExpression parse(String src);
}
