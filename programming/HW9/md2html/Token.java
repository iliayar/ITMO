package md2html;


import java.util.*;

public class Token {

    protected Type type = Type.UNDEFINED;

    protected StringBuilder text = new StringBuilder();

    protected ArrayList<Token> inner = new ArrayList<Token>();

    public Token() {}

    public Token(char c) {
        type = matchType(c);
        text.append(c);
    }

    public Token(Type t) {
        this.type = t;
    }

    public String getText() {
        return text.toString();
    }

    public Type getType() {
        return type;
    }

    public void merge(String text, Type type) {
        // FIX???
        this.text.insert(0,text);
        this.type = type;
    }

    private static Type matchType(char c) {
        switch(c) {
            case '-':
                return Type.DASH;
            case '_':
                return Type.UNDERLINE;
            case '*':
                return Type.ASTERISK;
            case '`':
                return Type.APOS;
            case '[':
                return Type.OP_SQR_BRACKET;
            case ']':
                return Type.CL_SQR_BRACKET;
            case '(':
                return Type.OP_BRACKET;
            case ')':
                return Type.CL_BRACKET;
            case '#':
                return Type.HASH;
            case '\\':
                return Type.BACKSLASH;
            case '\t':
            case ' ':
            case '\n':
            case '\r':
                return Type.SEPARATOR;
            default:
                return Type.ALPHABETIC;
        }
    }

    public void toHtml(StringBuilder sb) {
        sb.append(text.toString());
    }


    public void setText(String s) {
        this.text = new StringBuilder(s);
    }

    public void add(Token t) {
        inner.add(t);
    }


}