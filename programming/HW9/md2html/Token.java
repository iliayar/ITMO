package md2html;


import java.util.*;

public class Token {

    private Type type = Type.UNDEFINED;

    private StringBuilder text = new StringBuilder();

    protected ArrayList<Token> inner = new ArrayList<Token>();

    int index;

    public Token(char c) {
        type = matchType(c);
        text.append(escapeChars(c));
    }

    public Token(Type t) {
        this.type = t;
    }

    public Token(String s, Type t) {
        this.text = new StringBuilder(s);
        this.type = t;
    }

    public Token(Token t) {
        this.type = t.type;
        this.text = new StringBuilder(t.getText());
    }

    public void setIndex(int index) {
        this.index = index;
    }

    public int getIndex() {
        return index;
    }

    private String escapeChars(char c) {
        switch(c) {
            case '<':
                return "&lt;";
            case '>':
                return "&gt;";
            case '&':
                return "&amp;";
            default:
                return Character.toString(c);
        }
    }

    public String getText() {
        return text.toString();
    }

    public Type getType() {
        return type;
    }

    public void merge(String text, Type type) {
        this.text.append(text);
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

}