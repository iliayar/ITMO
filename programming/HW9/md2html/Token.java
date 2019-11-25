package md2html;


import java.util.*;

public class Token {

    private Type type = Type.UNDEFINED;

    private StringBuilder text = new StringBuilder();

    public ArrayList<Token> inner = new ArrayList<Token>();

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
        this.text.append(text);
        this.type = type;
    }

    private static Type matchType(char c) {
        if(Character.isWhitespace(c)) {
            return Type.SEPARATOR;
        }
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
            default:
                return Type.ALPHABETIC;
        }
    }


}