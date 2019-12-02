package md2html;

public class Token {
    char c;
    Type t;

    public Token(char c, Type t) {
        this.c = c;
        this.t = t;
    }


    public char getChar() {
        return c;
    }

    public Type getType() {
        return t;
    }
}
