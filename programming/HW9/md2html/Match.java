package md2html;

import java.util.List;

public class Match {

    private Type type;


    private List<Token> tokens;

    public Match(Type t, List<Token> tokens) {
        this.type = t;
        this.tokens = tokens;
    }

    public List<Token> getTokens() {
        return tokens;
    }

    public Type getType() {
        return type;
    }
}
