package md2html;

import java.util.ArrayList;

public class Tokenizer {
    ArrayList<Token> tokens;

    String paragraph;

    public Tokenizer(String paragraph) {
        this.paragraph = paragraph;
    }

    public ArrayList<Token> tokenize() {
        this.tokens = new ArrayList<>();

        for(int i = 0; i < paragraph.length(); ++i) {
            Type t = getType(paragraph.charAt(i));
            if(t == Type.ASTERISK || t == Type.UNDERLINE) {
                if(checkSeparators(i)) {
                    tokens.add(new Token(paragraph.charAt(i), Type.TEXT));
                    continue;
                }
            }
            if(paragraph.charAt(i) == '\\') {
                tokens.add(new Token(paragraph.charAt(++i), Type.TEXT));
                continue;
            }
            tokens.add(new Token(paragraph.charAt(i), t));
        }
        return tokens;
    }

    private boolean checkSeparators(int index) {
        if (getType(paragraph.charAt(index - 1)) == Type.SEPARATOR && getType(paragraph.charAt(index + 1)) == Type.SEPARATOR) {
            return true;
        }
        return false;
    }

    protected Type getType(char c) {
        switch (c) {
            case '*':
                return Type.ASTERISK;
            case '_':
                return Type.UNDERLINE;
            case '-':
                return Type.DASH;
            case '#':
                return Type.HASH;
            case '`':
                return Type.APOS;
            case '[':
                return Type.OP_SQR_BRACKET;
            case ']':
                return Type.CL_SQR_BRACKER;
            case '(':
                return Type.OP_BRACKET;
            case ')':
                return Type.CL_BRACKET;
            case ' ':
            case '\t':
            case '\n':
                return Type.SEPARATOR;
            default:
                return Type.TEXT;
        }
    }

}
