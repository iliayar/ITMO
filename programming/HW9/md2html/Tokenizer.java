package md2html;

import java.util.*;


public class Tokenizer {

    
    TokenStack tokens = new TokenStack();

    String paragraph;

    public Tokenizer(String paragraph) {
        this.paragraph = paragraph;
        tokenize();
    }

    public List<Token> tokenize() {
        if(tokens.size() != 0) {
            return tokens.toList();
        }
        tokens.push(new Token(Type.BEGIN_OF_LINE));
        for(int i = 0;i  < paragraph.length(); ++i) {
            tokens.push(new Token(paragraph.charAt(i)));
            while(prune());
        }
        tokens.push(new Token(Type.END_OF_LINE));
        return tokens.toList();
    }


    private void merge(int n, Type t) {
        Token nToken = new Token(t);
        for(int i = 0; i < n; ++i) {
            Token tmp = tokens.pop();
            tmp.merge(nToken.getText(), t);
            nToken = tmp;
        }
        tokens.push(nToken);
    }

    private boolean matchPattern(List<Type> pattern) {
        try {
            for (int i = pattern.size() - 1, j = 0; i >= 0; --i, ++j) {
//                System.out.println(Integer.toString(i) + " " + pattern.get(i).toString() + " " + tokens.getFromEnd(pattern.size() - 1 - i).getType());
                if (!pattern.get(i).equal(tokens.get(j).getType())) {
                    return false;
                }
            }
        } catch (IndexOutOfBoundsException e) {
            return false;
        }
        return true;
    }

    private boolean prune() {

        if(pruneEscape()) {
            return true;
        }
        if(pruneSymbols()) {
            return true;
        }
        if(pruneInline()) {
            return true;
        }
        return false;
    }

    private boolean pruneInline() {

        // ** -> STRONG_ASTERISK
        if(matchPattern(List.of(Type.EMPHASIS_ASTERISK, Type.EMPHASIS_ASTERISK))) {
            merge(2, Type.STRONG_ASTERISK);
            return true;
        }

        // ## -> HEADER
        if(matchPattern(List.of(Type.HEADER, Type.HEADER))) {
            merge(2, Type.HEADER);
            return true;
        }

        // __ -> STRONG_UNDERLINE
        if(matchPattern(List.of(Type.EMPHASIS_UNDERLINE, Type.EMPHASIS_UNDERLINE))) {
            merge(2, Type.STRONG_UNDERLINE);
            return true;
        }

        // -- > STRIKEOUT
        if(matchPattern(List.of(Type.DASH, Type.DASH))) {
            merge(2, Type.STRIKEOUT);
            return true;
        }

        return false;
    }

    private boolean pruneSymbols() {

        // * -> EMPHASIS_ASTERISK
        if(matchPattern(List.of(Type.ASTERISK))) {
            merge(1, Type.EMPHASIS_ASTERISK);
            return true;
        }

        // _ -> EMPHASIS_UNDERLINE
        if(matchPattern(List.of(Type.UNDERLINE))) {
            merge(1, Type.EMPHASIS_UNDERLINE);
            return true;
        }

        // ` -> CODE
        if(matchPattern(List.of(Type.APOS))) {
            merge(1, Type.CODE);
            return true;
        }

        // # -> HEADER
        if(matchPattern(List.of(Type.HASH))) {
            merge(1, Type.HEADER);
            return true;
        }

        // <Alphabetic> -> TEXT
        if(matchPattern(List.of(Type.ALPHABETIC))) {
            merge(1, Type.TEXT);
            return true;
        }

        return false;
    }

    private boolean pruneEscape() {

        // \<ANY> -> TEXT
        if(matchPattern(List.of(Type.BACKSLASH, Type.ANY))) {
            Token tmp = tokens.pop();
            tokens.pop();
            tokens.push(new Token(tmp.getText(), Type.TEXT));
            return true;
        }

        // <SEPARATOR><(EMPHASIS|STRONG)><SEPARATOR> -> TEXT
        if(matchPattern(List.of(Type.SEPARATOR, Type.STRONG_ASTERISK, Type.SEPARATOR)) ||
                matchPattern(List.of(Type.SEPARATOR, Type.STRONG_UNDERLINE, Type.SEPARATOR)) ||
                matchPattern(List.of(Type.SEPARATOR, Type.EMPHASIS_ASTERISK, Type.SEPARATOR)) ||
                matchPattern(List.of(Type.SEPARATOR, Type.EMPHASIS_UNDERLINE, Type.SEPARATOR))) {
            merge(3, Type.TEXT);
            return true;
        }

        // <!HEADER !BOF># -> <ANY>TEXT
        if(!matchPattern(List.of(Type.BEGIN_OF_LINE, Type.HEADER)) &&
                !matchPattern(List.of(Type.HEADER, Type.HEADER)) &&
                matchPattern(List.of(Type.ANY, Type.HEADER))) {
            merge(1, Type.TEXT);
            return true;
        }


        // TEXT TEXT -> TEXT
        if(matchPattern(List.of(Type.TEXT, Type.TEXT))) {
            merge(2, Type.TEXT);
            return true;
        }

        // SEPARATOR SEPARATOR -> SEPARATOR
        if(matchPattern(List.of(Type.SEPARATOR, Type.SEPARATOR))) {
            merge(2, Type.SEPARATOR);
            return true;
        }

        // <!HEADER><SEPARATOR><TEXT> -> <ANY>TEXT
        if(matchPattern(List.of(Type.ANY, Type.SEPARATOR, Type.TEXT)) &&
                !matchPattern(List.of(Type.HEADER, Type.SEPARATOR, Type.TEXT))) {
            merge(2, Type.TEXT);
            return true;
        }

        // <TEXT><SEPARATOR><ANY><ANY> -> TEXT<ANY><ANY>
        if(matchPattern(List.of(Type.TEXT, Type.SEPARATOR, Type.ANY, Type.ANY))) {
            Token tmp1 = tokens.pop();
            Token tmp2 = tokens.pop();
            merge(2, Type.TEXT);
            tokens.push(tmp2);
            tokens.push(tmp1);
            return true;
        }

        // <HEADER><TEXT><ANY> -> <TEXT><ANY>
        if(matchPattern(List.of(Type.HEADER, Type.TEXT, Type.ANY))) {
            Token tmp = tokens.pop();
            merge(2, Type.TEXT);
            tokens.push(tmp);
            return true;
        }


        // <TEXT><SEPARATOR><TEXT> -> TEXT
        if(matchPattern(List.of(Type.TEXT, Type.SEPARATOR, Type.TEXT)) ||
                matchPattern(List.of(Type.TEXT, Type.DASH, Type.TEXT))) {
            merge(3, Type.TEXT);
            return true;
        }

        return false;
    }



}