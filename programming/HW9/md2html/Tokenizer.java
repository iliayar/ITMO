package md2html;

import java.util.*;


public class Tokenizer {

    
    TokenStack tokens = new TokenStack();

    String paragraph;

    public Tokenizer(String paragraph) {
        this.paragraph = paragraph;
    }

    public ArrayList<Token> tokenize() {
        tokens.push(new Token(Type.BEGIN_OF_LINE));
        for(int i = 0;i  < paragraph.length(); ++i) {
            tokens.push(new Token(paragraph.charAt(i)));
            while(prune());
        }
        return tokens.toArrayList();
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

        // __ -> STRONG_UNDERLINE
        if(matchPattern(List.of(Type.EMPHASIS_UNDERLINE, Type.EMPHASIS_UNDERLINE))) {
            merge(2, Type.STRONG_UNDERLINE);
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
        if(matchPattern(List.of(Type.ASTERISK))) {
            merge(1, Type.EMPHASIS_UNDERLINE);
            return true;
        }

        // ` -> CODE
        if(matchPattern(List.of(Type.APOS))) {
            merge(1, Type.CODE);
            return true;
        }

        // ` -> CODE
        if(matchPattern(List.of(Type.APOS))) {
            merge(1, Type.CODE);
            return true;
        }

        // # -> CODE
        if(matchPattern(List.of(Type.HASH))) {
            merge(1, Type.HEADER);
            return true;
        }

        // <Alphabetic> -> CODE
        if(matchPattern(List.of(Type.ALPHABETIC))) {
            merge(1, Type.TEXT);
            return true;
        }

        return false;
    }

    private boolean pruneEscape() {

        // \<ANY> -> TEXT
        if(matchPattern(List.of(Type.BACKSLASH, Type.ANY))) {
            merge(2, Type.TEXT);
            return true;
        }

        // <SEPARATOR><(EMPHASIS|STRONG)><SEPARATOR> -> TEXT
        if(matchPattern(List.of(Type.SEPARATOR, Type.STRONG_EMPHASIS, Type.SEPARATOR))) {
            merge(3, Type.TEXT);
            return true;
        }

        // <ANY># -> <ANY>TEXT
        if(matchPattern(List.of(Type.BEGIN_OF_LINE.not(), Type.HEADER))
        //       && matchPattern(List.of(Type.HEADER.not(), Type.HEADER))
        ) {
//            System.out.println(matchPattern(List.of(Type.HEADER, Type.HEADER)));
            merge(1, Type.TEXT);
            return true;
        }

        // TEXT TEXT -> TEXT
        if(matchPattern(List.of(Type.TEXT, Type.TEXT))) {
            merge(2, Type.TEXT);
            return true;
        }

        return false;
    }

    private void mergeInner(int n, Type t) {
        Token nToken = new Token(t);
        for(int i = 0; i < n; ++i) {
            nToken.inner.add(tokens.pop());
        }
        tokens.push(nToken);
    }

    private void merge(int n, Type t) {
        Token nToken = new Token(t);
        for(int i = 0; i < n; ++i) {
            nToken.merge(tokens.pop().getText(), t);
        }
        tokens.push(nToken);
    }

    private boolean matchPattern(List<Type> pattern) {
        try {
            for (int i = pattern.size() - 1; i >= 0; --i) {
//                System.out.println(Integer.toString(i) + " " + pattern.get(i).toString() + " " + tokens.getFromEnd(pattern.size() - 1 - i).getType());
                if (!pattern.get(i).equal(tokens.getFromEnd(pattern.size() - 1 - i).getType())) {
                    return false;
                }
            }
        } catch (IndexOutOfBoundsException e) {
            return false;
        }
        return true;
    }

}