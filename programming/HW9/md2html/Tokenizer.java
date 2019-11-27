package md2html;

import javax.print.DocFlavor;
import java.util.*;


public class Tokenizer {

    
    TokenStack tokens = new TokenStack();

    String paragraph;

    public Tokenizer(String paragraph) {
        this.paragraph = paragraph;
        tokenize();
    }

    public ArrayList<Token> tokenize() {
        if(tokens.getSize() != 0) {
            return tokens.toArrayList();
        }
        tokens.push(new Token(Type.BEGIN_OF_LINE));
        for(int i = 0;i  < paragraph.length(); ++i) {
            tokens.push(new Token(paragraph.charAt(i)));
            while(prune());
        }
        tokens.push(new Token(Type.END_OF_LINE));
        return tokens.toArrayList();
    }

    public ArrayList<Token> getTree() {
        ArrayList<Token> tokenList = tokenize();
        TokenStack tmp = tokens;
        tokens = new TokenStack();
        for(Token t : tokenList) {
            tokens.push(t);
            while (pruneInner()) ;
        }
        tmp = tokens;
        tokens = new TokenStack();
        return tmp.toArrayList();
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
                if(pattern.get(i) == Type.ANY_COUNT) {
                    --j;
                    continue;
                }
                if (!pattern.get(i).equal(tokens.getFromEnd(j).getType())) {
                    if(i < pattern.size() - 1 && pattern.get(i + 1) == Type.ANY_COUNT) {
//                        System.out.println("TEST");
                        i++;
                        continue;
                    }
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

    private void pruneMarkupUntil(Type t) {
        Token nText = new Text(new Token());
        for(int i = 0; i < tokens.getSize();) {
            if(tokens.getFromEnd(i).getType() == t) {
                break;
            }
            Text tmp = new Text(tokens.pop());
            tmp.add(nText);
            nText = tmp;
        }
        tokens.push(nText);
//        while(prune());
    }

    private void pruneTextUntil(Type t) {
        Token nText = new Token();
        for(int i = 0; i < tokens.getSize();) {
            if(tokens.getFromEnd(i).getType() == t) {
                break;
            }
            Token tmp = tokens.pop();
            tmp.merge(nText.getText(), Type.TEXT);
            nText = tmp;
        }
        tokens.push(nText);
//        while(prune());
    }

    private boolean pruneInner() {

        if(matchPattern(List.of(Type.EMPHASIS_UNDERLINE, Type.ANY, Type.EMPHASIS_UNDERLINE)) ||
                matchPattern(List.of(Type.EMPHASIS_ASTERISK, Type.ANY, Type.EMPHASIS_ASTERISK))) {
            tokens.pop();
            Token inner = tokens.pop();
            tokens.pop();
            tokens.push(new Emphasis(inner));
            return true;
        }

        if(matchPattern(List.of(Type.STRONG_UNDERLINE, Type.ANY, Type.STRONG_UNDERLINE)) ||
                matchPattern(List.of(Type.STRONG_ASTERISK, Type.ANY, Type.STRONG_ASTERISK))) {
            tokens.pop();
            Token inner = tokens.pop();
            tokens.pop();
            tokens.push(new Strong(inner));
            return true;
        }

        if(matchPattern(List.of(Type.CODE, Type.ANY, Type.CODE))) {
            tokens.pop();
            Token inner = tokens.pop();
            tokens.pop();
            tokens.push(new Code(inner));
            return true;
        }

        if(matchPattern(List.of(Type.STRIKEOUT, Type.ANY, Type.STRIKEOUT))) {
            tokens.pop();
            Token inner = tokens.pop();
            tokens.pop();
            tokens.push(new Strikeout(inner));
            return true;
        }

        if(matchPattern(List.of(Type.HEADER, Type.SEPARATOR, Type.ANY_COUNT, Type.END_OF_LINE))) {
            tokens.pop();
            pruneMarkupUntil(Type.SEPARATOR);
            Token inner = tokens.pop();
            tokens.pop();
//            inner.merge(tree.pop().getText(), Type.TEXT);
            Token h = tokens.pop();
            tokens.pop();
            tokens.push(new Header(inner));
            tokens.getTop().setText(h.getText());
            return true;
        }

        if(matchPattern(List.of(Type.MARKUP_ELEMENT, Type.TEXT)) ||
                matchPattern(List.of(Type.TEXT, Type.MARKUP_ELEMENT)) ||
                matchPattern(List.of(Type.MARKUP_ELEMENT, Type.MARKUP_ELEMENT))) {
            Token tmp1 = tokens.pop();
            Token tmp2 = tokens.pop();
            tokens.push(new Text(tmp2));
            tokens.getTop().add(tmp1);
            return true;
        }

        if(matchPattern(List.of(Type.OP_SQR_BRACKET, Type.ANY,Type.CL_SQR_BRACKET,Type.OP_BRACKET,Type.ANY,Type.CL_BRACKET))) {
//            System.out.println("TEST");
            tokens.pop();
            Token tmp1 = tokens.pop();
            tokens.pop();
            tokens.pop();
//            pruneMarkupUntil(Type.OP_SQR_BRACKET);
            Token tmp2 = tokens.pop();
            tokens.pop();
            StringBuilder sb = new StringBuilder();
            Link e = new Link(tmp2);
            sb = new StringBuilder();
            tmp1.toHtml(sb);
            e.setLink(sb.toString());
            tokens.push(e);
            return true;
        }

        if(matchPattern(List.of(Type.BEGIN_OF_LINE, Type.ANY_COUNT, Type.END_OF_LINE))) {
            tokens.pop();
            pruneMarkupUntil(Type.BEGIN_OF_LINE);
            Token tmp1 = tokens.pop();
            tokens.pop();
            tokens.push(new Paragraph(tmp1));
            return true;
        }

        if(matchPattern(List.of(Type.MARKUP_ELEMENT,Type.SEPARATOR,Type.CL_SQR_BRACKET))) {
            Token tmp1 = tokens.pop();
            Token tmp2 = tokens.pop();
            Token tmp3 = tokens.pop();
            Text nText = new Text(tmp3);
            nText.add(tmp2);
            tokens.push(nText);
            tokens.push(tmp1);
            return true;
        }

//         if(matchPattern(List.of(Type.ANY, Type.ANY, Type.END_OF_LINE)) &&
//         !matchPattern(List.of(Type.BEGIN_OF_LINE, Type.ANY, Type.END_OF_LINE)) &&
//         !matchPattern(List.of(Type.SEPARATOR, Type.ANY, Type.END_OF_LINE)) &&
//         !matchPattern(List.of(Type.HEADER, Type.ANY, Type.END_OF_LINE))) {
//             tokens.pop();
////             pruneTextUntil(Type.BEGIN_OF_LINE);
//             tokens.push(new Token(Type.END_OF_LINE));
//             return true;
//         }

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
            tmp.type = Type.TEXT;
            tokens.push(tmp);
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


        if(matchPattern(List.of(Type.CL_SQR_BRACKET,Type.OP_BRACKET,Type.ANY_COUNT,Type.CL_BRACKET))) {
            Token tmp = tokens.pop();
            pruneTextUntil(Type.OP_BRACKET);
            tokens.push(tmp);
        }

        return false;
    }



}