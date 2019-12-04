package md2html;

import java.util.ArrayList;

public abstract class MarkdownParser {
    Type terminator;
    String paragraph;

    ArrayList<Token> tokens;

    public MarkdownParser(String paragraph) {
        this.paragraph = paragraph;
        this.tokens = new Tokenizer(paragraph).tokenize();
    }

    public MarkdownParser(ArrayList<Token> tokens) {
        this.tokens = tokens;
    }


    public void genHtml(StringBuilder sb) {
        parse(new MutableInteger(0)).toHtml(sb);
    }
    public abstract MarkupElement parse(MutableInteger index);

    protected abstract Type getTerminator();
    protected abstract String getParagraph();
    protected abstract ArrayList<Token> getTokens();

    protected boolean checkTerminator(MutableInteger index) {
        if(index.val() >= getTokens().size()) {
            return true;
        }
        if(tokens.get(index.val()).getType() != getTerminator()) {
            return false;
        }
        return true;
    }

    protected ArrayList<MarkupElement> parseElems(MutableInteger index) {
        ArrayList<MarkupElement> elems = new ArrayList<>();
        StringBuilder text = new StringBuilder();
        for(;; index.inc()) {
            if(checkTerminator(index)) {
//                index.inc();
//                System.out.println(getTerminator().size());
                elems.add(new Text(text.toString()));
                break;
            }
            if(tokens.get(index.val()).getType() != Type.SEPARATOR &&
                    tokens.get(index.val()).getType() != Type.TEXT) {
                elems.add(new Text(text.toString()));
                text = new StringBuilder();
//                index.inc();
                MarkdownParser p = getParser(index);
                index.inc();
                elems.add(p.parse(index));
                if(index.val() >= getTokens().size()) {
                    break;
                }
                continue;
            }
            text.append(getTokens().get(index.val()).getChar());
        }
        return elems;
    }

    protected String parseRaw(MutableInteger index) {
        StringBuilder text = new StringBuilder();
        for(;; index.inc()) {
            if(checkTerminator(index)) {
                break;
            }
            if(getTokens().get(index.val()).getType() == Type.DOUBLE_UNDERLINE ||
                    getTokens().get(index.val()).getType() == Type.DOUBLE_ASTERISK ||
                    getTokens().get(index.val()).getType() == Type.DOUBLE_DASH) {
                text.append(getTokens().get(index.val()).getChar());
            }
            text.append(getTokens().get(index.val()).getChar());
        }
        return text.toString();

    }

    protected MarkdownParser getParser(MutableInteger index) {
        switch (tokens.get(index.val()).getType()) {
            case APOS:
                return new CodeParser(getTokens());
            case UNDERLINE:
                return new EmphasisParser(getTokens(), Type.UNDERLINE);
            case DOUBLE_UNDERLINE:
                return new StrongParser(getTokens(), Type.DOUBLE_UNDERLINE);
            case ASTERISK:
                return new EmphasisParser(getTokens(), Type.ASTERISK);
            case DOUBLE_ASTERISK:
                return new StrongParser(getTokens(), Type.DOUBLE_ASTERISK);
            case DOUBLE_DASH:
                return new StrikeoutParser(getTokens());
            case HASH:
                return new HeaderParser(getTokens());
            case OP_SQR_BRACKET:
                return new LinkParser(getTokens());
            default:
                getTokens().get(index.val()).setType(Type.TEXT);
                index.sub(1);
                return new TextParser(getTokens());
        }
    }


}
