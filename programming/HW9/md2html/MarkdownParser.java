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
        parse(new MutableInteger(0), sb);
    }
    public abstract void parse(MutableInteger index, StringBuilder sb);

    protected abstract String getHtmlPrefix();
    protected abstract String getHtmlPostfix();
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

    protected void parseElems(MutableInteger index, StringBuilder sb) {
//        ArrayList<MarkupElement> elems = new ArrayList<>();
//        StringBuilder text = new StringBuilder();
        sb.append(getHtmlPrefix());
        for(;; index.inc()) {
            if(checkTerminator(index)) {
//                index.inc();
//                System.out.println(getTerminator().size());
//                elems.add(new Text(text.toString()));
                break;
            }
            if(tokens.get(index.val()).getType() != Type.SEPARATOR &&
                    tokens.get(index.val()).getType() != Type.TEXT) {
//                elems.add(new Text(text.toString()));
//                text = new StringBuilder();
//                index.inc();
                MarkdownParser p = getParser(index);
                index.inc();
                p.parse(index, sb);
                if(index.val() >= getTokens().size()) {
                    break;
                }
                continue;
            }
            escape(getTokens().get(index.val()).getChar(), sb);
        }
        sb.append(getHtmlPostfix());
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
            escape(getTokens().get(index.val()).getChar(), text);
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

    private void escape(char c, StringBuilder sb) {
        switch (c) {
            case '<':
                sb.append("&lt;");
                break;
            case '>':
                sb.append("&gt;");
                break;
            case '&':
                sb.append("&amp;");
                break;
            default:
                sb.append(c);
        }
    }


}
