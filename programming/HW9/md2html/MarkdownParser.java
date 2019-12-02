package md2html;

import java.util.ArrayList;
import java.util.List;

public abstract class MarkdownParser {
    List<Type> terminator;
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

    protected abstract List<Type> getTerminator();
    protected abstract String getParagraph();
    protected abstract ArrayList<Token> getTokens();

    protected boolean checkTerminator(Integer index) {
        if(index >= getTokens().size()) {
            return false;
        }
        for(int i = index; i > index - getTerminator().size(); --i) {
            if(tokens.get(i).getType() != getTerminator().get(getTerminator().size() - index + i - 1)) {
                return false;
            }
        }
        return true;
    }

    protected ArrayList<MarkupElement> parseElems(MutableInteger index) {
        ArrayList<MarkupElement> elems = new ArrayList<>();
        StringBuilder text = new StringBuilder();
        for(;; index.inc()) {
            if(!checkTerminator(index.val())) {
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
            }
            text.append(getTokens().get(index.val()).getChar());
        }
        return elems;
    }

    protected String parseRaw(MutableInteger index) {
        StringBuilder text = new StringBuilder();
        for(;; index.inc()) {
            if(checkTerminator(index.val())) {
                break;
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
                return getUnderlineParser(index, getTokens());
            case ASTERISK:
                return getAsteriskParser(index, getTokens());
            case HASH:
                return new HeaderParser(getTokens());
            case OP_SQR_BRACKET:
                return new LinkParser(getTokens());
            default:
                return new TextParser(getTokens());
        }
    }

    private MarkdownParser getUnderlineParser(MutableInteger index, ArrayList<Token> tokens) {

        if(index.val() + 1 < tokens.size() && tokens.get(index.val() + 1).getType() == Type.UNDERLINE) {
            return new StrongParser(tokens, List.of(Type.UNDERLINE, Type.UNDERLINE));
        } else {
            return new EmphasisParser(tokens, List.of(Type.UNDERLINE));
        }
    }

    private MarkdownParser getAsteriskParser(MutableInteger index,  ArrayList<Token> tokens) {
        if(tokens.get(index.val() + 1).getType() == Type.ASTERISK) {
            return new StrongParser(tokens, List.of(Type.ASTERISK, Type.ASTERISK));
        } else {
            return new EmphasisParser(tokens, List.of(Type.ASTERISK));
        }
    }


}
