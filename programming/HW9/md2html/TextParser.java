package md2html;

import java.util.ArrayList;
import java.util.List;

public class TextParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    public TextParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    protected String getHtmlPrefix() {
        return "";
    }

    @Override
    protected String getHtmlPostfix() {
        return "";
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
//        index.sub(1);
        parseElems(index, sb);
    }

    @Override
    protected Type getTerminator() {
        return terminator;
    }

    @Override
    protected String getParagraph() {
        return paragraph;
    }

    @Override
    protected ArrayList<Token> getTokens() {
        return tokens;
    }
}
