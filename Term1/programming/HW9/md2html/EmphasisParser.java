package md2html;

import java.util.ArrayList;
import java.util.List;

public class EmphasisParser extends MarkdownParser {

    protected EmphasisParser(ArrayList<Token> tokens, Type term) {
        super(tokens);
        this.terminator = term;
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
        parseElems(index, sb);
    }

    @Override
    protected String getHtmlPrefix() {
        return "<em>";
    }

    @Override
    protected String getHtmlPostfix() {
        return "</em>";
    }

    @Override
    protected Type getTerminator() {
        return terminator;
    }

    @Override
    protected ArrayList<Token> getTokens() {
        return tokens;
    }
}
