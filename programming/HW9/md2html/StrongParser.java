package md2html;

import java.util.ArrayList;
import java.util.List;

public class StrongParser extends MarkdownParser {
    protected StrongParser(ArrayList<Token> tokens, Type term) {
        super(tokens);
        this.terminator = term;
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
        parseElems(index,sb);
    }

    @Override
    protected String getHtmlPrefix() {
        return "<strong>";
    }

    @Override
    protected String getHtmlPostfix() {
        return "</strong>";
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
