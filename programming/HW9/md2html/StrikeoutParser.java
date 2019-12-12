package md2html;

import java.util.ArrayList;

public class StrikeoutParser extends MarkdownParser {

    protected StrikeoutParser(ArrayList<Token> tokens) {
        super(tokens);
        this.terminator = Type.DOUBLE_DASH;
    }

    @Override
    protected String getHtmlPrefix() {
        return "<s>";
    }

    @Override
    protected String getHtmlPostfix() {
        return "</s>";
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
        parseElems(index, sb);
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
