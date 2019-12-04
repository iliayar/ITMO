package md2html;

import java.util.ArrayList;

public class StrikeoutParser extends MarkdownParser {

    public StrikeoutParser(ArrayList<Token> tokens) {
        super(tokens);
        this.terminator = Type.DOUBLE_DASH;
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        return new Strikeout(parseElems(index));
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
