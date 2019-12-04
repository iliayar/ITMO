package md2html;

import java.util.ArrayList;
import java.util.List;

public class EmphasisParser extends MarkdownParser {

    public EmphasisParser(ArrayList<Token> tokens, Type term) {
        super(tokens);
        this.terminator = term;
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        return new Emphasis(parseElems(index));
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
