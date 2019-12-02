package md2html;

import java.util.ArrayList;
import java.util.List;

public class StrongParser extends MarkdownParser {
    public StrongParser(ArrayList<Token> tokens, List<Type> term) {
        super(tokens);
        this.terminator = term;
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        return new Strong(parseElems(index));
    }

    @Override
    protected List<Type> getTerminator() {
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
