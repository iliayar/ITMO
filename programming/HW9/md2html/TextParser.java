package md2html;

import java.util.ArrayList;
import java.util.List;

public class TextParser extends MarkdownParser {

    private List<Type> terminator = List.of();

    public TextParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        return new Text(parseElems(index));
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
