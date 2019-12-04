package md2html;

import java.util.ArrayList;
import java.util.List;

public class TextParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    public TextParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
//        index.sub(1);
        return new Text(parseElems(index));
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
