package md2html;

import java.util.ArrayList;
import java.util.List;

public class CodeParser extends MarkdownParser {

    private List<Type> terminator = List.of(Type.APOS);

    public CodeParser(ArrayList<Token> tokens) {
        super(tokens);
    }


    @Override
    public MarkupElement parse(MutableInteger index) {
        return new Code(parseElems(index));
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
