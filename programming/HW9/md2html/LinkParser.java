package md2html;

import java.util.ArrayList;
import java.util.List;

public class LinkParser extends MarkdownParser {

    public LinkParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        this.terminator = List.of(Type.CL_SQR_BRACKER, Type.OP_BRACKET);
        ArrayList<MarkupElement> elems = parseElems(index);
        this.terminator = List.of(Type.CL_BRACKET);
        String link = parseRaw(index);
        return new Link(elems,link);
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
