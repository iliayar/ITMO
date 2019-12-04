package md2html;

import java.util.ArrayList;
import java.util.List;

public class LinkParser extends MarkdownParser {

    public LinkParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        int stIndex = index.val();
        this.terminator = Type.CL_SQRT_BRACKET;
        ArrayList<MarkupElement> elems = parseElems(index);
        if(index.val() >= getTokens().size() || getTokens().get(index.val() + 1).getType() != Type.OP_BRACKET) {
            index.setVal(stIndex - 1);
            tokens.get(stIndex - 1).setType(Type.TEXT);
            return new TextParser(getTokens()).parse(index);
        }
        index.inc();
        index.inc();
        this.terminator = Type.CL_BRACKET;
        String link = parseRaw(index);
        return new Link(elems,link);
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
