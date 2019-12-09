package md2html;

import java.util.ArrayList;
import java.util.List;

public class CodeParser extends MarkdownParser {

    private Type terminator = Type.APOS;

    public CodeParser(ArrayList<Token> tokens) {
        super(tokens);
    }


    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
        parseElems(index, sb);
    }

    @Override
    protected String getHtmlPrefix() {
        return "<code>";
    }

    @Override
    protected String getHtmlPostfix() {
        return "</code>";
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
