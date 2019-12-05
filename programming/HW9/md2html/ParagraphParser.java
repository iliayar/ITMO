package md2html;

import java.util.ArrayList;

public class ParagraphParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    public ParagraphParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    protected String getHtmlPrefix() {
        return "<p>";
    }

    @Override
    protected String getHtmlPostfix() {
        return "</p>";
    }

    public ParagraphParser(String paragraph) {
        super(paragraph);
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {

        if(tokens.get(index.val()).getType() == Type.HASH) {
            HeaderParser hp = new HeaderParser(getTokens());
            if(hp.isHeader(index) != -1) {
                hp.parse(index, sb);
                return;
            }
        }
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
