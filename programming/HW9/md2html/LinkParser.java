package md2html;

import java.util.ArrayList;
import java.util.List;

public class LinkParser extends MarkdownParser {

    private String htmlPrefix = "";
    private String htmlPostfix = "";


    public LinkParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    @Override
    protected String getHtmlPrefix() {
        return htmlPrefix;
    }

    @Override
    protected String getHtmlPostfix() {
        return htmlPostfix;
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {
        int stIndex = index.val();
        this.terminator = Type.CL_SQRT_BRACKET;
        StringBuilder inner = new StringBuilder();
        parseElems(index, inner);
        if(index.val() >= getTokens().size() || getTokens().get(index.val() + 1).getType() != Type.OP_BRACKET) {
            index.setVal(stIndex - 1);
            tokens.get(stIndex - 1).setType(Type.TEXT);
            new TextParser(getTokens()).parse(index, sb);
        }
        index.inc();
        index.inc();
        this.terminator = Type.CL_BRACKET;
        String link = parseRaw(index);
        htmlPrefix = "<a href='" + link + "'>";
        htmlPostfix = "</a>";
        sb.append(htmlPrefix);
        sb.append(inner);
        sb.append(htmlPostfix);
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
