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
            sb.append('[');
            sb.append(inner);
            return;
        }
        index.inc();
        index.inc();
        this.terminator = Type.CL_BRACKET;
        
        boolean flag = false;
        for(int i = index.val(); i < getTokens().size(); ++i) {
            if(getTokens().get(i).getType() == getTerminator()) {
                flag = true;
                break;
            }
        }

        if(flag) {
            String link = parseRaw(index);

            htmlPrefix = "<a href='" + link + "'>";
            htmlPostfix = "</a>";
            sb.append(htmlPrefix);
            sb.append(inner);
            sb.append(htmlPostfix);
        } else {
            for(int i = stIndex - 1; i < getTokens().size(); ++i) {
                if(getTokens().get(i).getType() == Type.CL_SQRT_BRACKET ||
                        getTokens().get(i).getType() == Type.OP_SQR_BRACKET ||
                        getTokens().get(i).getType() == Type.OP_BRACKET) {
                    getTokens().get(i).setType(Type.TEXT);
                }
            }
            index.setVal(stIndex - 1);
            new TextParser(getTokens()).parse(index, sb);
        }
//        parseElems(index, sb);
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
