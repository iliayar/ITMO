package md2html;

import java.util.ArrayList;

public class HeaderParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    private String htmlPrefix = " ";
    private String htmlPostfix = " ";

    protected HeaderParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    protected int checkHeader(MutableInteger index) {
        int i = index.val();
        int headerLevel = 0;

        while (i < tokens.size() && tokens.get(i).getType() == Type.HASH) {
            headerLevel++;
            i++;
        }

        if(i >= tokens.size() || tokens.get(i).getType() != Type.SEPARATOR || index.val() != 0) {
            if(index.val() > 0) {
                index.sub(1);
            }
            for(i = index.val(); tokens.get(i).getType() == Type.HASH; ++i) {
                tokens.get(i).setType(Type.TEXT);
            }
            return -1;
        }
        return  headerLevel;
    }

    @Override
    public void parse(MutableInteger index, StringBuilder sb) {

        int headerLevel = checkHeader(index);

        if(headerLevel == -1) {
            new TextParser(getTokens()).parse(index, sb);
        }
        index.add(headerLevel + 1);
        htmlPrefix = "<h" + Integer.toString(headerLevel) + ">";
        htmlPostfix = "</h" + Integer.toString(headerLevel) + ">";
        parseElems(index, sb);
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
    protected Type getTerminator() {
        return terminator;
    }

    @Override
    protected ArrayList<Token> getTokens() {
        return tokens;
    }

}
