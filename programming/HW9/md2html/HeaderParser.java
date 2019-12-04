package md2html;

import java.util.ArrayList;
import java.util.List;

public class HeaderParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    public HeaderParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    public int isHeader(MutableInteger index) {
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
    public MarkupElement parse(MutableInteger index) {

        int headerLevel = isHeader(index);

        if(headerLevel == -1) {
            return new TextParser(getTokens()).parse(index);
        }
        index.add(headerLevel + 1);
        return new Header(parseElems(index),headerLevel);
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
