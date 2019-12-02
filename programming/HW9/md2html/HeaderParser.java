package md2html;

import java.util.ArrayList;
import java.util.List;

public class HeaderParser extends MarkdownParser {

    private List<Type> terminator = List.of();

    public HeaderParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    public int isHeader(MutableInteger index) {
        int i = index.val();
        int headerLevel = 0;

        while (i < tokens.size() && tokens.get(i).getType() == Type.HASH) {
            headerLevel++;
//            index.inc();
            i++;
        }

        if(i >= tokens.size() || tokens.get(i).getType() != Type.SEPARATOR || index.val() != 0) {
            return -1;
        }
        return  headerLevel;
    }

    @Override
    public MarkupElement parse(MutableInteger index) {

        int headerLevel = isHeader(index);

        if(headerLevel == -1) {
            ArrayList<MarkupElement> elems = new ArrayList<>();
            elems.add(new Text(parseRaw(index)));
            return new TextParser(getTokens()).parse(index);
        }
        index.add(headerLevel + 1);
        return new Header(parseElems(index),headerLevel);
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
