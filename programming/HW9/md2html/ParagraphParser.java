package md2html;

import java.util.ArrayList;
import java.util.List;

public class ParagraphParser extends MarkdownParser {

    private List<Type> terminator = List.of();

    public ParagraphParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    public ParagraphParser(String paragraph) {
        super(paragraph);
    }

    @Override
    public void genHtml(StringBuilder sb) {
        parse(new MutableInteger(0)).toHtml(sb);
    }

    @Override
    public MarkupElement parse(MutableInteger index) {
        if(tokens.get(index.val()).getType() == Type.HASH) {
            HeaderParser hp = new HeaderParser(getTokens());
            if(hp.isHeader(index) != -1) {
                return hp.parse(index);
            }
        }
//        index.inc();
        return new Paragraph(parseElems(index));
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
