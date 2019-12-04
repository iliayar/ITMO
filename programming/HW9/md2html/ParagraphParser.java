package md2html;

import java.util.ArrayList;

public class ParagraphParser extends MarkdownParser {

    private Type terminator = Type.NONE;

    public ParagraphParser(ArrayList<Token> tokens) {
        super(tokens);
    }

    public ParagraphParser(String paragraph) {
        super(paragraph);
    }

//    @Override
//    public void genHtml(StringBuilder sb) {
//        parse(new MutableInteger(0)).toHtml(sb);
//    }

    @Override
    public MarkupElement parse(MutableInteger index) {

//        System.out.print("Tokens: ");
//        for(int i = 0; i < tokens.size(); ++i) {
//            System.out.print(tokens.get(i).getType() + " ");
//        }
//        System.out.println();

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
