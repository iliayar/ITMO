package md2html;

public class Strikeout extends  MarkupElement {


    public Strikeout(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<s>";
    }

    @Override
    protected String getPostfix() {
        return "</s>";
    }
}
