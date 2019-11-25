package md2html;

public class Code extends MarkupElement {




    public Code(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<code>";
    }

    @Override
    protected String getPostfix() {
        return "</code>";
    }

}
