package md2html;

public class Strong extends MarkupElement {
    public Strong(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<strong>";
    }

    @Override
    protected String getPostfix() {
        return "</strong>";
    }
}
