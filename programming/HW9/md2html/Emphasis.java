package md2html;

public class Emphasis extends MarkupElement {
    public Emphasis(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<em>";
    }

    @Override
    protected String getPostfix() {
        return "</em>";
    }

}
