package md2html;

public class Paragraph extends MarkupElement {
    public Paragraph(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<p>";
    }

    @Override
    protected String getPostfix() {
        return "</p>";
    }
}
