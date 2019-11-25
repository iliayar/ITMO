package md2html;

public class Header extends MarkupElement {
    public Header(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "<h" + Integer.toString(text.length() )+ ">";
    }

    @Override
    protected String getPostfix() {
        return "</h" + Integer.toString(text.length() )+ ">";
    }
}
