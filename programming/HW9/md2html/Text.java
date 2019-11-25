package md2html;

public class Text extends MarkupElement {


    public Text(Token t) {
        super(t);
    }

    @Override
    protected String getPrefix() {
        return "";
    }

    @Override
    protected String getPostfix() {
        return "";
    }
}
