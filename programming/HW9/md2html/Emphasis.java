package md2html;

import java.util.List;

public class Emphasis extends MarkupElement {

    public Emphasis(List<MarkupElement> elems) {
        super(elems);
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
