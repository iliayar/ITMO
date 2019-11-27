package md2html;

import java.util.List;

public class Paragraph extends MarkupElement {

    public Paragraph(List<MarkupElement> elems) {
        super(elems);
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
