package md2html;

import java.util.List;

public class Strong extends MarkupElement {
    public Strong(List<MarkupElement> elems) {
        super(elems);
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
