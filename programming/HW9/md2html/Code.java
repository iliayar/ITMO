package md2html;

import java.util.List;

public class Code extends MarkupElement {

    public Code(List<MarkupElement> elems) {
        super(elems);
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
