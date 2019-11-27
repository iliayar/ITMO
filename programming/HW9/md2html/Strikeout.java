package md2html;

import java.util.List;

public class Strikeout extends  MarkupElement {


    public Strikeout(List<MarkupElement> elems) {
        super(elems);
    }

    @Override
    protected String getPrefix() {
        return "<s>";
    }

    @Override
    protected String getPostfix() {
        return "</s>";
    }
}
