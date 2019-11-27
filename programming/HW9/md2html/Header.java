package md2html;

import java.util.List;

public class Header extends MarkupElement {

    private int size;

    public Header(List<MarkupElement> t, int size) {
        super(t);
        this.size = size;
    }

    @Override
    protected String getPrefix() {
        return "<h" + Integer.toString(size)+ ">";
    }

    @Override
    protected String getPostfix() {
        return "</h" + Integer.toString(size)+ ">";
    }
}
