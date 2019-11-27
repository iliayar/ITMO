package md2html;

import java.util.List;

public class Text extends MarkupElement {

    public Text(List<MarkupElement> elems) {
        super(elems);
    }
    public Text(String text) {super(text);}

    @Override
    protected String getPrefix() {
        return "";
    }

    @Override
    protected String getPostfix() {
        return "";
    }
}
