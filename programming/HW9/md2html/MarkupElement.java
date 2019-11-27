package md2html;

import java.util.List;

public abstract class MarkupElement{

    List<MarkupElement> inner;

    String text;

    public MarkupElement(List<MarkupElement> elems) {
        this.inner = elems;
    }
    public MarkupElement(String text) {
        this.text = text;
    }

    protected abstract String getPrefix();
    protected abstract String getPostfix();

    public void toHtml(StringBuilder sb) {
        sb.append(getPrefix());
        if(text != null) {
            sb.append(text);
        } else {
            for (MarkupElement t : inner) {
                t.toHtml(sb);
            }
        }
        sb.append(getPostfix());
    }

}
