package md2html;

import java.util.List;

public class Link extends MarkupElement {

    String link;

    public Link(List<MarkupElement> elems, String link) {
        super(elems);
        this.link = link;
    }

    @Override
    protected String getPrefix() {
        return "";
    }

    @Override
    protected String getPostfix() {
        return "</a>";
    }

    @Override
    public void toHtml(StringBuilder sb) {
        sb.append("<a href=\'");
        sb.append(link);
        sb.append("\'>");
        super.toHtml(sb);
    }
}
