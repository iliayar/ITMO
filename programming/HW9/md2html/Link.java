package md2html;

public class Link extends MarkupElement {
    public Link(Token t) {
        super(t);
    }

    String link;

    @Override
    protected String getPrefix() {
        return "";
    }

    @Override
    protected String getPostfix() {
        return "</a>";
    }

    public void setLink(String s) {
        this.link = s;
    }

    @Override
    public void toHtml(StringBuilder sb) {
        sb.append("<a href=\'");
        sb.append(link);
        sb.append("\'>");
        super.toHtml(sb);
    }
}
