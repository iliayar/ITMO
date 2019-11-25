package md2html;

public abstract class MarkupElement extends Token{

    protected abstract String getPrefix();
    protected abstract String getPostfix();


    public MarkupElement(Token t) {
        inner.add(t);
        this.type = Type.MARKUP_ELEMENT;
    }

    public void toHtml(StringBuilder sb) {
        sb.append(getPrefix());
        for(Token t : inner) {
            t.toHtml(sb);
        }
        sb.append(getPostfix());
    }

}
