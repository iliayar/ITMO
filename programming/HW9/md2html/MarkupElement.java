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

    protected void escape(char c, StringBuilder sb) {
        switch (c) {
            case '<':
                sb.append("&lt;");
                break;
            case '>':
                sb.append("&gt;");
                break;
            case '&':
                sb.append("&amp;");
                break;
            default:
                sb.append(c);
        }
    }

    public void toHtml(StringBuilder sb) {
        sb.append(getPrefix());
        if(text != null) {
//            sb.append(text);
            for(int i = 0; i < text.length(); ++i) {
                escape(text.charAt(i), sb);
            }
        } else {
            for (MarkupElement t : inner) {
                t.toHtml(sb);
            }
        }
        sb.append(getPostfix());
    }

}
