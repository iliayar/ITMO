package markup;

import java.util.*;

public abstract class MarkupList extends ListItem{

    protected String texPrefix;
    protected String texPostfix;
    protected String htmlPostfix;
    protected String htmlPrefix;

    public String getHtmlPrefix(){
        return htmlPrefix;
    }
    public String getHtmlPostfix() {
        return htmlPostfix;
    }

    public String getTexPrefix() {
        return texPrefix;
    }

    public String getTexPostfix() {
        return texPostfix;
    }

    public MarkupList() {}

    public MarkupList(List<ListItem> elements) {
        super(elements);
    }

    public void toTex(StringBuilder sb) {
        sb.append(getTexPrefix());
        for(ListItem element : elements) {
            element.toTex(sb);
        }
        sb.append(getTexPostfix());
    }
}