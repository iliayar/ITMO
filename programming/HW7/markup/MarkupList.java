package markup;

import java.util.*;

public abstract class MarkupList{

    protected String texPrefix;
    protected String texPostfix;

    
    List<ListItem> elements;

    public String getTexPrefix() {
        return texPrefix;
    }

    public String getTexPostfix() {
        return texPostfix;
    }

    public MarkupList() {}

    public MarkupList(List<ListItem> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        sb.append(getTexPrefix());
        for(ListItem element : elements) {
            element.toTex(sb);
        }
        sb.append(getTexPostfix());
    }
}