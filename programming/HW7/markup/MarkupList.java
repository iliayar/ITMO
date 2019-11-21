package markup;

import java.util.*;

public abstract class MarkupList {
    List<ListItem> elements;

    protected abstract String getTexPrefix();

    protected abstract String getTexPostfix();

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