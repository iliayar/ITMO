package markup;

import java.util.*;

public class ListItem{

    protected String ModifierBegin = "";
    protected String ModifierEnd = "";
    protected String ModifierEach = "\\item ";

    public String getModifierBegin() {
        return ModifierBegin;
    }

    public String getModifierEach() {
        return ModifierEach;
    }

    public String getModifierEnd() {
        return ModifierEnd;
    }

    List<ListItem> elements;

    public ListItem() {}

    public ListItem(List<ListItem> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        sb.append(getModifierBegin());
        for(ListItem element : elements) {
            sb.append(getModifierEach());
            element.toTex(sb);
        }
        sb.append(getModifierEnd());
    }

}