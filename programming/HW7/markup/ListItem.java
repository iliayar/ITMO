package markup;

import java.util.*;

public class ListItem{

    protected String texInfix = "\\item ";

    public String getTexInfix() {
        return texInfix;
    }

    List<ListItem> elements;

    public ListItem() {}

    public ListItem(List<ListItem> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        for(ListItem element : elements) {
            sb.append(getTexInfix());
            element.toTex(sb);
        }
    }

}