package markup;

import java.util.*;

public class ListItem{

    protected String texInfix = "\\item ";

    public String getTexInfix() {
        return texInfix;
    }

    List<MarkupList> elements;

    public ListItem() {}

    public ListItem(List<MarkupList> elements) {
        this.elements = elements;
    }

    public ListItem(MarkupList element) {
        elements = new ArrayList<MarkupList>();
        elements.add(element);
    }

    public void toTex(StringBuilder sb) {
        for(MarkupList element : elements) {
            sb.append(getTexInfix());
            element.toTex(sb);
        }
    }

}