package markup;

import java.util.*;

public class ListItem{

    protected String Prefix = "";
    protected String Postfix = "";
    protected String Infix = "\\item ";

    public String getPrefix() {
        return Prefix;
    }

    public String getInfix() {
        return Infix;
    }

    public String getPostfix() {
        return Postfix;
    }

    List<ListItem> elements;

    public ListItem() {}

    public ListItem(List<ListItem> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        sb.append(getPrefix());
        for(ListItem element : elements) {
            sb.append(getInfix());
            element.toTex(sb);
        }
        sb.append(getPostfix());
    }

}