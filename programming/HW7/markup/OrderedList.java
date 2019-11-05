package markup;

import java.util.*;

public class OrderedList extends ListItem {

 
    protected String ModifierBegin = "\\begin{enumerate}";
    protected String ModifierEnd = "\\end{enumerate}";
    protected String ModifierEach = "";

    public String getModifierBegin() {
        return ModifierBegin;
    }

    public String getModifierEach() {
        return ModifierEach;
    }

    public String getModifierEnd() {
        return ModifierEnd;
    }

    public OrderedList(List<ListItem> elements) {
        super(elements);
    }
}