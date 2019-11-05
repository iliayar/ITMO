package markup;

import java.util.*;

public class UnorderedList extends ListItem {


    protected String ModifierBegin = "\\begin{itemize}";
    protected String ModifierEnd = "\\end{itemize}";
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

    public UnorderedList(List<ListItem> elements) {
        super(elements);
    }
}