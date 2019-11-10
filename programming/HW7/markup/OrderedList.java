package markup;

import java.util.*;

public class OrderedList extends MarkupList {

 
    protected String texPrefix = "\\begin{enumerate}";
    protected String texPostfix = "\\end{enumerate}";

    public String getTexPrefix() {
        return texPrefix;
    }

    public String getTexPostfix() {
        return texPostfix;
    }

    public OrderedList(List<ListItem> elements) {
        super(elements);
    }
}