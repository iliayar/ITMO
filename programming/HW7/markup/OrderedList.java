package markup;

import java.util.*;

public class OrderedList extends ListItem {

 
    protected String Prefix = "\\begin{enumerate}";
    protected String Postfix = "\\end{enumerate}";
    protected String Infix = "";

    public String getPrefix() {
        return Prefix;
    }

    public String getInfix() {
        return Infix;
    }

    public String getPostfix() {
        return Postfix;
    }

    public OrderedList(List<ListItem> elements) {
        super(elements);
    }
}