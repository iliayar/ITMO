package markup;

import java.util.*;

public class UnorderedList extends ListItem {


    protected String Prefix = "\\begin{itemize}";
    protected String Postfix = "\\end{itemize}";
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

    public UnorderedList(List<ListItem> elements) {
        super(elements);
    }
}