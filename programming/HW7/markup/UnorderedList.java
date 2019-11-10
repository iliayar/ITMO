package markup;

import java.util.*;

public class UnorderedList extends MarkupList {


    protected String texPrefix = "\\begin{itemize}";
    protected String texPostfix = "\\end{itemize}";

    public String getTexPrefix() {
        return texPrefix;
    }
    
    public String getTexPostfix() {
        return texPostfix;
    }

    public UnorderedList(List<ListItem> elements) {
        super(elements);
    }
}