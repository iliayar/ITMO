package markup;

import java.util.*;

public class UnorderedList extends MarkupList {


    private String texPrefix = "\\begin{itemize}";
    private String texPostfix = "\\end{itemize}";

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