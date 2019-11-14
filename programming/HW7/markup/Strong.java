package markup;

import java.util.*;

public class Strong extends ParagraphElement {
    protected String texPrefix = "\\textbf{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</strong>";
    protected String htmlPrefix = "<strong>";
    protected String mdPostfix = "**";
    protected String mdPrefix = "**";
    
    public String getPrefix(Markup markup) {
        switch(markup) {
            case HTML:
                return htmlPrefix;
            case TEX:
                return texPrefix;
            case MARKDOWN:
                return mdPrefix;
        }
        return "";
    }

    public String getPostfix(Markup markup) {
        switch(markup) {
            case HTML:
                return htmlPrefix;
            case TEX:
                return texPostfix;
            case MARKDOWN:
                return mdPostfix;    
        }
        return "";
    }

    public Strong(List<ParagraphElement> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}