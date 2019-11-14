package markup;

import java.util.*;


public class Emphasis extends ParagraphElement {

    protected String texPrefix = "\\emph{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</em>";
    protected String htmlPrefix = "<em>";
    protected String mdPostfix = "_";
    protected String mdPrefix = "_";
 
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

    public Emphasis(List<ParagraphElement> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
