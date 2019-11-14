package markup;

import java.util.*;

public class Strikeout extends ParagraphElement {

    protected String texPrefix = "\\textst{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</s>";
    protected String htmlPrefix = "<s>";
    protected String mdPostfix = "--";
    protected String mdPrefix = "--";
    

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

    public Strikeout(List<ParagraphElement> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}