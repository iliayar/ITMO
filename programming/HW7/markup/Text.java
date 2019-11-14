package markup;

import java.util.*;

public class Text extends ParagraphElement {

    protected String texPrefix = "";
    protected String texPostfix = "";
    protected String htmlPostfix = "";
    protected String htmlPrefix = "";
    protected String mdPostfix = "";
    protected String mdPrefix = "";

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

    public Text(List<ParagraphElement> elements) {
        super(elements);
    }
    public Text(String element) {
        super(element);
    }
}