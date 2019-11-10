package markup;

import java.util.*;

public class Strong extends MarkupElement {
    protected String texPrefix = "\\textbf{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</strong>";
    protected String htmlPrefix = "<strong>";
    
    public String getHtmlPrefix(){
        return htmlPrefix;
    }
    public String getHtmlPostfix() {
        return htmlPostfix;
    }

    public String getTexPrefix() {
        return texPrefix;
    }
    public String getTexPostfix() {
        return texPostfix;
    }

    public Strong(List<MarkupElement> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}