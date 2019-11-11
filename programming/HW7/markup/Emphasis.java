package markup;

import java.util.*;


public class Emphasis extends MarkupElement {

    protected String texPrefix = "\\emph{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</em>";
    protected String htmlPrefix = "<em>";
    
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

    public Emphasis(List<MarkupElement> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
