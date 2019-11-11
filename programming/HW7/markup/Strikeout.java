package markup;

import java.util.*;

public class Strikeout extends MarkupElement {

    protected String texPrefix = "\\textst{";
    protected String texPostfix = "}";
    protected String htmlPostfix = "</s>";
    protected String htmlPrefix = "<s>";
    
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

    public Strikeout(List<MarkupElement> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}