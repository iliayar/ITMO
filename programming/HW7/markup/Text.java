package markup;

import java.util.*;

public class Text extends MarkupElement {

    protected String texPrefix = "";
    protected String texPostfix = "";
    protected String htmlPostfix = "";
    protected String htmlPrefix = "";
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

    public Text(List<MarkupElement> elements) {
        super(elements);
    }
    public Text(String element) {
        super(element);
    }
}