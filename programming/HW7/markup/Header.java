package markup;

import java.util.*;


public class Header extends ParagraphElement {

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

    private void initSize(int size) {
        this.htmlPrefix = "<h" + Integer.toString(size) + ">";
        this.htmlPostfix = "</h" + Integer.toString(size) + ">";
    }

    public Header(List<ParagraphElement> elements, int size) {
        super(elements);
        initSize(size);
    }
    public Header(String element, int size) {
        super(element);
        initSize(size);
    }

}
