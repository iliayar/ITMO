package markup;

import java.util.*;

public class Code extends MarkupElement {

    protected String htmlPostfix = "</code>";
    protected String htmlPrefix = "<code>";
    
    public String getHtmlPrefix(){
        return htmlPrefix;
    }
    public String getHtmlPostfix() {
        return htmlPostfix;
    }

    public Code(List<MarkupElement> elements) {
        super(elements);
    }
    public Code(String element) {
        super(element);
    }
}