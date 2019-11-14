package markup;

import java.util.*;

public class Code extends ParagraphElement {

    protected String htmlPostfix = "</code>";
    protected String htmlPrefix = "<code>";
    
    public String getHtmlPrefix(){
        return htmlPrefix;
    }
    public String getHtmlPostfix() {
        return htmlPostfix;
    }

    public Code(List<ParagraphElement> elements) {
        super(elements);
    }
    public Code(String element) {
        super(element);
    }
}