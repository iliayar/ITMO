package markup;

import java.util.*;


public class Emphasis extends MarkupElement {

    protected String Prefix = "\\emph{";
    protected String Postfix = "}";

    public String getPrefix() {
        return Prefix;
    }
    public String getPostfix() {
        return Postfix;
    }

    public Emphasis(List<MarkupElement> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
