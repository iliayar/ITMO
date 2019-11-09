package markup;

import java.util.*;

public class Strong extends MarkupElement {
    protected String Prefix = "\\textbf{";
    protected String Postfix = "}";

    public String getPrefix() {
        return Prefix;
    }
    public String getPostfix() {
        return Postfix;
    }

    public Strong(List<MarkupElement> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}