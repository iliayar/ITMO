package markup;

import java.util.*;

public class Strikeout extends MarkupElement {

    protected String Prefix = "\\textst{";
    protected String Postfix = "}";

    public String getPrefix() {
        return Prefix;
    }
    public String getPostfix() {
        return Postfix;
    }

    public Strikeout(List<MarkupElement> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}