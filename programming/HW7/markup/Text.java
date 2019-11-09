package markup;

import java.util.*;

public class Text extends MarkupElement {

    protected String Prefix = "";
    protected String Postfix = "";
    public String getPrefix() {
        return Prefix;
    }
    public String getPostfix() {
        return Postfix;
    }

    public Text(List<MarkupElement> elements) {
        super(elements);
    }
    public Text(String element) {
        super(element);
    }
}