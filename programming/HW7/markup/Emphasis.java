package markup;

import java.util.*;


public class Emphasis extends MarkupElement {

    protected String ModifierBegin = "\\emph{";
    protected String ModifierEnd = "}";

    public String getModifierBegin() {
        return ModifierBegin;
    }
    public String getModifierEnd() {
        return ModifierEnd;
    }

    public Emphasis(List<MarkupElement> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
