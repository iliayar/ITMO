package markup;

import java.util.*;

public class Strikeout extends MarkupElement {

    protected String ModifierBegin = "\\textst{";
    protected String ModifierEnd = "}";

    public String getModifierBegin() {
        return ModifierBegin;
    }
    public String getModifierEnd() {
        return ModifierEnd;
    }

    public Strikeout(List<MarkupElement> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}