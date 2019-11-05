package markup;

import java.util.*;

public class Strong extends MarkupElement {
    protected String ModifierBegin = "\\textbf{";
    protected String ModifierEnd = "}";

    public String getModifierBegin() {
        return ModifierBegin;
    }
    public String getModifierEnd() {
        return ModifierEnd;
    }

    public Strong(List<MarkupElement> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}