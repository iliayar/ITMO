package markup;

import java.util.*;

public class Text extends MarkupElement {

    protected String ModifierBegin = "";
    protected String ModifierEnd = "";
    public String getModifierBegin() {
        return ModifierBegin;
    }
    public String getModifierEnd() {
        return ModifierEnd;
    }

    public Text(List<MarkupElement> elements) {
        super(elements);
    }
    public Text(String element) {
        super(element);
    }
}