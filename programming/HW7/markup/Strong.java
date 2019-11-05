package markup;

import java.util.*;

public class Strong extends Text {
    private String markupModifier = "__";

    public String getMarkupModifier() {
        return markupModifier;
    }

    public Strong(List<Text> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}