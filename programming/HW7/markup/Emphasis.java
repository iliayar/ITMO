package markup;

import java.util.*;


public class Emphasis extends Text {
    private String markupModifier = "*";

    public String getMarkupModifier() {
        return markupModifier;
    }

    public Emphasis(List<Text> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
