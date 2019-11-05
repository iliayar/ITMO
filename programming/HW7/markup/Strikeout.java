package markup;

import java.util.*;

public class Strikeout extends Text {

    private String markupModifier = "~";

    public String getMarkupModifier() {
        return markupModifier;
    }


    public Strikeout(List<Text> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}