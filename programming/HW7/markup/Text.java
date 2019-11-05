package markup;

import java.util.*;

public class Text{
    List<Text> elements;
    
    String markupModifier = "";

    String element;
    boolean fromString;

    public Text(List<Text> elements) {
        this.elements = elements;
        fromString = false;
    }

    public Text(String element) {
        this.element = element;
        fromString = true;
    }

    public String getMarkupModifier() {
        return markupModifier;
    }

    public void toMarkdown(StringBuilder sb) {
        String markupModifier = getMarkupModifier();
        if(fromString) {
            sb.append(markupModifier + element + markupModifier);
            return;
        }
        sb.append(markupModifier);
        for(Text element : elements) {
            element.toMarkdown(sb);
        }
        sb.append(markupModifier);
    }
    
}