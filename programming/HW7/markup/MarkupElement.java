package markup;

import java.util.*;

public abstract class MarkupElement{
    List<MarkupElement> elements;

    protected String ModifierBegin;
    protected String ModifierEnd;

    String element;
    boolean fromString;

    public MarkupElement(List<MarkupElement> elements) {
        this.elements = elements;
        fromString = false;
    }

    public MarkupElement(String element) {
        this.element = element;
        fromString = true;
    }

    public String getModifierBegin() {
        return ModifierBegin;
    }
    public String getModifierEnd() {
        return ModifierEnd;
    }


    public void toTex(StringBuilder sb) {
        String modifierBegin = getModifierBegin();
        String modifierEnd = getModifierEnd();

        if(fromString) {
            sb.append(modifierBegin + element + modifierEnd);
            return;
        }
        sb.append(modifierBegin);
        for(MarkupElement element : elements) {
            element.toTex(sb);
        }
        sb.append(modifierEnd);
    }

}