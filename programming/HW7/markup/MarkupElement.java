package markup;

import java.util.*;

public abstract class MarkupElement{
    List<MarkupElement> elements;

    protected String Prefix;
    protected String Postfix;

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

    public String getPrefix() {
        return Prefix;
    }
    public String getPostfix() {
        return Postfix;
    }


    public void toTex(StringBuilder sb) {
        String Prefix = getPrefix();
        String Postfix = getPostfix();

        if(fromString) {
            sb.append(Prefix + element + Postfix);
            return;
        }
        sb.append(Prefix);
        for(MarkupElement element : elements) {
            element.toTex(sb);
        }
        sb.append(Postfix);
    }

}