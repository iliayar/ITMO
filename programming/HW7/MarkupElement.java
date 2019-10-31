package markup;
import java.util.ArrayList;

public class MarkupElement {
    ArrayList<MarkupElement> elements;

    String markupSymbol;

    boolean fromString;
    String text;

    public void toMarkdown(StringBuilder sb) {
        sb.append(markupSymbol);
        if(fromString) {
            sb.append(text);
        } else {
            for(MarkupElement e : elements) {
                e.toMarkdown(sb);
            }
        }
        sb.append(markupSymbol);
    }

    public MarkupElement(ArrayList<MarkupElement> elements) {
        fromString = false;
        this.elements = elements;
    }
    public MarkupElement(String str) {
        fromString = true;
        text = str;
    }
}
