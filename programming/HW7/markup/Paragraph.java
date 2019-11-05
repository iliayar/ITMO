package markup;

import java.util.*;

public class Paragraph extends ListItem {

    List<MarkupElement> elements;

    public Paragraph(List<MarkupElement> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        for(MarkupElement t : elements) {
            t.toTex(sb);
        }
    }
}