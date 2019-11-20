package markup;

import java.util.*;

public class Paragraph extends MarkupList {
    List<ParagraphElement> elements;

    public Paragraph(List<ParagraphElement> elements) {
        this.elements = elements;
    }

    public void toTex(StringBuilder sb) {
        for(ParagraphElement t : elements) {
            t.toTex(sb);
        }
    }
    public void toMarkdown(StringBuilder sb) {
        for(ParagraphElement t : elements) {
            t.toMarkdown(sb);
        }
    }
}