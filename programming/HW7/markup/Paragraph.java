package markup;

import java.util.*;

public class Paragraph extends MarkupList {

    protected String htmlPrefix = "<p>";
    protected String htmlPostfix = "</p>";

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
    public void toHtml(StringBuilder sb) {
        sb.append(htmlPrefix);
        for(ParagraphElement t : elements) {
            t.toHtml(sb);
        }
        sb.append(htmlPostfix);
    }
}