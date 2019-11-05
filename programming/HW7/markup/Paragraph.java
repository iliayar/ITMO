package markup;

import java.util.*;

public class Paragraph{

    List<Text> elements;
    
    public Paragraph(List<Text> elements) {
        this.elements = elements;
    }
    public void toMarkdown(StringBuilder sb) {
        for(Text t : elements) {
            t.toMarkdown(sb);
        }
    }
}