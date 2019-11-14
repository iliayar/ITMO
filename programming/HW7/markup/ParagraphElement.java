package markup;

import java.util.*;

public abstract class ParagraphElement{
    enum Markup {
        HTML,
        TEX,
        MARKDOWN
    }

    List<ParagraphElement> elements;

    protected String texPrefix;
    protected String texPostfix;
    protected String htmlPostfix;
    protected String htmlPrefix;
    protected String mdPostfix;
    protected String mdPrefix;
    
    String element;
    boolean fromString;

    public ParagraphElement(List<ParagraphElement> elements) {
        this.elements = elements;
        fromString = false;
    }

    public ParagraphElement(String element) {
        this.element = element;
        fromString = true;
    }


    public String getPrefix(Markup markup) {
        switch(markup) {
            case HTML:
                return htmlPrefix;
            case TEX:
                return texPrefix;
            case MARKDOWN:
                return mdPrefix;
        }
        return "";
    }

    public String getPostfix(Markup markup) {
        switch(markup) {
            case HTML:
                return htmlPrefix;
            case TEX:
                return texPostfix;
            case MARKDOWN:
                return mdPostfix;    
        }
        return "";
    }

    private void toMarkup(StringBuilder sb, Markup markup) {
        if(fromString) {
            sb.append(getPrefix(markup) + element + getPostfix(markup));
            return;
        }
        sb.append(getPrefix(markup));
        for(ParagraphElement element : elements) {
            element.toMarkup(sb,markup);
        }
        sb.append(getPostfix(markup));
    }

    public void toTex(StringBuilder sb) {
        toMarkup(sb, Markup.TEX);
    }

    public void toHtml(StringBuilder sb) {
        toMarkup(sb, Markup.HTML);
    }
    public void toMarkdown(StringBuilder sb) {
        toMarkup(sb, Markup.MARKDOWN);
    }

}