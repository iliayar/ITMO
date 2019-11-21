package markup;

import java.util.*;

public abstract class ParagraphElement {
    enum Markup {
        TEX,
        MARKDOWN
    }

    List<ParagraphElement> elements;

    protected String texPrefix;
    protected String texPostfix;
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

    public String getMdPostfix() {
        return mdPostfix;
    }
    public String getMdPrefix() {
        return mdPrefix;
    }
    public String getTexPostfix() {
        return texPostfix;
    }
    public String getTexPrefix() {
        return texPrefix;
    }


    private String getPrefix(Markup markup) {
        switch(markup) {
            case TEX:
                return getTexPrefix();
            case MARKDOWN:
                return getMdPrefix();
        }
        return "";
    }

    private String getPostfix(Markup markup) {
        switch(markup) {
            case TEX:
                return getTexPostfix();
            case MARKDOWN:
                return getMdPostfix();
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

    public void toMarkdown(StringBuilder sb) {
        toMarkup(sb, Markup.MARKDOWN);
    }

}