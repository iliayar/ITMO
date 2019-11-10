package markup;

import java.util.*;

public abstract class MarkupElement{
    enum Markup {
        HTML,
        TEX
    }

    List<MarkupElement> elements;

    protected String texPrefix;
    protected String texPostfix;
    protected String htmlPostfix;
    protected String htmlPrefix;

    
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
    public String getHtmlPrefix(){
        return htmlPrefix;
    }
    public String getHtmlPostfix() {
        return htmlPostfix;
    }

    public String getTexPrefix() {
        return texPrefix;
    }
    public String getTexPostfix() {
        return texPostfix;
    }

    public String getPrefix(Markup markup) {
        switch(markup) {
            case HTML:
                return getHtmlPrefix();
            case TEX:
                return getTexPrefix();
        }
        return "";
    }

    public String getPostfix(Markup markup) {
        switch(markup) {
            case HTML:
                return getHtmlPostfix();
            case TEX:
                return getTexPostfix();
        }
        return "";
    }

    private void toMarkup(StringBuilder sb, Markup markup) {
        if(fromString) {
            sb.append(getPrefix(markup) + element + getPostfix(markup));
            return;
        }
        sb.append(getPrefix(markup));
        for(MarkupElement element : elements) {
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

}