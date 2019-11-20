package markup;

import java.util.*;

public class Strikeout extends ParagraphElement {

    protected String texPrefix = "\\textst{";
    protected String texPostfix = "}";
    protected String mdPostfix = "--";
    protected String mdPrefix = "--";
    


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


    public Strikeout(List<ParagraphElement> elements) {
        super(elements);
    }
    public Strikeout(String element) {
        super(element);
    }
}