package markup;

import java.util.*;

public class Strong extends ParagraphElement {
    protected String texPrefix = "\\textbf{";
    protected String texPostfix = "}";
    protected String mdPostfix = "**";
    protected String mdPrefix = "**";
    

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

    public Strong(List<ParagraphElement> elements) {
        super(elements);
    }
    public Strong(String element) {
        super(element);
    }
}