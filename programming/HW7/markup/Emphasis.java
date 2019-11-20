package markup;

import java.util.*;


public class Emphasis extends ParagraphElement {

    protected String texPrefix = "\\emph{";
    protected String texPostfix = "}";
    protected String mdPostfix = "_";
    protected String mdPrefix = "_";
 

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



    public Emphasis(List<ParagraphElement> elements) {
        super(elements);
    }
    public Emphasis(String element) {
        super(element);
    }

}
