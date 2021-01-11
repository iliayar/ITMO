package markup;

import java.util.*;

public class Text extends ParagraphElement {

    protected String texPrefix = "";
    protected String texPostfix = "";
    protected String mdPostfix = "";
    protected String mdPrefix = "";


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


    public Text(List<ParagraphElement> elements) {
        super(elements);
    }
    public Text(String element) {
        super(element);
    }
}