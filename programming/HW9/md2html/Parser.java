package md2html;

import java.awt.image.AreaAveragingScaleFilter;
import java.util.*;


public class Parser {

    String paragraph;

    public Parser(String p) {
        this.paragraph = p;
    }


    public void genHtml(StringBuilder sb) {
        ArrayList<Token> tokens = new Tokenizer(paragraph).tokenize();

        for(Token t : tokens) {
            sb.append(t.getType().toString());
            sb.append(" ");
        }
    }

}