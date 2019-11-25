package md2html;

import java.util.*;


public class Parser {

    String paragraph;

    public Parser(String p) {
        this.paragraph = p;
    }


    public void genHtml(StringBuilder sb) {
        ArrayList<Token> tokens = new Tokenizer(paragraph).getTree();

        for(Token t : tokens) {
//            sb.append(t.getType().toString());
//            sb.append(" ");
            t.toHtml(sb);
        }
    }

}