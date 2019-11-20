package md2html;

import java.util.*;


public class Tokenizer {

    private ArrayList<Token> tokens;

    public ArrayList<Token> tokenize(String p) {
        tokens.add(new Token());
        for(int i = 0, j = 0; i < p.length(); ++i) {
            if(!tokens.get(j).addIfMatch(p.charAt(i))) {
                tokens.add(new Token());
                // System.err.println(tokens.get(j).type + " " + tokens.get(j).text);
                j++;
                // System.out.println(p.charAt(i));
                tokens.get(j).addIfMatch(p.charAt(i));
            }
        }
        return tokens;
    }


}