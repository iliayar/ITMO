package md2html;

import java.util.*;


public abstract class Parser {

    protected List<Token> tokens;
    protected Match[] matches;
    protected Map<Type, TokenStack> tokenMap;
    protected List<Pattern> patterns;


    public Parser() {
        tokenMap = genTokenMap();
        patterns = genPatterns();
    }


    protected void parse() {
        int i = 0;
        for(Token t : tokens) {
            tokenMap.get(t.getType()).push(new Token(t));
            tokenMap.get(t.getType()).get(0).setIndex(i);
            fetchMatches();
            i++;
        }
    }

    private boolean fetchMatches() {
        for(Pattern p : patterns) {
            if(p.match()) {
                Match m = p.fetchMatch();
//                for(Token t : m.getTokens()) {
//                    matches[t.getIndex()] = m;
//                }
                matches[m.getTokens().get(0).index] = m;
                return true;
            }
        }
        return false;
    }

    protected abstract Map<Type, TokenStack> genTokenMap();
    protected abstract List<Pattern> genPatterns();

}