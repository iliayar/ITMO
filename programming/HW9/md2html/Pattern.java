package md2html;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class Pattern {

    private List<Type> pattern;
    private Type type;
    private Map<Type, TokenStack> tokens;

    private Match lastMatch;

    public Pattern(List<Type> pattern, Type t, Map<Type,TokenStack> tokens) {
        this.pattern = pattern;
        this.type = t;
        this.tokens = tokens;
    }

    public Type getType() {
        return type;
    }

    public boolean match() {
        if(tokens.get(pattern.get(0)).size() == 0) {
            return false;
        }
        List<Token> matches = new ArrayList<Token>();
//        int index = tokens.get(pattern.get(0)).get(tokens.get(pattern.get(0)).size() - 1).getIndex();
//        matches.add(tokens.get(pattern.get(0)).get(tokens.get(pattern.get(0)).size() - 1));
        int index = Integer.MAX_VALUE;
//        for(int i = tokens.get(pattern.get(0)).size() - 1; i >= 0; --i) {
//            if(!tokens.get(pattern.get(0)).get(i).isUsed()){
//                index = tokens.get(pattern.get(0)).get(i).getIndex();
//                matches.add(tokens.get(pattern.get(0)).get(i));
//                break;
//            }
//        }
//        if(index == -1) {
//            return false;
//        }
        pattern_for:
        for(int j = 0; j < pattern.size(); ++j) {
            Type t = pattern.get(j);
//            System.out.println("TEST3: " + t.toString() + " " +Integer.toString(index));
            if(t == Type.ANY_COUNT || t == Type.ANY) {
                continue;
            }


            for(int i =  tokens.get(t).lower_bound(index - 1) - 1; i < tokens.get(t).size() ; ++i) {

                if(i < 0) {
                    continue;
                }

                if(index == Integer.MAX_VALUE) {
                    index = tokens.get(t).get(i).getIndex();
                    matches.add(tokens.get(t).get(i));
                    continue pattern_for;
                }
//                System.out.println(tokens.get(t).get(i).getType().toString() + " " + Boolean.toString(tokens.get(t).get(i).isUsed()));
//                if(tokens.get(t).get(i).isUsed()) {
//                    continue;
//                }
                if(tokens.get(t).get(i).getIndex() > index) {
                    int dIndex = tokens.get(t).get(i).getIndex() - index;
                    index = tokens.get(t).get(i).getIndex();
                    if(pattern.get(j - 1) == Type.ANY) {
                        if(dIndex != 2) {
                            return false;
                        }
                    } else if (pattern.get(j - 1) != Type.ANY_COUNT){
                        if(dIndex != 1) {
                            return false;
                        }
                    }
                    matches.add(tokens.get(t).get(i));
                    continue pattern_for;
                }
            }
            return false;
        }
//        System.out.println("TEST4");
        lastMatch = new Match(type, matches);
        return true;
    }

    public Match fetchMatch() {
        if(match()) {
//            lastMatch.getTokens();
            List<Token> matches = lastMatch.getTokens();
            for(int j = matches.size() - 1; j >= 0; --j) {
                Token t = lastMatch.getTokens().get(j);
                int i = t.stackIndex;
//                System.out.println("TEST5: " + Integer.toString(tokens.get(t.getType()).getSize()));
//                Token tmp = tokens.get(t.getType()).get(i);
//                tokens.get(t.getType()).set(i, tokens.get(t.getType()).getFromEnd(0));
//                tokens.get(t.getType()).pop();
                tokens.get(t.getType()).remove(i);
//                tokens.get(t.getType()).get(i).use();
            }
            return lastMatch;
        }
        return null;
    }



}
