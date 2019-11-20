package md2html;

import java.util.*;
import markup.*;


public class Parser {

    private int index = 0;

    ArrayList<Token> tokens;

    public void genHtml(String p, StringBuilder sb) {
        int hashCount = -1;
            while(p.charAt(++hashCount) == '#') {}
            if(p.charAt(hashCount) != ' ') {
                hashCount = 0;
            }
            if(hashCount > 0 ) {
                p = p.substring(hashCount + 1);
        }

        tokens = new Tokenizer().tokenize(p);

        ArrayList<ParagraphElement> elements = new ArrayList<ParagraphElement>();
        
        while(index < tokens.size()) {
            elements.add(parseMarkup());
        }

        if(hashCount > 0) {
            new Header(elements, hashCount).toHtml(sb);
        } else {
            new Paragraph(elements).toHtml(sb);
        }
    }


    private ParagraphElement parseMarkup() {
        ArrayList<ParagraphElement> elements = new ArrayList<ParagraphElement>();
        StringBuilder text = new StringBuilder();
        Token.MarkupType startType = tokens.get(index).getType();
        if(startType == Token.MarkupType.TEXT) {
            index--;
        }
        for(index++; index < tokens.size(); ++index) {
            if(tokens.get(index).getType() != Token.MarkupType.TEXT) {
                if(tokens.get(index).hasSeparator()) {
                    text.append(tokens.get(index).getText().charAt(0));
                }
                elements.add(new Text(text.toString()));
                text = new StringBuilder();
                if(tokens.get(index).getType() == startType) {
                    switch(startType) {
                        case STRONG_STAR:
                        case STRONG_UNDERLINE:
                            return new Strong(elements);
                        case EMPHASIS_STAR:
                        case EMPHASIS_UNDERLINE:
                            return new Emphasis(elements);
                        case CODE:
                            return new Code(elements);
                        case STRIKEOUT:
                            return new Strikeout(elements);
                    }
                }
                elements.add(parseMarkup());
                continue;
            }
            text.append(tokens.get(index).getText());

        }
        elements.add(new Text(text.toString()));
        return new Text(elements);

    }


}