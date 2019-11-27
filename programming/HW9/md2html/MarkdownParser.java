package md2html;

import javax.print.DocFlavor;
import java.util.*;

import static md2html.Type.PARAGRAPH;

public class MarkdownParser extends Parser {

    private MarkupElement paragraph;

    public MarkdownParser(String p) {
        super();
//        this.p = p;
        tokens = new Tokenizer(p).tokenize();
        matches = new Match[tokens.size()];

//        for(Token t : tokens) {
//            System.out.print(t.getType().toString() + " ");
//        }
//        System.out.println();
    }


    @Override
    protected Map<Type, TokenStack> genTokenMap() {
        Map<Type, TokenStack> tokenMap = new LinkedHashMap<Type, TokenStack>();

        tokenMap.put(Type.BEGIN_OF_LINE,      new TokenStack());
        tokenMap.put(Type.END_OF_LINE,        new TokenStack());
        tokenMap.put(Type.EMPHASIS_ASTERISK,  new TokenStack());
        tokenMap.put(Type.EMPHASIS_UNDERLINE, new TokenStack());
        tokenMap.put(Type.STRONG_ASTERISK,    new TokenStack());
        tokenMap.put(Type.STRONG_UNDERLINE,   new TokenStack());
        tokenMap.put(Type.CODE,               new TokenStack());
        tokenMap.put(Type.SEPARATOR,          new TokenStack());
        tokenMap.put(Type.HEADER,             new TokenStack());
        tokenMap.put(Type.STRIKEOUT,          new TokenStack());
        tokenMap.put(Type.TEXT,               new TokenStack());
        tokenMap.put(Type.OP_SQR_BRACKET,     new TokenStack());
        tokenMap.put(Type.CL_SQR_BRACKET,     new TokenStack());
        tokenMap.put(Type.OP_BRACKET,         new TokenStack());
        tokenMap.put(Type.CL_BRACKET,         new TokenStack());
        tokenMap.put(Type.ANY,                new TokenStack());

        return tokenMap;
    }

    @Override
    protected List<Pattern> genPatterns() {
        List<Pattern> patterns = new ArrayList<Pattern>();

        patterns.add(new Pattern(List.of(Type.EMPHASIS_UNDERLINE,Type.ANY_COUNT,Type.EMPHASIS_UNDERLINE), Type.EMPHASIS_UNDERLINE, tokenMap));
        patterns.add(new Pattern(List.of(Type.EMPHASIS_ASTERISK,Type.ANY_COUNT,Type.EMPHASIS_ASTERISK), Type.EMPHASIS_ASTERISK, tokenMap));
        patterns.add(new Pattern(List.of(Type.STRONG_ASTERISK,Type.ANY_COUNT,Type.STRONG_ASTERISK), Type.STRONG_ASTERISK, tokenMap));
        patterns.add(new Pattern(List.of(Type.STRONG_UNDERLINE,Type.ANY_COUNT,Type.STRONG_UNDERLINE), Type.STRONG_UNDERLINE, tokenMap));
        patterns.add(new Pattern(List.of(Type.STRIKEOUT,Type.ANY_COUNT, Type.STRIKEOUT), Type.STRIKEOUT, tokenMap));
        patterns.add(new Pattern(List.of(Type.OP_SQR_BRACKET,Type.ANY_COUNT,Type.CL_SQR_BRACKET,Type.OP_BRACKET,Type.ANY_COUNT,Type.CL_BRACKET), Type.LINK, tokenMap));
        patterns.add(new Pattern(List.of(Type.CODE,Type.ANY_COUNT, Type.CODE), Type.CODE, tokenMap));
        patterns.add(new Pattern(List.of(Type.BEGIN_OF_LINE, Type.HEADER, Type.ANY_COUNT, Type.END_OF_LINE), Type.HEADER, tokenMap));
        patterns.add(new Pattern(List.of(Type.BEGIN_OF_LINE,Type.ANY_COUNT, Type.END_OF_LINE), PARAGRAPH, tokenMap));
//        patterns.add(new Pattern(List.of(Type.TEXT), Type.TEXT, tokenMap));


        return patterns;
    }

    private MarkupElement parseElement(Match m) {
        switch (m.getType()) {
            case EMPHASIS_ASTERISK:
            case EMPHASIS_UNDERLINE:
                return new Emphasis(parseInline(m.getTokens().get(0).index + 1,
                        m.getTokens().get(1).index));
            case STRONG_ASTERISK:
            case STRONG_UNDERLINE:
                return new Strong(parseInline(m.getTokens().get(0).index + 1,
                        m.getTokens().get(1).index));
            case CODE:
                return new Code(parseInline(m.getTokens().get(0).index + 1,
                        m.getTokens().get(1).index));
            case STRIKEOUT:
                return new Strikeout(parseInline(m.getTokens().get(0).index + 1,
                        m.getTokens().get(1).index));
            case PARAGRAPH:
                return new Paragraph(parseInline(m.getTokens().get(0).index + 1,
                        m.getTokens().get(1).index));
            case HEADER:
                return new Header(parseInline(m.getTokens().get(1).index + 2,
                        m.getTokens().get(2).index),m.getTokens().get(1).getText().length());
            case LINK:
                return new Link(parseInline(
                            m.getTokens().get(0).index + 1,
                            m.getTokens().get(1).index),
                        parseRaw(m.getTokens().get(2).index + 1,
                                m.getTokens().get(3).index));
        }
        return null;
    }


    private String parseRaw(int st, int end) {
        StringBuilder sb = new StringBuilder();
        for(int i = st; i < end; ++i) {
            sb.append(tokens.get(i).getText());
        }
        return sb.toString();
    }

    private List<MarkupElement> parseInline(int st, int end) {
        List<MarkupElement> elems = new ArrayList<MarkupElement>();
        for(int i = st; i < end; ++i) {
            if(matches[i] == null) {
                elems.add(new Text(tokens.get(i).getText()));
            } else {
                elems.add(parseElement(matches[i]));
                i = matches[i].getTokens().get(matches[i].getTokens().size() - 1).index;
            }
        }
        return elems;
    }

    public void genHtml(StringBuilder sb) {
        super.parse();
        paragraph = parseElement(matches[0]);
        paragraph.toHtml(sb);
//        paragraph = parseElements(matches.get(matches.size() - 1));
//        paragraph.toHtml(sb);
//        System.out.println(matches.size());
//        for(int i = 0; i < matches.length; ++i) {
//            if(matches[i] == null) {
//                sb.append("NULL ");
//                continue;
//            }
//            sb.append(matches[i].getType().toString() + " ");
//        }
    }

}
