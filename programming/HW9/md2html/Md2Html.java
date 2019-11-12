package md2html;

import java.io.*;
import java.util.*;

import markup.*;

public class Md2Html {

    static Scanner in;

    static boolean EOF = false;


    static ArrayList<Token> tokens;

    private static void printTokens() {
        for(int i = 0; i < tokens.size(); ++i) {
            System.err.println(tokens.get(i).type + " " + tokens.get(i).text);
        }
    }

    private static ArrayList<Token> tokenize(String p) {
        ArrayList<Token> tokens = new ArrayList<Token>();
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

    static int index = 0;

    private static MarkupElement parseMarkup() {
        ArrayList<MarkupElement> elements = new ArrayList<MarkupElement>();
        StringBuilder text = new StringBuilder();
        Token.MarkupType startType = tokens.get(index).getType();
        if(startType == Token.MarkupType.TEXT) {
            index--;
        }
        for(index++; index < tokens.size(); ++index) {
            if(tokens.get(index).getType() != Token.MarkupType.TEXT) {
                if(tokens.get(index).hasSeparator) {
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
    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );


        
        while(!EOF) {
            String currentParagraph = readParagraph();

            if(currentParagraph.length() <= 1) {
                continue;
            }
            index = 0;
            int hashCount = -1;
            while(currentParagraph.charAt(++hashCount) == '#') {}
            if(currentParagraph.charAt(hashCount) != ' ') {
                hashCount = 0;
            }
            if(hashCount > 0 ) {
                currentParagraph = currentParagraph.substring(hashCount + 1);
            }
            tokens = tokenize(currentParagraph);
            ArrayList<MarkupElement> elements = new ArrayList<MarkupElement>();
            while(index < tokens.size()) {
                elements.add(parseMarkup());
            }


            StringBuilder result = new StringBuilder();
            if(hashCount > 0) {
                new Header(elements, hashCount).toHtml(result);
            } else {
                new Paragraph(elements).toHtml(result);
            }
            // System.err.println("HTML: " + result.toString() + "\n");
            out.write(result.toString() + "\n");
            
            // currentParagraph = readParagraph();

        }

        EOF = false;

        in.close();
        out.close();


    }


    private static String readParagraph() throws IOException {
        StringBuilder paragraph = new StringBuilder();
        while(in.hasNextLine()) {

            String line = in.nextLine();
            if(line.length() > 0) {
                paragraph.append(line + "\n");
            } else {
                break;
            }
        }
        // System.err.println("Paragraph: " + paragraph);

        if(paragraph.length() > 0) {
            paragraph.deleteCharAt(paragraph.length() - 1);
        }
        if(!in.hasNextLine() && paragraph.length() == 0) {
            EOF = true;
        }

        return paragraph.toString();
    }

    private static class Token {
        enum MarkupType {
            TEXT,
            STRONG_STAR,
            STRONG_UNDERLINE,
            EMPHASIS_STAR,
            EMPHASIS_UNDERLINE,
            CODE,
            STRIKEOUT,
            HALF_STRIKEOUT,
            NONE
        }
        enum Type {
            APOS,
            STAR,
            DASH,
            UNDERLINE,
            SEPARATOR,
            ALPH,
            ESCAPE
        }

        MarkupType type;
        StringBuilder text;

        boolean hasSeparator;
        boolean hasEscape;

        public Token() {
            this.hasSeparator = false;
            this.text = new StringBuilder();
            this.type = MarkupType.NONE;
        }

        public String getText() {
            return text.toString();
        }
       
        public static Type getType(char c) {
            switch(c) {
                case '-':
                return Type.DASH;
                
                case '*':
                return Type.STAR;
                
                case '_':
                return Type.UNDERLINE;
                
                case '`':
                return Type.APOS;
                
                case '\n':
                case '\t':
                case ' ':
                return Type.SEPARATOR;

                case '\\':
                return Type.ESCAPE;

                default:
                return Type.ALPH;
            }
        }
        public boolean addIfMatch(char c) {
            if(matchType(getType(c))) {
                if(getType(c) == Type.SEPARATOR) {
                    hasSeparator = true;
                }
                if(getType(c) == Type.ESCAPE) {
                    hasEscape = true;
                }
                if("<>&".indexOf(c) != -1) {
                    switch(c) {
                        case '<':
                        text.append("&lt;");
                        break;

                        case '>':
                        text.append("&gt;");
                        break;

                        case '&':
                        text.append("&amp;");
                        break;
                    }
                } else {
                    text.append(c);
                }
                return true;
            }
            return false;
        }
        public boolean matchType(Type c) {
            if(getType() == MarkupType.NONE) {
                this.type = matchMarkupType(c);
                if(text.length() > 0 && getType(text.charAt(text.length() - 1)) == Type.ESCAPE) {
                    if(getType() != MarkupType.TEXT && getType() != MarkupType.NONE) {
                        text.deleteCharAt(text.length() - 1);
                    }

                    this.type = MarkupType.TEXT;
                }
                return true;
            }
            if(getType() != MarkupType.TEXT && getType() != MarkupType.NONE) {
                if(c == Type.SEPARATOR) {
                    if(hasSeparator || hasEscape) {
                        this.type = MarkupType.TEXT;
                        return false;
                    }
                }
            }
            if(getType() == MarkupType.EMPHASIS_STAR) {
                if(matchMarkupType(c) == MarkupType.EMPHASIS_STAR) {
                    this.type = MarkupType.STRONG_STAR;
                    return true;
                }
            }
            if(getType() == MarkupType.EMPHASIS_UNDERLINE) {
                if(matchMarkupType(c) == MarkupType.EMPHASIS_UNDERLINE) {
                    this.type = MarkupType.STRONG_UNDERLINE;
                    return true;
                }
            }
            if(getType() == MarkupType.HALF_STRIKEOUT) {
                if(matchMarkupType(c) == MarkupType.HALF_STRIKEOUT) {
                    this.type = MarkupType.STRIKEOUT;
                    return true;
                }
                this.type = MarkupType.TEXT;
            }
            if(getType() == MarkupType.TEXT) {
                if(matchMarkupType(c) == MarkupType.TEXT) {
                    return true;
                }
            }

            return false;            
        }
        public MarkupType getType() {
            return this.type;
        }

        public MarkupType matchMarkupType(Type t) {
            switch(t) {
                case DASH:
                return MarkupType.HALF_STRIKEOUT;

                case STAR:
                return MarkupType.EMPHASIS_STAR;

                case UNDERLINE:
                return MarkupType.EMPHASIS_UNDERLINE;

                case APOS:
                return MarkupType.CODE;

                case ALPH:
                return MarkupType.TEXT;

                default:
                return MarkupType.NONE;
            }
        }
    }
}
