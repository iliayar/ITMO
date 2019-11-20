package md2html;


import java.util.*;

public class Token {
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
        enum SymbolType {
            APOS,
            STAR,
            DASH,
            UNDERLINE,
            SEPARATOR,
            ALPH,
            BACKSLASH
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

        public boolean hasSeparator() {
            return hasSeparator;
        }

        public String getText() {
            return text.toString();
        }
       
        public static SymbolType getSymbolType(char c) {
            switch(c) {
                case '-':
                    return SymbolType.DASH;
                
                case '*':
                    return SymbolType.STAR;
                
                case '_':
                    return SymbolType.UNDERLINE;
                
                case '`':
                    return SymbolType.APOS;
                
                case '\n':
                case '\t':
                case ' ':
                    return SymbolType.SEPARATOR;

                case '\\':
                    return SymbolType.BACKSLASH;

                default:
                    return SymbolType.ALPH;
            }
        }
        public boolean addIfMatch(char c) {
            if(matchType(getSymbolType(c))) {
                if(getSymbolType(c) == SymbolType.SEPARATOR) {
                    hasSeparator = true;
                }
                if(getSymbolType(c) == SymbolType.BACKSLASH) {
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
                    // text.append("&" + Integer.valueOf(c).toString() + ";");
                } else {
                    text.append(c);
                }
                return true;
            }
            return false;
        }
        public boolean matchType(SymbolType c) {
            if(getType() == MarkupType.NONE) {
                this.type = matchMarkupType(c);
                if(text.length() > 0 && getSymbolType(text.charAt(text.length() - 1)) == SymbolType.BACKSLASH) {
                    if(getType() != MarkupType.TEXT && getType() != MarkupType.NONE) {
                        text.deleteCharAt(text.length() - 1);
                    }

                    this.type = MarkupType.TEXT;
                }
                return true;
            }
            if(getType() != MarkupType.TEXT && getType() != MarkupType.NONE) {
                if(c == SymbolType.SEPARATOR) {
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

        public MarkupType matchMarkupType(SymbolType t) {
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