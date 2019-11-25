package md2html;

public enum Type {
    OP_SQR_BRACKET,
    CL_SQR_BRACKET,
    OP_BRACKET,
    CL_BRACKET,
    APOS,
    ASTERISK,
    UNDERLINE,
    DASH,
    SEPARATOR,
    HASH,
    UNDEFINED,
    BACKSLASH,
    ALPHABETIC,

    TEXT,
    HEADER,
    STRONG_ASTERISK,
    EMPHASIS_ASTERISK,
    STRONG_UNDERLINE,
    EMPHASIS_UNDERLINE,
    CODE,
    STRIKEOUT,
    LINK,

    ANY,
    STRONG_EMPHASIS,
    BEGIN_OF_LINE,
    END_OF_LINE,
    MARKUP_ELEMENT,
    ANY_COUNT
    ;

    private boolean not = false;

    public boolean equal(Type t) {
        if(not) {
            if(this != t) {
                return true;
            }
            return false;
        }
        if(this == STRONG_EMPHASIS) {
            if(t == STRONG_ASTERISK || t == EMPHASIS_ASTERISK ||
            t == STRONG_UNDERLINE || t == EMPHASIS_UNDERLINE) {
                return true;
            }
        }
        if(this == ANY || t == ANY) {
            return true;
        }
        return this == t;
    }

}