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
    PARAGRAPH,
    LINK,

    ANY,
    BEGIN_OF_LINE,
    END_OF_LINE,
    ANY_COUNT
    ;


    public boolean equal(Type t) {
        if(this == ANY) {
            return true;
        }
        return this == t;
    }

}