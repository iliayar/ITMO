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

    ANY,
    STRONG_EMPHASIS,
    BEGIN_OF_LINE
    ;

    private boolean not = false;

    public boolean equal(Type t) {
        if(not) {
//            System.out.println(this + " " + t);
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

    public Type not() {
        this.not = true;
        return this;
    }
}