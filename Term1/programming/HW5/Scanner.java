import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.Closeable;
import java.io.IOException;
import java.io.Reader;

public class Scanner implements Closeable {   

    public static final String DASH = "\u002d\u058a\u05be\u1400\u1806\u2010\u2011\u2012\u2013\u2013\u2014\u2015\u2e17\u2e1a\u2e3a\u2e3b\u2e40\u301c\u3030\u30a0\ufe31\ufe32\ufe58\ufe63\uff0d";
    
    static final int LINE_TYPE = 0;
    static final int STRING_TYPE = 1;
    static final int WORD_TYPE = 2;
    static final int NONE_TYPE = -1;

    Reader in;

    char buffer[];
    int bufferIndex;
    int bufferLength;

    StringBuffer stored;
    int storedType;
    int nextStart;
    int nextLength;

    boolean EOF;

    public Scanner(InputStream in) {
        init();
        this.in = new InputStreamReader(in);
    }
    public Scanner(InputStreamReader in) {
        init();
        this.in = in;
    }
    public Scanner(String line) {
        init();
        this.in = new StringReader(line);
    }
    void init() {
        this.storedType = NONE_TYPE;
        this.stored = new StringBuffer();
        this.buffer = new char[1 << 10];
        this.bufferIndex = 0;
        this.EOF = false;
    }

    @Override
    public void close() throws IOException {
        in.close();
    }

    boolean checkSeparator(char c, int type) {
        switch (type) {
            case LINE_TYPE:
                return false;
            case STRING_TYPE:
                return Character.isWhitespace(c);
            case WORD_TYPE:
                return !(Character.isLetter(c) || DASH.indexOf(c) != -1 || c == '\'');
            default:
                return false;
        }
    }

    private char readChar() throws IOException {
        if(bufferIndex >= bufferLength) {
            bufferLength = in.read(buffer,0,buffer.length);
            if(bufferLength == -1) {
                EOF = true;
                return 0;
            }
            bufferIndex = 0;
        }
        return buffer[bufferIndex++];
    }

    public boolean hasNext(int type) throws IOException {
        if(storedType == type) {
            return true;
        }
        
        // char nextChar;

        storedType = type;
        nextLength = 0;
        nextStart = -1;
        int storedIndex = 0;
        for (;!EOF; storedIndex++) {
            if(storedIndex >= stored.length()) {
                char nextChar = readChar();
                stored.append((char)nextChar);
                // System.out.println();
            }
            if(checkSeparator(stored.charAt(storedIndex), type)) {
                if(nextStart < 0) {
                    continue;
                }
                return true;
            }
            if(stored.charAt(storedIndex) == '\n') {
                if(nextStart < 0) {
                    nextStart = storedIndex;
                }
                return true;
            }
            if(nextStart < 0) {
                nextStart = storedIndex;
            }
            nextLength++;
        }

        if(EOF && nextStart < 0 || storedIndex < 0) {
            storedType = NONE_TYPE;
            return false;
        }
        if(EOF) {
            nextLength--;
        }

        return true;

    }

    public String next(int type) throws IOException {
        if(hasNext(type)) {
            String result = stored.substring(nextStart, nextStart + nextLength);
            // System.out.print("|" + result + "|");
            stored.delete(0, nextStart + nextLength + 1);
            storedType = NONE_TYPE;
            return result;
        }
        return "";
    }

    public boolean hasNextLine() throws IOException {
        if(hasNext(LINE_TYPE)) {
            return true;
        }
        return false;
    }
    public String nextLine() throws IOException {
        if(hasNextLine()) {
            return next(LINE_TYPE);
        }
        return "";
    }
    public boolean hasNextString() throws IOException {
        if(hasNext(STRING_TYPE)) {
            if(nextLength <= 0) {
                return false;
            }
            return true;
        }
        return false;
    }
    public String nextString() throws IOException {
        if(hasNextString()) {
            return next(STRING_TYPE);
        }
        return "";
    }

    public boolean hasNextInt() throws IOException {
        if (hasNextString()) {
            try {
                Integer.parseInt(stored.substring(nextStart, nextStart + nextLength));
                return true;
            } catch(NumberFormatException e) {
                return false;
            }
        }
        return false;
    }
    public int nextInt() throws IOException {
        if(hasNextInt()) {
            return Integer.parseInt(nextString());
        }
        return 0;
    }

    public boolean hasNextWord() throws IOException {
        if(hasNext(WORD_TYPE)) {
            if(nextLength <= 0) {
                return false;
            }
            return true;
        }
        return false;
    }
    public String nextWord() throws IOException {
        if(hasNextWord()) {
            return next(WORD_TYPE);
        }
        return "";
    }

}
