import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.StringReader;
import java.io.BufferedReader;
import java.io.IOException;

public class Scanner {   

    public static String DASH = "\'\u002d\u058a\u05be\u1400\u1806\u2010\u2011\u2012\u2013\u2013\u2014\u2015\u2e17\u2e1a\u2e3a\u2e3b\u2e40\u301c\u3030\u30a0\ufe31\ufe32\ufe58\ufe63\uff0d";
    
    BufferedReader in;

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
        this.in = new BufferedReader(new InputStreamReader(in));
    }
    public Scanner(InputStreamReader in) {
        init();
        this.in = new BufferedReader(in);
    }
    public Scanner(String line) {
        init();
        this.in = new BufferedReader(new StringReader(line));
    }
    void init() {
        this.storedType = -1;
        this.stored = new StringBuffer();
        this.buffer = new char[1 << 10];
        this.bufferIndex = 0;
        this.EOF = false;
    }

    public void close() throws IOException {
        in.close();
    }

    boolean checkSeparator(char c, int type) {
        switch (type) {
            case 0: // line
                return false;
            case 1: //string
                return Character.isWhitespace(c);
            case 2:// word
                return !(Character.isLetter(c) || DASH.indexOf(c) != -1);
            default:
                return false;
        }
    }

    char readChar() throws IOException {
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
        
        char nextChar;

        storedType = type;
        nextLength = 0;
        nextStart = -1;
        int storedIndex = 0;
        for (;!EOF; storedIndex++) {
            if(storedIndex >= stored.length()) {
                nextChar = readChar();
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
            storedType = -1;
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
            storedType = -1;
            return result;
        }
        return "";
    }

    public boolean hasNextLine() throws IOException {
        if(hasNext(0)) {
            return true;
        }
        return false;
    }
    public String nextLine() throws IOException {
        if(hasNextLine()) {
            return next(0);
        }
        return "";
    }
    public boolean hasNextString() throws IOException {
        if(hasNext(1)) {
            if(nextLength <= 0) {
                return false;
            }
            return true;
        }
        return false;
    }
    public String nextString() throws IOException {
        if(hasNextString()) {
            return next(1);
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
        return -1;
    }

    public boolean hasNextWord() throws IOException {
        if(hasNext(2)) {
            if(nextLength <= 0) {
                return false;
            }
            return true;
        }
        return false;
    }
    public String nextWord() throws IOException {
        if(hasNextString()) {
            return next(2);
        }
        return "";
    }

}
