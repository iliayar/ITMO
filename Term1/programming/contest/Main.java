import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.io.*;

public class Main {
    static boolean[] was;
    static int[] cnt;
    static int[][] g;
    static int[] c;
    static int[] l;
    static int middle = -1;
    static int mx = -1;
    static int mi = 0;

    static void doubleG(int i) {
        g[i] = Arrays.copyOf(g[i], g[i].length * 2);
    }

    public static void main(String[] args) throws IOException {
        Scanner in = new Scanner(System.in);
        int n, m;
        n = in.nextInt();
        m = in.nextInt();

        c = new int[m];
        g = new int[n][1];
        l = new int[n];

        cnt = new int[n];
        was = new boolean[n];

        for(int i = 0; i < n - 1; ++i) {
            int v, u;
            v = in.nextInt(); v--;
            u = in.nextInt(); u--;
            if(l[v] >= g[v].length) doubleG(v);
            if(l[u] >= g[u].length) doubleG(u);
            g[v][l[v]] = u;
            g[u][l[u]] = v;
            l[v]++; l[u]++;
        }
        for(int i = 0; i < m; ++i) {
            c[i] = in.nextInt() - 1;
        }
        in.close();
        count(c[0],0); renewWas();
        for(int i = 0; i < m; ++i) {
            if(mx < cnt[c[i]]) {
                mx = cnt[c[i]];
                mi = c[i];
            }
        }
        findM(c[0], mi); renewWas();
        if(middle != -1) {
            count(middle, 0);
            if(check()) {
                System.out.println("YES");
                System.out.println(middle + 1);
                return;
            }
        }
        System.out.println("NO");
    }

    static boolean findM(int i, int end) {
        was[i] = true;
        if(i == end){
            if(cnt[i] == mx/2 && mx%2 == 0) {
                middle = i;
            }
            return true;
        }
        for(int j = 0; j < l[i]; ++j) {
            if(was[g[i][j]]) continue;
            if(findM(g[i][j], end)) {
                // System.out.println(cnt[i] + " true " + i);
                if(cnt[i] == mx/2 && mx%2 == 0) {
                    middle = i;
                }
                return true;
            }
            // System.out.println(cnt[i] + " false " + i);
        }
        return false;
    }

    static void renewWas() {
        for(int i = 0; i < was.length; ++i) {
            was[i] = false;
        }
    }

    static boolean check() {
        for(int i = 1; i < c.length; ++i) {
            if(cnt[c[i-1]] != cnt[c[i]]) {
                return false;
            }
        }
        return true;
    }

    static void count(int i, int h) {
        cnt[i] = h;
        was[i] = true;
        for(int j = 0; j < l[i]; ++j) {
            if(was[g[i][j]]) continue;
            count(g[i][j],h+1);
        }
    }


    public static int min(int a, int b) {
        if(a < b)
            return a;
        return b;
    }
    public static int max(int a, int b) {
        if(a > b)
            return a;
        return b;
    }
//#########################FAST_SCANNER##############################################################
    static public class Scanner implements Closeable {   
        
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
                    return !(Character.isLetter(c) || Character.getType(c) == Character.DASH_PUNCTUATION || c == '\'');
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

}
