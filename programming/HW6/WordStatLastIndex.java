import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.BufferedWriter;
import java.util.*;

public class WordStatLastIndex {
    
    static Map<String,WordPair> words = new LinkedHashMap<String,WordPair>();
    
    static Scanner in;
    
    public static void main(String[] args) {
        try {
            in = new Scanner( new InputStreamReader(
                           new FileInputStream(args[0]), "UTF-8"));

        } catch (IOException e) {
            System.err.println(e.getMessage());
            return;
        }

        try {
            while(in.hasNextLine()) {
                Scanner lineIn = new Scanner(in.nextLine());
                Map<String,WordPair> curWords = new LinkedHashMap<String,WordPair>();
                int i = 1;
                while(lineIn.hasNextWord()) {
                    String word = lineIn.nextWord().toLowerCase();
                    if(!curWords.containsKey(word)) {
                        curWords.put(word, new WordPair(i));
                    }
                    curWords.get(word).update(i);
                    i++;
                }
                for(String word : curWords.keySet()) {
                    if(!words.containsKey(word)) {
                        words.put(word, new WordPair());
                    }
                    words.get(word).add(curWords.get(word));
                }

                lineIn.close();
            }
        } catch(IOException e) {}

        BufferedWriter out = null;
        try {
            out = new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
            );

            for(String word : words.keySet()) {
                WordPair pair = words.get(word);
                out.write(word + " " + pair.count);
                for(Integer c : pair.counts) {
                    out.write(" " + c.toString());
                }
                out.write("\n");
            }
        } catch (IOException e){
            System.err.println(e.getMessage());
        }

        try {
            words = new LinkedHashMap<String,WordPair>();
            in.close();
            out.close();
        } catch(IOException e) {}
    }

    static public class WordPair {
        int count;
        int index;
        ArrayList<Integer> counts;
        WordPair() {
            this.count = 0;
            this.counts = new ArrayList<Integer>();
        }
        WordPair(int index) {
            this.index = index;
            this.count = 0;
        }
        public void update(int index) {
            this.count++;
            this.index = index;
        }
        public void add(WordPair cur) {
            this.count += cur.count;
            this.counts.add(cur.index);
        }
    }
}
