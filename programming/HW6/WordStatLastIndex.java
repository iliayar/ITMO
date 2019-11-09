import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.BufferedWriter;
import java.util.LinkedHashMap;
import java.util.Map;

import java.util.ArrayList;

public class WordStatLastIndex {
    
    static Map<String,WordPair> words = new LinkedHashMap<String,WordPair>();
        
    public static void main(String[] args) throws IOException {

        Scanner in = new Scanner( new InputStreamReader(
                        new FileInputStream(args[0]), "UTF-8"));


        while(in.hasNextLine()) {
            Scanner lineIn = new Scanner(in.nextLine());
            Map<String,LineWordPair> lineWords = new LinkedHashMap<String,LineWordPair>();
            int i = 1;
            while(lineIn.hasNextWord()) {
                String word = lineIn.nextWord().toLowerCase();
                if(!lineWords.containsKey(word)) {
                    lineWords.put(word, new LineWordPair(i));
                }
                lineWords.get(word).update(i);
                i++;
            }
            for(String word : lineWords.keySet()) {
                if(!words.containsKey(word)) {
                    words.put(word, new WordPair());
                }
                words.get(word).add(lineWords.get(word));
            }

            lineIn.close();
        }

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );

        for(String word : words.keySet()) {
            WordPair pair = words.get(word);
            out.write(word + " " + pair.count);
            for(int i = 0; i < pair.counts.length(); ++i) {
                out.write(" " + pair.counts.get(i));
            }
            out.write("\n");
        }

        words = new LinkedHashMap<String,WordPair>();
        in.close();
        out.close();
    }

    static public class LineWordPair {
        int count;
        int index;

        public LineWordPair(int index) {
            this.index = index;
            this.count = 0;
        }

        public void update(int index) {
            this.count++;
            this.index = index;
        }
    }

    static public class WordPair {
        int count;
        IntList counts;
        public WordPair() {
            this.count = 0;
            this.counts = new IntList();
        }
        public void add(LineWordPair cur) {
            this.count += cur.count;
            this.counts.add(cur.index);
        }
    }
}
