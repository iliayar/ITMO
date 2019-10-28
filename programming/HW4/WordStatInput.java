import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.BufferedWriter;
import java.util.*;

public class WordStatInput {

    public static Pair words[] = new Pair[0];
    public static String DASH = "\'\u002d\u058a\u05be\u1400\u1806\u2010\u2011\u2012\u2013\u2013\u2014\u2015\u2e17\u2e1a\u2e3a\u2e3b\u2e40\u301c\u3030\u30a0\ufe31\ufe32\ufe58\ufe63\uff0d";
    
    public static void main(String[] args) {
        
        Scanner in = null;

        try {
            in = new Scanner( new InputStreamReader(
                           new FileInputStream(args[0]), "UTF-8"));

        } catch (IOException e) {
            System.err.println(e.getMessage());
            return;
        }

        try {
            
            StringBuffer temp = new StringBuffer("");
            while(in.hasNextLine()) {
                String input = in.nextLine();
                // System.err.println(input);
                for(int j = 0; j <= input.length(); ++j) {
                    // if(j == input.length() ||  input.charAt(j) != Character.DASH_PUNCTUATION && 
                    // input.charAt(j) != '\'' && 
                    // input.charAt(j) != '-' && 
                    // !Character.isLetter(input.charAt(j))) { 
                    // System.err.println(DASH.indexOf(input.charAt(j)));                       
                    if(j == input.length() || 
                    DASH.indexOf(input.charAt(j)) == -1 && 
                    !Character.isLetter(input.charAt(j))) {
                        countWord(temp.toString());
                        temp = new StringBuffer();
                        continue;
                    }
                    temp.append(input.charAt(j));
                }
            }
        } catch(IOException e) {

        }
        // Arrays.sort(words,(a,b) -> a.getCount() - b.getCount());

        BufferedWriter out = null;
        try {
            out = new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
            );


            for(int i = 0; i < words.length; ++i) {
                out.write(words[i].toString());
            }
            // out.write('\n');
        } catch (IOException e){
            System.err.println(e.getMessage());
        }

        try {
            words = new Pair[0];
            in.close();
            out.close();
        } catch(IOException e) {}
    }

    public static boolean countWord(String temp) {
        if(temp.length() == 0) return true;


        temp = temp.toLowerCase();
        int wordIndex = findWord(temp);
        if(wordIndex == -1) {
            words = Arrays.copyOf(words, words.length + 1);
            wordIndex = words.length - 1;
            words[wordIndex] = new Pair(temp);
        }
        words[wordIndex].inc();
        return true;
    }

    public static int findWord(String s) {
        for(int i = 0; i < words.length; ++i) {
            if(words[i].equals(s))
                return i;
        }
        return -1;
    }

    public static class Pair {
        StringBuffer word;
        Integer count;

        public Pair(String word, Integer count) {
            this.word = new StringBuffer(word);
            this.count = count;
        }

        public Pair(String word) {
            this.word = new StringBuffer(word);
            this.count = 0;
        }

        public Pair() {
            this.word = new StringBuffer();
            this.count = 0;
        }

        public void inc() {
            this.count += 1;
        }
        public Integer getCount() {
            return this.count;
        }
        public boolean equals(String s) {
            return s.equals(this.word.toString());
        }
        public String toString() {
            return word.toString() + " " + count.toString() + "\n";
        }
    }

}
