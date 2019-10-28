import java.io.FileInputStream;
import java.io.InputStreamReader;
import java.io.IOException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.io.BufferedWriter;
import java.util.Arrays;

public class WordStatCount {

    public static final String SEPARATORS = " \n\t!\"#$%&()*+,./0123456789:;<=>?@[\\]^_`{|}~ ¡¢£¤¥¦§¨©«¬\u00AD®¯°±²³´¶·¸¹»¼½¾¿×÷˂˃˄˅˒˓˔˕˖˗˘˙˚˛˜˝₴₵₶₷₸₹₺\u20BB\u20BC\u20BD\u20BE";


    public static WordPair words[] = new WordPair[1 << 10];

    static int wordsLength = 0;

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
            while(in.hasNextWord()) {
                countWord(in.nextWord());
            }
        } catch(IOException e) {

        }
        Arrays.sort(words, 0, wordsLength, (a,b) -> a.getCount() - b.getCount());

        BufferedWriter out = null;
        try {
            out = new BufferedWriter(
                new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
            );


            for(int i = 0; i < wordsLength; ++i) {
                out.write(words[i].toString());
            }
        } catch (IOException e){
            System.err.println(e.getMessage());
        }

        try {
            words = new WordPair[8];
            wordsLength = 0;
            in.close();
            out.close();
        } catch(IOException e) {}
    }
    public static boolean countWord(String word) {
        if(word.length() == 0){
             return true;
        }

        word = word.toLowerCase();
        int wordIndex = findWord(word);
        
        if(wordIndex == -1) {
            if(wordsLength + 1 >= words.length) {
                words = Arrays.copyOf(words, words.length * 2);
            }
            wordsLength++;

            wordIndex = wordsLength - 1;
            words[wordIndex] = new WordPair(word,wordIndex);
        }
        words[wordIndex].inc();

        return true;
    }

    public static int findWord(String s) {
        for(int i = 0; i < wordsLength; ++i) {
            if(words[i].equals(s))
                return i;
        }
        return -1;
    }

    public static class WordPair {
        StringBuffer word;
        int count;
        int index;

        public WordPair(String word, int index) {
            this.word = new StringBuffer(word);
            this.count = 0;
            this.index = index;
        }

        public void inc() {
            this.count += 1;
        }
        public int getIndex() {
            return this.index;
        }
        public int getCount() {
            return this.count;
        }
        public boolean equals(String s) {
            return s.equals(this.word.toString());
        }
        public String toString() {
            return word.toString() + " " + count + "\n";
        }
    }

}
