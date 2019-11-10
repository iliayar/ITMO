import java.io.*;
import java.util.*;

import markup.*;

public class Md2Html {

    static Scanner in;


    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        String paragraph = readParagraph();
        while(paragraph.length() > 0) {
            ArrayList<MarkupElement> elements = new ArrayList<MarkupElement>();

            
            paragraph = readParagraph();
        }

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );

    }


    private static String readParagraph() throws IOException {
        StringBuilder paragraph = new StringBuilder();
        while(in.hasNextLine()) {
            String line = in.nextLine();
            if(line.length() > 0) {
                paragraph.append(line);
            } else {
                break;
            }
        }
        return paragraph.toString();
    }
}