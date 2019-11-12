import java.io.*;
import java.util.*;

import markup.*;

public class Md2Html {

    static Scanner in;

    private static MarkupElement parseMarkup(String paragraph) {
      

    }
    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );


        String currentParagraph = readParagraph();
        while(currentParagraph.length() > 0) {
            if(currentParagraph.length() <= 1) {
                // currentParagraph = readParagraph();
                continue;
            }
            parseIndex = 0;
            MarkupElement elements = parseMarkup(currentParagraph);

            StringBuilder result = new StringBuilder();
            new Paragraph(List.of(elements)).toHtml(result);
            out.write(result.toString() + "\n");
            
            currentParagraph = readParagraph();
        }

        in.close();
        out.close();


    }


    private static String readParagraph() throws IOException {
        StringBuilder paragraph = new StringBuilder();
        while(in.hasNextLine()) {

            String line = in.nextLine();
            if(line.length() > 1) {
                paragraph.append(line + "\n");
            } else {
                break;
            }
        }
        if(paragraph.length() > 1) {
            paragraph.deleteCharAt(paragraph.length() - 1);
        }
        return paragraph.toString();
    }

    private static class Token {
        enum Type {
            TEXT,
            STRONG,
            EMPHASIS,
            CODE,
            STRIKEOUT
        }

        Type type;
        String text;

        public Token(Type type, String text) {
            this.type = type;
            this.text = text;
        }
    }
}
