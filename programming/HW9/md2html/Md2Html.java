package md2html;

import java.io.*;
import java.util.*;

public class Md2Html {

    static Scanner in;

    static boolean EOF = false;


    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );


        
        while(!EOF) {
            String currentParagraph = readParagraph();

            if(currentParagraph.length() <= 1) {
                continue;
            }
            
            StringBuilder result = new StringBuilder();
            new MarkdownParser(currentParagraph).genHtml(result);
            // System.err.println("HTML: " + result.toString() + "\n");
//            out.write("Paragraph: " + currentParagraph + "\n");
//            out.write("Result: " + result.toString() + "\n");
//            out.write("\n");
            out.write(result.toString() + "\n");
            // currentParagraph = readParagraph();

        }

        EOF = false;

        in.close();
        out.close();


    }


    private static String readParagraph() throws IOException {
        StringBuilder paragraph = new StringBuilder();
        while(in.hasNextLine()) {

            String line = in.nextLine();
            if(line.length() > 0) {
                paragraph.append(line + "\n");
            } else {
                break;
            }
        }
        // System.err.println("Paragraph: " + paragraph);

        if(paragraph.length() > 0) {
            paragraph.deleteCharAt(paragraph.length() - 1);
        }
        if(!in.hasNextLine() && paragraph.length() == 0) {
            EOF = true;
        }

        return paragraph.toString();
    }

   
}
