package md2html;

import java.io.*;

public class Md2Html {

    static BufferedReader in;

    static boolean EOF = false;

    public static void test(MutableInteger i) {
        i.inc();
    }
    
    public static void main(String[] args) throws IOException {
        in = new BufferedReader( new InputStreamReader(
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
            new ParagraphParser(currentParagraph).genHtml(result);
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
        while(!EOF) {

            String line = in.readLine();

            if(line == null) {
                EOF = true;
                break;
            }

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

        return paragraph.toString();
    }

   
}
