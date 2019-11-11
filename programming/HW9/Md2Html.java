import java.io.*;
import java.util.*;

import markup.*;

public class Md2Html {

    enum MarkupSymbol {
        STRONG_UNDERLINE,
        STRONG_STAR,
        EMPHASIS_UNDERLINE,
        EMPHASIS_STAR,
        STRIKEOUT,
        CODE,
        TEXT,
        NONE
    }


    static Scanner in;

    static String currentParagraph;

    private static MarkupSymbol checkMarkupSymbol(int index) {
        if(index > 0 && currentParagraph.charAt(index - 1) == currentParagraph.charAt(index) &&
        (index <= 1 || (index > 1 && currentParagraph.charAt(index - 2) != '\\'))) {
            switch (currentParagraph.charAt(index)){
                case '*':
                    return MarkupSymbol.STRONG_STAR;
                case '_':
                    return MarkupSymbol.STRONG_UNDERLINE;
                case '-':
                    return MarkupSymbol.STRIKEOUT;
            }
        }

        if( index == 0 || (index >= 0 && currentParagraph.charAt(index - 1) != '\\')) {
            switch (currentParagraph.charAt(index)){
                case '*':
                    return MarkupSymbol.EMPHASIS_STAR;
                case '_':
                    return MarkupSymbol.EMPHASIS_UNDERLINE;
                case '`':
                    return MarkupSymbol.CODE;
            }
        } 
 
        return MarkupSymbol.TEXT;
    }

    static int parseIndex = 0;

    private static int findNext() {

    }

    private static MarkupElement parseMarkup() {

    }
    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );


        currentParagraph = readParagraph();
        while(currentParagraph.length() > 0) {
            if(currentParagraph.length() == 1) {
                continue;
            }
            parseIndex = 0;
            // System.out.println("Paragraph: " + currentParagraph);
            MarkupElement elements = parseMarkup();

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
            if(line.length() > 0) {
                paragraph.append(line + "\n");
            } else {
                break;
            }
        }
        return paragraph.toString();
    }
}