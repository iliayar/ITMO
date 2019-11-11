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
        NONE,
    }


    static Scanner in;

    static String currentParagraph;


    private static int symbolLength(MarkupSymbol symbol) {
        switch (symbol) {
            case STRIKEOUT:
            case STRONG_STAR:
            case STRONG_UNDERLINE:
                return 2;
            case EMPHASIS_STAR:
            case EMPHASIS_UNDERLINE:
            case CODE:
                return 1;
            case NONE:
                return 0;
        }
        return 0;
    }

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
 
        return MarkupSymbol.NONE;
    }

    static int parseIndex = 0;

    private static MarkupSymbol findNextSymbol() {
        for(; parseIndex <  currentParagraph.length(); ++parseIndex) {
            if(checkMarkupSymbol(parseIndex) != MarkupSymbol.NONE) {
                return checkMarkupSymbol(parseIndex);
            }
        }
        parseIndex--;
        return MarkupSymbol.NONE;
    }

    private static MarkupElement parseMarkup() {
        ArrayList<MarkupElement> elements = new ArrayList<MarkupElement>();
        
        int startIndex = parseIndex++;
        int textStartIndex = startIndex;

        MarkupSymbol startSymbol = checkMarkupSymbol(parseIndex);
        MarkupSymbol nextSymbol = findNextSymbol();

        while(nextSymbol != MarkupSymbol.NONE) {

            if(nextSymbol != MarkupSymbol.NONE) {
                System.out.println(textStartIndex + " " + parseIndex + " " + symbolLength(nextSymbol) + " ");
                elements.add(new Text(currentParagraph.substring(textStartIndex ,1 + parseIndex - symbolLength(nextSymbol))));
                
                if(nextSymbol == startSymbol) {
                    switch (startSymbol) {
                        case STRONG_STAR:
                        case STRONG_UNDERLINE:
                            return new Strong(elements);
                        case EMPHASIS_STAR:
                        case EMPHASIS_UNDERLINE:
                            return new Emphasis(elements);
                        case CODE:
                            return new Code(elements);
                        case STRIKEOUT:
                            return new Strikeout(elements);
                    }
                }
                elements.add(parseMarkup());
                textStartIndex = parseIndex - 1;
            }

            nextSymbol = findNextSymbol();
        }
        if(textStartIndex < currentParagraph.length()) {
            elements.add(new Text(currentParagraph.substring(textStartIndex)));
        }
        return new Text(elements);
    }
    
    public static void main(String[] args) throws IOException {
        in = new Scanner( new InputStreamReader(
            new FileInputStream(args[0]), "UTF-8"));

        BufferedWriter out = new BufferedWriter(
            new OutputStreamWriter(new FileOutputStream(args[1]), "UTF-8")
        );


        currentParagraph = readParagraph();
        while(currentParagraph.length() > 0) {
            if(currentParagraph.length() <= 1) {
                // currentParagraph = readParagraph();
                continue;
            }
            parseIndex = 0;
            System.out.println("Paragraph: " + currentParagraph);
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
            System.out.println("Line: " + line + " " + Integer.toString(line.length()));
            if(line.length() > 1) {
                paragraph.append(line + '\n');
            } else {
                break;
            }
        }
        return paragraph.toString();
    }
}