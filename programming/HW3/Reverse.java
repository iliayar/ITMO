import java.io.IOException;
// import java.util.Arrays;

public class Reverse {

    public static void main(String[] args) {

        Scanner inp = new Scanner(System.in);

        StringBuffer a = new StringBuffer("");
        try {
             while(inp.hasNextLine()) {
                // System.err.println("Test");
                a.append(inp.nextLine());
                a.append('\n');  
             }
        } catch (IOException e) {}

        int numBegin = 0;
        int numLen = 0;
        for(int q = a.length() - 3; q >= -1; --q) {
            if(q == -1 || Character.isWhitespace(a.charAt(q)) ) {
                if(q != -1 && numLen == 0 && a.charAt(q) == '\n') {
                    System.out.print("\n");
                    continue;
                }
                if(numLen == 0) continue;
                
                System.out.print(a.substring(numBegin,numBegin + numLen) + " ");
                if(q != -1 && a.charAt(q) == '\n') {
                    System.out.print("\n");
                }
                numBegin = 0;
                numLen = 0;
                continue;
            }
            numBegin = q;
            numLen++;
        }

        System.out.print("\n");

        try{
            inp.close();
        } catch (IOException e) {}
    }

}
