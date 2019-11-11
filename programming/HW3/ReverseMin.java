import java.util.Arrays;
import java.io.IOException;

public class ReverseMin {
    final static int START_LENGTH = 2<<20;

    static int lineSize[];
    static int lineMin[];
    static int colMin[];

    public static void doubleLineArrays() {
        int c[] = new int[lineSize.length*2];
        int d[] = new int[lineMin.length*2];
        
        System.arraycopy(lineSize, 0, c, 0, lineSize.length);
        lineSize = c;
        System.arraycopy(lineMin, 0, d, 0, lineMin.length);
        lineMin = d;
    }


    public static void doubleColArrays() {
        int c[] = new int[colMin.length*2];

        Arrays.fill(c,Integer.MAX_VALUE);
        System.arraycopy(colMin, 0, c, 0, colMin.length);
        colMin = c;

    }

    public static void main(String[] args) {
        Scanner inp = new Scanner(System.in);

        colMin = new int[START_LENGTH];
        Arrays.fill(colMin,Integer.MAX_VALUE);
        lineSize = new int[START_LENGTH];
        lineMin = new int[START_LENGTH];
        int lineCnt = 0;
        try {
            // System.out.println(inp.hasNextLine());
            while(inp.hasNextLine()) {
                if(lineCnt >= lineMin.length) {
                    // lineMin = Arrays.copyOf(lineMin, lineMin.length*2);
                    // lineSize = Arrays.copyOf(lineSize, lineSize.length*2);
                    doubleLineArrays();
                }
                String numsStr = inp.nextLine();

                int numsCnt = 0;
                int curLineMin = Integer.MAX_VALUE;

                Scanner lineScanner = new Scanner(numsStr);
                while(lineScanner.hasNextInt()) {
                    int t = lineScanner.nextInt();

                    curLineMin = min(curLineMin, t);
                    if(colMin.length <= numsCnt) {
                        // colMin = Arrays.copyOf(colMin,colMin.length + 1);
                        // colMin[colMin.length - 1] = Integer.MAX_VALUE;
                        doubleColArrays();
                    }
                    colMin[numsCnt] = min(t, colMin[numsCnt]);
                    numsCnt++;
                }
                lineSize[lineCnt] = numsCnt;
                lineMin[lineCnt] = curLineMin;

                lineCnt++;
            }
        } catch(IOException e) {
        }

        for(int i = 0; i < lineCnt; ++i) {
            for(int j = 0; j < lineSize[i]; ++j) {
                System.out.print(min(lineMin[i], colMin[j])+ " ");
            }
            if(i != lineCnt - 1) {
                System.out.println();
            }
        }
        
        try {
            inp.close();
        } catch(Exception e) {}
        
    }
    static int min(int a, int b){
        if(a < b) {
            return a;
        }
        return b;
    }

}
