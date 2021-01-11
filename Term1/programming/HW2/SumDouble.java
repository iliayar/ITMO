//import java.util.*;

public class SumDouble {
    public static void main(String[] args) {

        double sum = 0;

        for(int i = 0; i < args.length; ++i) {
            int numBegin = -1;
            int numLen = 0;
            for(int q = 0; q <= args[i].length(); ++q) {
                if( q == args[i].length() || Character.isWhitespace(args[i].charAt(q)) ) {
                    if(numLen == 0) {
                        continue;
                    }
                    sum += Double.parseDouble(args[i].substring(numBegin, numBegin + numLen));
                    numBegin = -1;
                    numLen = 0;
                    continue;
                }
                if(numBegin < 0)
                    numBegin = q;
                numLen++;
            }
        }
       

        System.out.println(sum);

    }

}
