import java.util.*;

public class Sum {
    public static void main(String[] args) {

        int sum = 0;

        for(int i = 0; i < args.length; ++i) {
            String temp = "";
            for(int q = args[i].length() - 1; q >= -1; --q) {
                if( q == -1 || Character.isWhitespace(args[i].charAt(q)) ) {
                    if(temp.length() == 0) continue;
                    sum += Integer.parseInt(temp);
                    temp = "";
                    continue;
                }
                temp = args[i].charAt(q) + temp;
            }
        }
       

        System.out.println(sum);

    }

}
