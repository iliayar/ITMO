import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Scanner;

public class BinarySearch {


    public static void main(String[] args) {
        new BinarySearch().run(args);
    }


    private void run(String[] args) {


        int x = Integer.parseInt(args[0]);

        int[] a = new int[args.length - 1];

        for(int i = 1; i < args.length; ++i) {
            a[i - 1] = Integer.parseInt(args[i]);
        }

        int i = bSearch(x,a);
        System.out.println(i + " which is " + a[i]);
    }

    private int bSearch(int x, int[] a) {

        int l = 0, r = a.length;

        while(r - l > 1) {
            int m = (l + r)/2;

            if(x < a[m]) {
                l = m;
            } else {
                r = m;
            }

        }

        // TODO: case when a[i] <= x doesn't exists

        if(a.length > 1 && l == 0 && a[l+1] != x) {
            l += 0;
        } else {
            l += 1;
        }

        return l;
    }

}
