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

        int i1 = bSearch(x,a);
        int i2 = recBSearch(x, a, 0, a.length);
        System.out.println("Non recursive: a[" + i1 + "] = " + a[i1] + ", Recursive: a[" + i2 + "] = " + a[i2]);
    }

    // Pre: I = [0 : a.length) and exists j in I: a[j] <= x and forall j,k in I: j > k a[j] <= a[k]
    // Post: i: i = min({j in I: a[j] <= x})
    private int bSearch(int x, int[] a) {

        // Pre: a.length > 0
        // Post: l = 0 and r = max(I) + 1 and [l : r) = I
        int l = 0, r = a.length;


        // inv: [l' : r') subset I and a[r'] <= x < a[l']
        // Pre: l = 0 and r = max(I) + 1 and [l : r) = I
        // Post: |[l' : r')| = 1 and
        //     ( (exists j in I: a[j] > x and l' = max({j in I: a[j] > x})) or
        //     (not exists j in I: a[j] > x and l' = 0)
        while(r - l > 1) {

            // Pre: [l : r) subset I
            // Post l < m < r
            int m = (l + r)/2;

            // Pre: l < m < r and a[r] <= x < a[l]
            // Post: |[l' : r')| < |[l : r)| and  a[r'] <= x < a[l']
            if(x < a[m]) {

                // Pre: l < m < r and x < a[m]
                // Post: |[l' : r)| < |[l : r)| and a[l'] > x
                l = m;
            } else {

                // Pre: l < m < r in [l : r) and x >= a[m]
                // Post: |[l : r')| < |[l : r)| and a[r'] <= x
                r = m;
            }

        }

        // Pre:
        // ( (exists j in I: a[j] > x and l = max({j in I: a[j] > x})) or
        // (not exists j in I: a[j] > x and l = 0)
        // Post: l' = min({j in i: a[j] <= x})
        if(a[l] <= x) {

            // Pre: not exists j in I: a[j] > x and l = 0 => forall j in I: a[j] <= x
            // Post: l = min({j in I: a[j] <= x})
            l += 0;
        } else {

            // Pre: l = max({j in I: a[j] > x}) and forall j in I: j > l a[j] < a[l] => not a[j] > x => a[j] <= x
            // Post: l = min({j in I: a[j] <= x})
            l += 1;
        }
        // if(l >= a.length) {
        //     l = a.length - 1;
        // }

        return l;
    }

    private int recBSearch(int x, int[] a, int l, int r) {

        if(r - l <= 1) {
            if(a.length > 1 && l == 0 && a[l+1] != x) {
                l += 0;
            } else {
                l += 1;
            }
            // if(l >= a.length) {
            //     l = a.length - 1;
            // }
            return l;
        }

        int m = (l + r)/2;

        if(x < a[m]) {
            return recBSearch(x, a, m, r);
        } else {
            return recBSearch(x, a, l, m);
        }

    }

}
