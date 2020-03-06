package search;


public class BinarySearchSpan {

    public static void main(String[] args) {
        new BinarySearchSpan().run(args);
    }


    // Pre: |args| > 1 for all v in a: v - Integer
    // Post: let e = {i in indexes(args[1:]): args[i] = args[0]} l = min(e) r = max(e)
    private void run(String[] args) {

        if (args.length <= 1) {
            System.out.println("0 0");
            return;
        }

        int x = Integer.parseInt(args[0]);

        int[] a = new int[args.length - 1];

        for (int i = 1; i < args.length; ++i) {
            a[i-1] = Integer.parseInt(args[i]);
        }
        int l = upperBound(x, a);
        int r = lowerBound(x, a);

        // Pre: not exist v in a: v = x
        // Post: insertion position
        if(l >= a.length || a[l] != x) {
            r = l - 1;
        }


        System.out.println(l + " " + (r - l + 1));

    }



    // Pre:  let I = [0 : |a|) and forall j,k in I: j > k a[j] <= a[k]
    // Post: i: i = max({j in I: a[j] <= x})
    private int lowerBound(int x, int[] a) {

        // Pre: |a| > 0
        // Post: l = 0 and r = |a|
        int l = 0, r = a.length;

        // let a[r] = -INF
        // inv: a[r'] < x <= a[l'] and |[l' : r')| > 1 and |[l' : r')| < |[l : r)|
        // Pre: l = 0 and r = |a| and forall j,k in I: j > k a[j] <= a[k]
        // Post: |[l' : r')| = 1 and l = max({j in [0 : |a|): a[j] >= x}) Д-во от обратного a[l+1 = r] >= x
        while (r - l > 1) {

            // Pre: |[l' : r')| > 1
            // Post l < m < r
            int m = (l + r)/2;

            // Pre: l < m < r and a[r] <= x <= a[l]
            // Post: |[l' : r')| < |[l : r)| and  a[r'] <= x <= a[l']
            if (x <= a[m]) {

                // Pre: l < m < r and x <= a[m]
                // Post: |[l' : r)| < |[l : r)| and a[l'] >= x
                l = m;
            } else {

                // Pre: l < m < r in [l : r) and x > a[m]
                // Post: |[l : r')| < |[l : r)| and a[r'] < x
                r = m;
            }
        }

        return l;
    }




    // Pre: let I = [0 : |a|) and forall j,k in I: j > k a[j] <= a[k]
    // Post: i: i = min({j in I: a[j] <= x})
    private int upperBound(int x, int[] a) {

        // Pre: |a| > 0
        // Post: l = 0 and r = max(I) + 1 and [l : r) = I
        int l = 0, r = a.length;


        // inv: a[r'] <= x <= a[l'] and |[l' : r')| > 1 and |[l' : r')| < |[l : r)|
        // Pre: l = 0 and r = |a| and forall j,k in I: j > k a[j] <= a[k]
        // Post: |[l' : r')| = 1 and
        //     ( (exists j in I: a[j] > x and l' = max({j in I: a[j] > x}) Д-во от обратного a[l+1 = r] > x or
        //     (not exists j in I: a[j] >= x and l' = 0) Д-во ни разу не выполнится x < a[m]
        while(r - l > 1) {

            // Pre: |[l' : r')| > 1
            // Post l < m < r
            int m = (l + r)/2;

            // Pre: l < m < r and a[r] <= x <= a[l]
            // Post: |[l' : r')| < |[l : r)| and  a[r'] <= x <= a[l']
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
        //     ( (exists j in I: a[j] > x and l = max({j in I: a[j] > x})) or
        //     (not exists j in I: a[j] >= x and l = 0)
        // Post: l' = min({j in i: a[j] <= x})
        if(a[l] > x) {

            // Pre:l = max({j in I: a[j] > x}) and
            //     forall j in I: j > l a[j] < a[l] |=> not a[j] > x |=> a[j] <= x
            // Post: l = min({j in I: a[j] <= x})
            l += 1;
        }

        return l;
    }
}
