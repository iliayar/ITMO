package search;


public class BinarySearchSpan {

    public static void main(String[] args) {
        new BinarySearchSpan().run(args);
    }

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

        if(l >= a.length) {
            r = l - 1;
        } else if(a[l] != x) {
            r = l - 1;
        }


        System.out.println(l + " " + (r - l + 1));

    }



    private int lowerBound(int x, int[] a) {
        if (a[a.length - 1] > x) {
            return a.length;
        }

        int l = 0, r = a.length;

        while (r - l > 1) {
            int m = (l + r)/2;
            if (x <= a[m]) {
                l = m;
            } else {
                r = m;
            }
        }

        return l;
    }



    private int upperBound(int x, int [] a) {
        if (a[a.length - 1] > x) {
            return a.length;
        }

        int l = 0, r = a.length;

        while (r - l > 1) {
            int m = (l + r)/2;
            if (x < a[m]) {
                l = m;
            } else {
                r = m;
            }
        }

        if (a[l] > x) {
            l += 1;
        }

        return l;
    }

}
