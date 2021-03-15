package info.kgeorgiy.ja.yaroshevskij.arrayset;

import java.util.Comparator;
import java.util.List;
import java.util.NavigableSet;

public class ArrayTest {

    public static void main(String[] args) {

        List<Integer> data = List.of(2, 4, 6, 8, 10, 12, 14, 16, 18, 20);
        NavigableSet<Integer> set = (new ArraySet<>(data)).descendingSet();
        // Integer r = set.floor(11);

        for(Integer n : set.subSet(21, false, 10, false)) {
            System.out.print(n);
            System.out.print(" ");
        }
        System.out.println();

        // System.out.println(r);
        // System.out.println(Comparator.<Integer>naturalOrder().reversed().compare(3, 4));
    }
}
