package info.kgeorgiy.ja.yaroshevskij.arrayset;

import java.util.AbstractList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

class ReversibleList<T> extends AbstractList<T> {

    private final List<T> data;
    private final boolean reversed;
    private final Comparator<? super T> comparator;

    public ReversibleList(List<T> data, Comparator<? super T> comparator) {
        this(data, comparator, false);
    }

    public ReversibleList(List<T> data, Comparator<? super T> comparator, boolean reversed) {
        this.data = data;
        this.reversed = reversed;
        this.comparator = comparator;
    }

    @Override
    public T get(int i) {
        if (!checkIndex(getIndex(i))) {
            return null;
        }
        return data.get(getIndex(i));
    }

    @Override
    public int size() {
        return data.size();
    }

    public ReversibleList<T> reverse() {
        return new ReversibleList<>(data, comparator, !reversed);
    }

    public T search(T key, boolean inclusive, boolean least) {
        int res = searchIndex(key, inclusive, least);
        if (!checkIndex(res)) {
            return null;
        }
        return data.get(res);
    }

    public ReversibleList<T> subArray(T left, boolean leftInclusive, T right, boolean rightInclusive) {
        if (reversed) {
            T t = left;
            left = right;
            right = t;
        }
        if (reversed) {
            boolean t = leftInclusive;
            leftInclusive = rightInclusive;
            rightInclusive = t;
        }
        if (left != null && right != null && comparator.compare(left, right) > 0) {
            throw new IllegalArgumentException("Invalid elements range");
        }

        int leftIndex = left == null ? 0 : searchIndex(left, leftInclusive, !reversed);
        int rightIndex = right == null ? data.size() : searchIndex(right, rightInclusive, reversed);
        if (rightIndex < data.size()) {
            rightIndex += 1;
        }

        if (leftIndex > rightIndex) {
            leftIndex = rightIndex;
        }
        return new ReversibleList<>(data.subList(leftIndex, rightIndex), comparator, reversed);
    }

    public Comparator<? super T> getComparator() {
        if (reversed) {
            return comparator.reversed();
        } else {
            return comparator;
        }
    }

    private int searchIndex(T key, boolean inclusive, boolean fromRight) {
        int i = Collections.binarySearch(data, key, comparator);
        int shiftNotFound = (reversed ^ fromRight) ? 0 : -1;
        int shiftFound = 0;
        if (!inclusive) {
            shiftFound = (reversed ^ fromRight) ? 1 : -1;
        }

        if (i < 0) {
            return (-i - 1) + shiftNotFound;
        } else {
            return i + shiftFound;
        }
    }

    private boolean checkIndex(int i) {
        return i >= 0 && i < data.size();
    }

    private int getIndex(int i) {
        if (reversed) {
            return data.size() - i - 1;
        } else {
            return i;
        }
    }

    @SuppressWarnings("unchecked")
    @Override
    public boolean contains(Object key) {
        return Collections.binarySearch(data, (T) key, comparator) >= 0;
    }

}
