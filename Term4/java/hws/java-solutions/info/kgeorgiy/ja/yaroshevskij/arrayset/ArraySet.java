package info.kgeorgiy.ja.yaroshevskij.arrayset;

import java.util.AbstractSet;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.NavigableSet;
import java.util.NoSuchElementException;
import java.util.SortedSet;

public class ArraySet<T> extends AbstractSet<T> implements NavigableSet<T> {

    private final ReversibleList<T> list;
    private final boolean isNaturalComparator;

    public ArraySet() {
        this(List.of());
    }

    public ArraySet(Comparator<? super T> comparator) {
        this(List.of(), comparator);
    }

    public ArraySet(Collection<? extends T> collection) {
        this(collection, null);
    }

    public ArraySet(Collection<? extends T> collection, Comparator<? super T> comparator) {
        if (comparator == null) {
            comparator = createComparator();
            isNaturalComparator = true;
        } else {
            isNaturalComparator = false;
        }

        // :NOTE: use TreeSet
        List<T> data = new ArrayList<>(collection);
        data.sort(comparator);
        List<T> uniqueData = new ArrayList<>();
        if (data.size() != 0) {
            uniqueData.add(data.get(0));
        }
        for (int i = 1; i < data.size(); ++i) {
            if (comparator.compare(data.get(i - 1), data.get(i)) != 0) {
                uniqueData.add(data.get(i));
            }
        }
        list = new ReversibleList<>(Collections.unmodifiableList(uniqueData), comparator, false);
    }

    private ArraySet(ReversibleList<T> list, boolean isNaturalComparator) {
        this.list = list;
        this.isNaturalComparator = isNaturalComparator;
    }

    @Override
    public Comparator<? super T> comparator() {
        if (isNaturalComparator) {
            return null;
        } else {
            return list.getComparator();
        }
    }

    @Override
    public T first() {
        T res = list.get(0);
        if (res == null) {
            throw new NoSuchElementException("Cannot get first element of empty set");
        }
        return res;
    }

    @Override
    public T last() {
        T res = list.get(list.size() - 1);
        if (res == null) {
            throw new NoSuchElementException("Cannot get first element of empty set");
        }
        return res;
    }

    @Override
    public Iterator<T> descendingIterator() {
        return list.reverse().iterator();
    }

    @Override
    public NavigableSet<T> descendingSet() {
        return new ArraySet<>(list.reverse(), isNaturalComparator);
    }

    @Override
    public T ceiling(T key) {
        return list.search(key, true, true);
    }

    @Override
    public T floor(T key) {
        return list.search(key, true, false);
    }

    @Override
    public T higher(T key) {
        return list.search(key, false, true);
    }

    @Override
    public T lower(T key) {
        return list.search(key, false, false);
    }

    @Override
    public SortedSet<T> headSet(T right) {
        return headSet(right, false);
    }

    @Override
    public NavigableSet<T> headSet(T right, boolean rightInclusive) {
        return new ArraySet<>(list.subArray(null, false, right, rightInclusive), isNaturalComparator);
    }

    @Override
    public SortedSet<T> subSet(T left, T right) {
        return subSet(left, true, right, false);
    }

    @Override
    public NavigableSet<T> subSet(T left, boolean leftInclusive, T right, boolean rightInclusive) {
        return new ArraySet<>(list.subArray(left, leftInclusive, right, rightInclusive), isNaturalComparator);
    }

    @Override
    public SortedSet<T> tailSet(T left) {
        return tailSet(left, true);
    }

    @Override
    public NavigableSet<T> tailSet(T left, boolean leftInclusive) {
        return new ArraySet<>(list.subArray(left, leftInclusive, null, false), isNaturalComparator);
    }

    @Override
    public T pollFirst() {
        throw new UnsupportedOperationException("ArraySet is immutable");
    }

    @Override
    public T pollLast() {
        throw new UnsupportedOperationException("ArraySet is immutable");
    }

    @Override
    public Iterator<T> iterator() {
        return list.iterator();
    }

    @Override
    public int size() {
        return list.size();
    }

    @Override
    public boolean contains(Object elem) {
        return list.contains(elem);
    }

    // :NOTE: unchecked cast
    @SuppressWarnings("unchecked")
    private Comparator<T> createComparator() {
        return (Comparator<T>) Comparator.naturalOrder();
    }
}
