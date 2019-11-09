import java.util.Arrays;

public class IntList{
    static final int START_LENGHT = 1 << 5;

    private int arr[];
    private int length;
    public IntList() {
        this.arr = new int[START_LENGHT];
        this.length = 0;
    }
    public void add(int item) {
        if(length >= arr.length) {
            doubleArr();
        }
        arr[length] = item;
        length++;
    }
    public int get(int index) throws ArrayIndexOutOfBoundsException {
        if(index < length) {
            return arr[index];
        }
        throw new ArrayIndexOutOfBoundsException();
    }
    public int length() {
        return length;
    }
    private void doubleArr() {
        arr = Arrays.copyOf(arr, arr.length * 2);
    }

}