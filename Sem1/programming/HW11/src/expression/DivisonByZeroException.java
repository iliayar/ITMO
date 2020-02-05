package expression;

public class DivisonByZeroException  extends  Exception{

    private int a, b;

    public DivisonByZeroException(int a, int b) {
        this.a = a;
        this.b = b;
    }

    @Override
    public String getMessage() {
        return "Divison by zero happens when: " + a + "/" + b;
    }

}
