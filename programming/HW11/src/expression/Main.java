package expression;

public class Main {


    private void run(String[] argv) {
        Expression e = new Multiply(new Const(1), new Divide(new Variable("x"), new Const(2)));
        System.out.println(e.evaluate(2));
        System.out.println(e.toMiniString());


        System.out.println(e.hashCode());
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
