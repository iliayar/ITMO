package expression;

public class Main {


    private void run(String[] argv) {
        Expression e = new Subtract(
                new Multiply(
                        new Const(2),
                        new Variable("x")
                ),
                new Const(3)
        );
        System.out.println(e.evaluate(5));
        System.out.println(e.toMiniString());
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
