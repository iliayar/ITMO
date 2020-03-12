package expression;

public class Main {


    private void run(String[] argv) {
        int x = Integer.parseInt(argv[0]);

        String t;

        CommonExpression expr = new Add(
            new Multiply(
                new Variable("x"),
                new Subtract(
                    new Variable("x"), 
                    new Const(2)
                )
            ), 
            new Const(1)
        );

        try {
            System.out.println(expr.evaluate(x));
        } catch (Exception e) {
            System.out.println(e.getMessage());
        }
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
