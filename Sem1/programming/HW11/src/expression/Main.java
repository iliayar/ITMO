package expression;

public class Main {


    private void run(String[] argv) {
        int x = Integer.parseInt(argv[0]);

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

        System.out.println(expr.evaluate(x));
        
    }

    public static void main(String[] argv) {
        new Main().run(argv);
    }

}
