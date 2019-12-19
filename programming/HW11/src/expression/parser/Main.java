package expression.parser;

public class Main {

    private void run(String args[]) {
        String exprString = "(((z << 2) + 3) + 9 / z) * (reverse (6 << y))";
        expression.TripleExpression expr = new ExpressionParser().parse(exprString);

        System.out.println(6 << -1);

        System.out.println("Input: " + exprString);
        System.out.println(expr.toString());
//        System.out.println(exprString.length());
        System.out.println(expr.toMiniString());
        System.out.println(expr.evaluate(1, 1, 1));
    }

    static public void main(String args[]) {
        new Main().run(args);
    }
}
