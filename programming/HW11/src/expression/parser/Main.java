package expression.parser;

public class Main {

    private void run(String args[]) {
        String exprString = "(- ((-1) * (-2))) / (((z) * (3)))";
        expression.TripleExpression expr = new ExpressionParser().parse(exprString);

        System.out.println("Input: " + exprString);
        System.out.println(expr.toString());
//        System.out.println(exprString.length());
        System.out.println(expr.toMiniString());
        System.out.println(expr.evaluate(1, -1, -1));
    }

    static public void main(String args[]) {
        new Main().run(args);
    }
}
