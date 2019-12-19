package expression.parser;

public class Main {

    private void run(String args[]) {
        String exprString = "x + y << z" ;
        expression.CommonExpression expr = new ExpressionParser().parse(exprString);

//        System.out.println(6 << Long.valueOf(-1));
        System.out.println("Integer: " + Integer.MAX_VALUE + " - " + Integer.MIN_VALUE);
        long num = 1761069089;
        System.out.println(num + " is Integer " + (num < Integer.MAX_VALUE && num > Integer.MIN_VALUE));

        System.out.println("Input: " + exprString);
        System.out.println(expr.toString());
//        System.out.println(exprString.length());
        System.out.println(expr.toMiniString());
        System.out.println((int)expr.evaluate(0,1,-10));
    }

    static public void main(String args[]) {
        new Main().run(args);
    }
}
