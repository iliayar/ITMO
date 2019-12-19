package expression.parser;

import java.math.BigInteger;

public class Main {

    private void run(String args[]) {
        String exprString = "((((-1273988855) - ((697355327) * ((1751609598) - (-820624248)))) * (((((z) << ((-448605695))) - (-647942712)) - ((((1761069089) + (944742580)) * (-1422254713)) / (z))) * (reverse ((digits (2065523746)) << (y))))))" ;
        expression.CommonExpression expr = new ExpressionParser().parse(exprString);

//        System.out.println(6 << Long.valueOf(-1));
//        System.out.println("Integer: " + Integer.MAX_VALUE + " - " + Integer.MIN_VALUE);
//        long num = -1273988855;
//        System.out.println(num + " is Integer " + (num < Integer.MAX_VALUE && num > Integer.MIN_VALUE));

        System.out.println("Input: " + exprString);
        System.out.println(expr.toString());
//        System.out.println(exprString.length());
        System.out.println(expr.toMiniString());
        System.out.println(expr.evaluate(BigInteger.valueOf(393872827), BigInteger.valueOf(1849657116), BigInteger.valueOf(-1580643101)));
    }

    static public void main(String args[]) {
        new Main().run(args);
    }
}
