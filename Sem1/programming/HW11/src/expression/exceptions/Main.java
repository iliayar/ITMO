package expression.exceptions;

import expression.exceptions.ExpressionParser;

public class Main {

    public static void main(String[] args) {

        System.out.println(new ExpressionParser().parse("1**1000000000**1000000000**1000000000**1000000000**1000000000").evaluate(0));


    }

}
