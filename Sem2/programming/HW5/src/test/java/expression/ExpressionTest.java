package expression;


import org.junit.Test;

import expression.*;

import static org.junit.Assert.*;

import java.math.BigInteger;

public class ExpressionTest {


    @Test
    public void CalculatorTest() {
        Calculator calc = new IntegerCalculator();
        assertEquals(Integer.valueOf(25), calc.add(Integer.valueOf(10), Integer.valueOf(15)));
        assertEquals(Integer.valueOf(150), calc.multiply(Integer.valueOf(10), Integer.valueOf(15)));
        assertEquals(Integer.valueOf(-5), calc.subtract(Integer.valueOf(10), Integer.valueOf(15)));
        assertEquals(Integer.valueOf(2), calc.divide(Integer.valueOf(30), Integer.valueOf(15)));

        calc = new DoubleCalculator();
        assertEquals(Double.valueOf(2.5), calc.add(Double.valueOf(1.0), Double.valueOf(1.5)));
        assertEquals(Double.valueOf(1.5), calc.multiply(Double.valueOf(0.1), Double.valueOf(15)));
        assertEquals(Double.valueOf(-1.5), calc.subtract(Double.valueOf(0.5), Double.valueOf(2)));
        assertEquals(Double.valueOf(0.5), calc.divide(Double.valueOf(15), Double.valueOf(30)));

        calc = new BigIntegerCalculator();
        assertEquals(BigInteger.valueOf(500000).multiply(BigInteger.valueOf(100000)), calc.multiply(BigInteger.valueOf(5000), BigInteger.valueOf(10000000)));
        assertEquals(BigInteger.valueOf(25), calc.add(BigInteger.valueOf(10), BigInteger.valueOf(15)));
        assertEquals(BigInteger.valueOf(1337), calc.subtract(BigInteger.valueOf(2000), BigInteger.valueOf(663)));
        assertEquals(BigInteger.valueOf(2), calc.divide(BigInteger.valueOf(30), BigInteger.valueOf(15)));
    }


    @Test
    public void ExpressionsTest() {
        Calculator calc = new IntegerCalculator();


        Expression e2 = new Add(new Subtract(new Const(Integer.valueOf(15)), new Const(Integer.valueOf(30))),
                               new Multiply(new Variable("x"), new Const(Integer.valueOf(3))));
        Expression e1 = new Subtract<Integer>(new Const<Integer>(Integer.valueOf(30)), new Variable<Integer>("x"), calc);
        Expression e = new Variable<Integer>("x");

        assertEquals(e.evaluate(10), Integer.valueOf(10));
        assertEquals(e.evaluate(0), Integer.valueOf(0));
        assertEquals(e1.evaluate(Integer.valueOf(0)), Integer.valueOf(Integer.valueOf(30)));
    }
}
