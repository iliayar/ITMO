package expression.generic;

import java.math.BigInteger;

import expression.*;
import expression.exceptions.ExpressionParser;

public class GenericTabulator implements Tabulator {

	@Override
	public Object[][][] tabulate(String mode, String expression, int x1, int x2, int y1, int y2, int z1, int z2)
			throws Exception {
        Object[][][] table = new Object[x2 - x1 + 1][y2 - y1 + 1][z2 - z1 + 1];

//        TripleExpression e;
//        Calculator calc;
        if(mode.equals( "i")) {
            Calculator<Integer> calc = new IntegerCalculator();
            TripleExpression<Integer> e = new ExpressionParser<Integer>(calc).parse(expression);
        }
        else if(mode.equals("d")) {
            Calculator<Double> calc = new DoubleCalculator();
            TripleExpression<Double> e = new ExpressionParser<Double>(calc).parse(expression);
        }
        else if(mode.equals("bi")){
            Calculator<BigInteger> calc = new BigIntegerCalculator();
            TripleExpression<BigInteger> e = new ExpressionParser<BigInteger>(calc).parse(expression);
        }
        else if(mode.equals("l")) {
            Calculator<Long> calc = new LongCalculator(false);
            TripleExpression<Long> e = new ExpressionParser<Long>(calc).parse(expression);
         }
        else if(mode.equals("bi")) {
            Calculator<Short> calc = new ShortCalculator(false);
            TripleExpression<Short> e = new ExpressionParser<Short>(calc).parse(expression);
        }
        else if(mode.equals("u")) {
            getTable(new ExpressionParser<Integer>(new IntegerCalculator(false)), expression, table, x1, y1, z1);
        } else {
            throw new Exception("Unknown number format");
        }

		return table;
	}

    private <T extends Number> void getTable(ExpressionParser<T> parser, String expression, Object[][][] table, int x1, int y1, int z1) {
        TripleExpression<T> e = parser.parse(expression);
        for (int x = 0; x < table.length; ++x) {
            for(int y = 0; y < table[x].length; ++y) {
                for(int z = 0; z < table[x][y].length; ++z) {
                    table[x][y][z] = e.evaluate(parser.calc.valueOf(x1 + x), parser.calc.valueOf(y1 + y), parser.calc.valueOf(z1 + z));
                }
            }
        }
    }
}
