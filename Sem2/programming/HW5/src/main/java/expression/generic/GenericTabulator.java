package expression.generic;

import java.math.BigInteger;

import expression.*;
import expression.parser.ExpressionParser;

public class GenericTabulator implements Tabulator {

	@Override
	public Object[][][] tabulate(String mode, String expression, int x1, int x2, int y1, int y2, int z1, int z2)
			throws Exception {

//        TripleExpression e;
//        Calculator calc;
        if(mode.equals( "i")) {
            return getTable(new ExpressionParser<Integer>(new IntegerCalculator()), expression, x1, y1, z1, x2, y2, z2);
        }
        else if(mode.equals("d")) {
            return getTable(new ExpressionParser<Double>(new DoubleCalculator()), expression, x1, y1, z1, x2, y2, z2);
        }
        else if(mode.equals("bi")){
            return getTable(new ExpressionParser<BigInteger>(new BigIntegerCalculator()), expression, x1, y1, z1, x2, y2, z2);
        }
        else if(mode.equals("l")) {
            return getTable(new ExpressionParser<Long>(new LongCalculator(false)), expression, x1, y1, z1, x2, y2, z2);
         }
        else if(mode.equals("s")) {
            return getTable(new ExpressionParser<Short>(new ShortCalculator(false)), expression, x1, y1, z1, x2, y2, z2);
        }
        else if(mode.equals("u")) {
            return getTable(new ExpressionParser<Integer>(new IntegerCalculator(false)), expression, x1, y1, z1, x2, y2, z2);
        } else {
            throw new Exception("Unknown number format");
        }
	}

    private <T extends Number> Object[][][] getTable(ExpressionParser<T> parser, String expression, int x1, int y1, int z1, int x2, int y2, int z2) {
        CommonExpression<T> e = parser.parse(expression);
        Object[][][] table = new Object[x2 - x1 + 1][y2 - y1 + 1][z2 - z1 + 1];
        for (int x = 0; x < table.length; ++x) {
            for(int y = 0; y < table[x].length; ++y) {
                for(int z = 0; z < table[x][y].length; ++z) {
                    table[x][y][z] = e.evaluate(parser.calc.valueOf(x1 + x), parser.calc.valueOf(y1 + y), parser.calc.valueOf(z1 + z));
                }
            }
        }
        return table;
    }
}
