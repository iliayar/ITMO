package expression.generic;

import java.math.BigInteger;

import expression.*;
import expression.exceptions.ExpressionParser;

public class GenericTabulator implements Tabulator {

	@Override
	public Object[][][] tabulate(String mode, String expression, int x1, int x2, int y1, int y2, int z1, int z2)
			throws Exception {
        Object[][][] table = new Object[x2 - x1 + 1][y2 - y1 + 1][z2 - z1 + 1];

        TripleExpression e;
        Calculator calc;
        switch(mode) {
        case "i":
            calc = new IntegerCalculator();
            e = new ExpressionParser<Integer>(calc).parse(expression);
            break;
        case "d":
            calc = new DoubleCalculator();
            e = new ExpressionParser<Double>(calc).parse(expression);
            break;
        case "bi":
            calc = new BigIntegerCalculator();
            e = new ExpressionParser<BigInteger>(calc).parse(expression);
            break;
        case "l":
            calc = new LongCalculator(false);
            e = new ExpressionParser<Long>(calc).parse(expression);
            break;
        case "s":
            calc = new ShortCalculator(false);
            e = new ExpressionParser<Short>(calc).parse(expression);
            break;
        case "u":
            calc = new IntegerCalculator(false);
            e = new ExpressionParser<Integer>(calc).parse(expression);
            break;
        default:
            throw new Exception("Unknown number format");
        }

        for (int x = 0; x < table.length; ++x) {
            for(int y = 0; y < table[x].length; ++y) {
                for(int z = 0; z < table[x][y].length; ++z) {
                    table[x][y][z] = e.evaluate(calc.valueOf(x1 + x), calc.valueOf(y1 + y), calc.valueOf(z1 + z));
                }
            }
        }
		return table;
	}
}
