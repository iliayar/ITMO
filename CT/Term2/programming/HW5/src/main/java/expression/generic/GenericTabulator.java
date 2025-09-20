package expression.generic;

import java.math.BigInteger;
import java.util.HashMap;

import expression.*;
import expression.parser.ExpressionParser;


public class GenericTabulator implements Tabulator {

	@Override
	public Object[][][] tabulate(String mode, String expression, int x1, int x2, int y1, int y2, int z1, int z2)
			throws Exception {
        final HashMap<String, ExpressionParser<?>> modes = new HashMap<String, ExpressionParser<?>>();
        modes.put("i", new ExpressionParser<Integer>(new IntegerCalculator()));
        modes.put("d", new ExpressionParser<Double>(new DoubleCalculator()));
        modes.put("bi", new ExpressionParser<BigInteger>(new BigIntegerCalculator()));
        modes.put("l", new ExpressionParser<Long>(new LongCalculator(false)));
        modes.put("s", new ExpressionParser<Short>(new ShortCalculator(false)));
        modes.put("u", new ExpressionParser<Integer>(new IntegerCalculator(false)));
        return getTable(modes.get(mode), expression, x1, y1, z1, x2, y2, z2);
	}

    private <T extends Number> Object[][][] getTable(ExpressionParser<T> parser, String expression, int x1, int y1, int z1, int x2, int y2, int z2) {
        CommonExpression<T> expr = parser.parse(expression);
        Object[][][] table = new Object[x2 - x1 + 1][y2 - y1 + 1][z2 - z1 + 1];
        for (int x = 0; x < table.length; ++x) {
            for(int y = 0; y < table[x].length; ++y) {
                for(int z = 0; z < table[x][y].length; ++z) {
                    try {
                        table[x][y][z] = expr.evaluate(parser.calc.valueOf(x1 + x), parser.calc.valueOf(y1 + y), parser.calc.valueOf(z1 + z));
                    } catch(ExpressionException e) {
                        table[x][y][z] = null;
                    }
                }
            }
        }
        return table;
    }
}
