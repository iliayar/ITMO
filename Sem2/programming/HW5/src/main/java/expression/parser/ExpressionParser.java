package expression.parser;

import expression.*;
import expression.parser.*;
import expression.exceptions.*;

public class ExpressionParser<T extends Number> extends BaseParser {

    private String parsedOperation = null;
    public Calculator<T> calc;

    public ExpressionParser(Calculator<T> calc) {
        this.calc = calc;
    }


    public ExpressionParser(ExpressionSource src, Calculator<T> calc) {
        this.src = src;
        this.calc = calc;
        nextChar();
    }


    @Override
    public CommonExpression<T> parse(String src) {
        this.src = new StringSource(src);
        nextChar();
        CommonExpression<T> res = parseExpression();
        if (ch != '\0') {
            throw error("End of expression expected");
        }
        return res;
    }

    private T parseNumber(boolean isInverse) {
        StringBuilder parsedNum = new StringBuilder(isInverse ? "-" : "");
        while (between('0','9') || in(".")) {
            parsedNum.append(ch);
            nextChar();
        }
        T res = null;
        try {
            res = calc.parseNumber(parsedNum.toString());
        } catch (NumberFormatException e) {
            throw error("Wrong Number: " + parsedNum.toString());
        }
        return res;
    }

    private void parseOperation() {
        if (parsedOperation != null) {
            return;
        }
        if (in("+-*/")) {
            char c = ch;
            nextChar();
            parsedOperation = Character.toString(c);
        } else if (test('m')) {
            if(test('i')) {
                expect('n');
                parsedOperation = "min";
            } else if(test('a')) {
                expect('x');
                parsedOperation = "max";
            }
        } else {
             throw operatorError();
        }

    }

    private boolean testOperation(String expect) {
        if (in("*+-m/")) {
            parseOperation();
        }
        if(parsedOperation != null && parsedOperation.equals(expect)) {
            parsedOperation = null;
            return true;
        } else {
            return false;
        }
    }

    private CommonExpression<T> parseOperand() {
        if (test('(')) {
            CommonExpression<T> expr = parseExpression();
            expect(')');
            return  expr;
        } else if (between('0', '9')) {
            T n = parseNumber(false);
            return new Const<T>(n);
        } else if (test('x')) {
            return new Variable<T>("x");
        } else if (test('y')) {
            return new Variable<T>("y");
        } else if (test('z')) {
            return new Variable<T>("z");
        } else if (test('-')) {
            skipWhitespace();
            if (between('0','9')) {
                T n = parseNumber(true);
                return new Const<T>(n);
            } else if (test('(')) {
                CommonExpression<T> expr = parseExpression();
                expect(')');
                return new Negate<T>(expr, calc);
            } else {
                return new Negate<T>(parseOperand(), calc);
            }
        } else if(test('c')) {
            expect("ount");
            skipWhitespace();
            if(test('(')) {
                CommonExpression<T> expr = parseExpression();
                expect(')');
                return new Count<T>(expr, calc);
            } else {
                return new Count<T>(parseOperand(), calc);
            }
        }
        throw operandError();
    }

    public CommonExpression<T> parseExpression() {
        return parse3PriorExpression();
    }

    private  CommonExpression<T> parse3PriorExpression() {

        skipWhitespace();

        CommonExpression<T> firstOperand = null;

        firstOperand = parse2PriorExpression();
        skipWhitespace();
        while (true) {
            if (testOperation("min")) {
                skipWhitespace();
                firstOperand = new Min<T>(firstOperand, parse2PriorExpression(), calc);
            } else if (testOperation("max")) {
                skipWhitespace();
                firstOperand = new Max<T>(firstOperand, parse2PriorExpression(), calc);
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    private CommonExpression<T> parse1PriorExpression() {

        skipWhitespace();

        CommonExpression<T> firstOperand = parseOperand();
        skipWhitespace();
        while (true) {
            if (testOperation("*")) {
                skipWhitespace();
                firstOperand = new Multiply<T>(firstOperand, parseOperand(), calc);
            } else if (testOperation("/")) {
                skipWhitespace();
                firstOperand = new Divide<T>(firstOperand, parseOperand(), calc);
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    private CommonExpression<T> parse2PriorExpression() {

        skipWhitespace();
        CommonExpression<T> firstOperand = parse1PriorExpression();
        skipWhitespace();
        while (true) {
            if (testOperation("+")) {
                skipWhitespace();
                firstOperand = new Add<T>(firstOperand, parse1PriorExpression(), calc);
            } else if (testOperation("-")) {
                skipWhitespace();
                firstOperand = new Subtract<T>(firstOperand, parse1PriorExpression(), calc);
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    @Override
    protected void expect(final char c) {
        if (ch != c) {
            if (c == ')') {
                throw bracketError();
            }
            if (ch == ')') {
                throw bracketError();
            }
            throw error("Expected \'" + c + "\'");
        }
        nextChar();
    }


    private MissingOperandException operandError() {
        return new MissingOperandException(error(""));
    }

    private MissingOperatorException operatorError() {
        return new MissingOperatorException(error(""));
    }

    private MissingBracketException bracketError() {
        return new MissingBracketException(error(""));
    }

    private void skipWhitespace() {
        while (test(' ') || test('\r') || test('\n') || test('\t')) {
            // skip
        }
    }

}
