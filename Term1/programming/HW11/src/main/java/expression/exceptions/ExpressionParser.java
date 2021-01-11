package expression.exceptions;

import expression.*;
import expression.parser.BaseParser;
import expression.parser.ExpressionSource;
import expression.parser.ParserException;
import expression.parser.StringSource;

public class ExpressionParser extends BaseParser {

    private String parsedOperation = null;

    public ExpressionParser() {
    }

    public ExpressionParser(ExpressionSource src) {
        this.src = src;
        nextChar();
    }


    @Override
    public CommonExpression parse(String src) {
        this.src = new StringSource(src);
        nextChar();
        CommonExpression res = parseExpression();
        if (ch != '\0') {
            throw error("End of expression expected");
        }
        return res;
    }

    private int parseNumber(boolean isInverse) {
        StringBuilder parsedNum = new StringBuilder(isInverse ? "-" : "");
        while (between('0','9')) {
            parsedNum.append(ch);
            nextChar();
        }
        int res;
        try {
            res = Integer.parseInt(parsedNum.toString());
        } catch (NumberFormatException e) {
            throw error("Wrong Integer: " + parsedNum.toString());
        }
        return res;
    }

    private void parseOperation() {
        if (parsedOperation != null) {
            return;
        }
        if (in("+-*/")) {
            char c = ch;
            if (test('*')) {
                if (test('*')) {
                    parsedOperation = "**";
                    return;
                }
            } else if (test('/')) {
                if (test('/')) {
                    parsedOperation = "//";
                    return;
                }
            } else {
                nextChar();
            }
            parsedOperation = Character.toString(c);
        } else if (test('<')) {
            expect('<');
            parsedOperation = "<<";
        } else if (test('>')) {
            expect('>');
            parsedOperation = ">>";
        } else {
             throw operatorError();
        }

    }

    private boolean testOperation(String expect) {
        if (in("*+-<>/")) {
            parseOperation();
        }
        if(parsedOperation != null && parsedOperation.equals(expect)) {
            parsedOperation = null;
            return true;
        } else {
            return false;
        }
    }

    private CommonExpression parseOperand() {
        if (test('(')) {
            CommonExpression expr = parseExpression();
            expect(')');
            return  expr;
        } else if (between('0', '9')) {
            int n = parseNumber(false);
            return new Const(n);
        } else if (test('x')) {
            return new Variable("x");
        } else if (test('y')) {
            return new Variable("y");
        } else if (test('z')) {
            return new Variable("z");
        } else if (test('-')) {
            skipWhitespace();
            if (between('0','9')) {
                int n = parseNumber(true);
                return new Const(n);
            } else if (test('(')) {
                CommonExpression expr = parseExpression();
                expect(')');
                return new CheckedNegate(expr);
            } else {
                return new CheckedNegate(parseOperand());
            }
        } else if (test('d')) {
            expect("igits");
            skipWhitespace();
            if (test('(')) {
                CommonExpression expr = parseExpression();
                expect(')');
                return new Digits(expr);
            } else {
                return new Digits(parseOperand());
            }
        } else if (test('r')) {
            expect("everse");
            skipWhitespace();
            if (test('(')) {
                CommonExpression expr = parseExpression();
                expect(')');
                return new Reverse(expr);
            } else {
                return new Reverse(parseOperand());
            }
        }

        throw operandError();
    }

    public CommonExpression parseExpression() {
        return parse3PriorExpression();
    }

    private  CommonExpression parse0PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = null;

        firstOperand = parseOperand();
        skipWhitespace();
        while (true) {
            if (testOperation("**")) {
                skipWhitespace();
                firstOperand = new Pow(firstOperand, parseOperand());
            } else if (testOperation("//")) {
                skipWhitespace();
                firstOperand = new Log(firstOperand, parseOperand());
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    private CommonExpression parse1PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = parse0PriorExpression();
        skipWhitespace();
        while (true) {
            if (testOperation("*")) {
                skipWhitespace();
                firstOperand = new CheckedMultiply(firstOperand, parse0PriorExpression());
            } else if (testOperation("/")) {
                skipWhitespace();
                firstOperand = new CheckedDivide(firstOperand, parse0PriorExpression());
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    private CommonExpression parse2PriorExpression() {

        skipWhitespace();
        CommonExpression firstOperand = parse1PriorExpression();
        skipWhitespace();
        while (true) {
            if (testOperation("+")) {
                skipWhitespace();
                firstOperand = new CheckedAdd(firstOperand, parse1PriorExpression());
            } else if (testOperation("-")) {
                skipWhitespace();
                firstOperand = new CheckedSubtract(firstOperand, parse1PriorExpression());
            } else {
                return firstOperand;
            }
            skipWhitespace();
        }
    }

    private CommonExpression parse3PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = parse2PriorExpression();
        skipWhitespace();
        while (true)  {
            if (testOperation("<<")) {
                skipWhitespace();
                firstOperand = new ShiftLeft(firstOperand, parse2PriorExpression());
            } else if (testOperation(">>")) {
                skipWhitespace();
                firstOperand = new ShiftRight(firstOperand, parse2PriorExpression());
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
