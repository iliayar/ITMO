package expression.exceptions;

import expression.*;
import expression.parser.BaseParser;
import expression.parser.ExpressionSource;
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
        if(ch != '\0') {
            if(ch == ')') {
                throw bracketError();
            }
            throw error("End of expression expected");
        }
        return res;
    }

    private int parseNumber(boolean isOtr) {
        int res = 0;

        while(between('0','9')) {
            if((!isOtr && Integer.MAX_VALUE/10 <= res && Integer.MAX_VALUE%10 < ch-'0') ||
            isOtr && Integer.MIN_VALUE/10 >= res && Integer.MIN_VALUE%10 > -ch+'0' ) {
                throw new IntegerOverflowException("Parsing const");
            }
            res *= 10;
            res += (isOtr ? -1 : 1)*(ch - '0');
            nextChar();
        }
        return  res;
    }

    private String parseOperation() {
        if(parsedOperation != null) {
            return parsedOperation;
        }
        if(in("+-*/")) {
            char c = ch;
            if(test('*')) {
                if(test('*')) {
                    parsedOperation = "**";
                    return parsedOperation;
                }
            } else if(test('/')) {
                if(test('/')) {
                    parsedOperation = "//";
                    return parsedOperation;
                }
            } else {
                nextChar();
            }
            parsedOperation = Character.toString(c);
        } else if(test('<')) {
            expect('<');
            parsedOperation = "<<";
        } else if(test('>')) {
            expect('>');
            parsedOperation = ">>";
        } else {
            throw error("One of \'+, -, *, <<, >>, /\' operation expected");
        }

        return parsedOperation;
    }

    private boolean testOperation(String expect) {
//        System.out.println(parsedOperation + " Testing operation " + ch + " " + expect);
        if(in("*+-<>/")) {
            parseOperation();
        }
        if(parsedOperation != null && parsedOperation.equals(expect)) {
            return true;
        }
        return false;
    }

    private CommonExpression parseOperand() {
        if(between('0','9')) {
            int n = parseNumber(false);
            return new Const(n);
        } else if(test('x')) {
            return new Variable("x");
        } else if(test('y')) {
            return new Variable("y");
        } else if(test('z')) {
            return new Variable("z");
        } else if(test('-')) {
            skipWhitespace();
            if(between('0','9')) {
                int n = parseNumber(true);
                return new Const(n);
            } else if(test('(')) {
                CommonExpression expr = parseExpression();
                expect(')');
                return new CheckedNegate(expr);
            } else {
                return new CheckedNegate(parseOperand());
            }
        } else if(test('d')) {
            expect("igits");
            skipWhitespace();
            if(test('(')) {
                CommonExpression expr = parseExpression();
                expect(')');
                return new Digits(expr);
            } else {
                return new Digits(parseOperand());
            }
        } else if(test('r')) {
            expect("everse");
            skipWhitespace();
            if(test('(')) {
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

//
//    private CommonExpression parse0PriorExpression() {
//
//        skipWhitespace();
//        return parseOperand();
//    }

    private  CommonExpression parse0PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = null;

        if(test('(')) {
            firstOperand = parseExpression();
            expect(')');
        } else {
            firstOperand = parseOperand();
        }
        skipWhitespace();
        while(testOperation("**") || testOperation("//")) {

            CommonExpression secondOperand = null;

            String operation = parsedOperation;
            parsedOperation = null;

            skipWhitespace();
            if(test('(')) {
                secondOperand = parseExpression();
                expect(')');
            } else {
                secondOperand = parseOperand();
            }
            skipWhitespace();
            if(operation.equals("**")) {
                firstOperand = new Pow(firstOperand, secondOperand);
            } else {
                firstOperand = new Log(firstOperand, secondOperand);
            }
        }
        return firstOperand;

    }

    private CommonExpression parse1PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = null;
        firstOperand = parse0PriorExpression();
        skipWhitespace();
        while(testOperation("*") || testOperation("/")) {
            CommonExpression secondOperand = null;

            String operation = parsedOperation;
            parsedOperation = null;
            skipWhitespace();
            secondOperand = parse0PriorExpression();
            skipWhitespace();
            if(operation.equals("*")) {
                firstOperand = new CheckedMultiply(firstOperand, secondOperand);
            } else {
                firstOperand = new CheckedDivide(firstOperand, secondOperand);
            }
        }
        return firstOperand;
    }

    private CommonExpression parse2PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = null;
        firstOperand = parse1PriorExpression();
        skipWhitespace();
        while(testOperation("+") || testOperation("-")) {
            CommonExpression secondOperand = null;

            String operation = parsedOperation;
            parsedOperation = null;

            skipWhitespace();
            secondOperand = parse1PriorExpression();
            skipWhitespace();
            if(operation.equals("+")) {
                firstOperand = new CheckedAdd(firstOperand, secondOperand);
            } else {
                firstOperand = new CheckedSubtract(firstOperand, secondOperand);
            }
        }
        return firstOperand;
    }

    private CommonExpression parse3PriorExpression() {

        skipWhitespace();

        CommonExpression firstOperand = null;

        firstOperand = parse2PriorExpression();
        skipWhitespace();
        while(testOperation("<<") || testOperation(">>")) {
            CommonExpression secondOperand = null;

            String operation = parsedOperation;
            parsedOperation = null;

            skipWhitespace();
            secondOperand = parse2PriorExpression();
            skipWhitespace();
            if(operation.equals("<<")) {
                firstOperand = new ShiftLeft(firstOperand, secondOperand);
            } else {
                firstOperand = new ShiftRight(firstOperand, secondOperand);
            }
        }
        return firstOperand;
    }

    @Override
    protected void expect(final char c) {
        if(ch != c) {
            if(c == ')') {
                throw bracketError();
            }
            if(ch == ')') {
                throw bracketError();
            }
            throw error("Expected \'" + c + "\'");
        }
        nextChar();
    }


    private MissingOperandException operandError() {
        return new MissingOperandException(error(""));
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
