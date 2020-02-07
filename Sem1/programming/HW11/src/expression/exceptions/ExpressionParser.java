package expression.exceptions;

import expression.*;
import expression.parser.BaseParser;
import expression.parser.ExpressionSource;
import expression.parser.StringSource;

public class ExpressionParser extends BaseParser {

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
            throw error("End of expression expected");
        }
        return res;
    }

    private long parseNumber() {
        StringBuilder sb = new StringBuilder();
        while(between('0','9')) {
            sb.append(ch);
            nextChar();
        }
        return  Long.parseLong(sb.toString());
    }

    private String parseOperation() {
        if(in("+-*/")) {
            char c = ch;
            if(test('*')) {
                if(test('*')) {
                    return "**";
                }
            } else if(test('/')) {
                if(test('/')) {
                    return "//";
                }
            } else {
                nextChar();
            }
            return Character.toString(c);
        } else if(test('<')) {
            expect('<');
            return "<<";
        } else if(test('>')) {
            expect('>');
            return ">";
        }
        throw error("One of \'+, -, *, <<, >>, /\' operation expected");
    }

    private CommonExpression parseOperand() {
        if(between('0','9')) {
            long n = parseNumber();
            if(n > Integer.MAX_VALUE) {
                throw new IntegerOverflowException(Long.toString(n));
            }
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
                long n = parseNumber();
                if(-n < Integer.MIN_VALUE) {
                    throw new IntegerOverflowException(Long.toString(-n));
                }
                return new Const(-n);
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

        throw error("Operand expected");
    }

    public CommonExpression parseExpression() {
        return parse3PriorExpression();
    }


    private CommonExpression parse0PriorExpression() {

        skipWhitespace();
        return parseOperand();
    }

    private CommonExpression parse1PriorExpression() {

        skipWhitespace();

        String opers = "*/";

        CommonExpression firstOperand = null;
        if(test('(')) {
            firstOperand = parseExpression();
            expect(')');
        } else {
            firstOperand = parse0PriorExpression();
        }
        skipWhitespace();
        while(in(opers)) {
            CommonExpression secondOperand = null;

            String operation = parseOperation();
            skipWhitespace();
            if(test('(')) {
                secondOperand = parseExpression();
                expect(')');
            } else {
                secondOperand = parse0PriorExpression();
            }
            skipWhitespace();
            if(operation.equals("*")) {
                firstOperand = new CheckedMultiply(firstOperand, secondOperand);
            } else if(operation.equals("/")) {
                firstOperand = new CheckedDivide(firstOperand, secondOperand);
            }

        }
        return firstOperand;
    }

    private CommonExpression parse2PriorExpression() {

        skipWhitespace();


        String opers = "+-";


        CommonExpression firstOperand = null;
        firstOperand = parse1PriorExpression();
        skipWhitespace();
        while(in(opers)) {
            CommonExpression secondOperand = null;

            String operation = parseOperation();
            skipWhitespace();
            secondOperand = parse1PriorExpression();
            skipWhitespace();
            if(operation.equals("+")) {
                firstOperand = new CheckedAdd(firstOperand, secondOperand);
            } else if(operation.equals("-")){
                firstOperand = new CheckedSubtract(firstOperand, secondOperand);
            }
        }
        return firstOperand;
    }

    private CommonExpression parse3PriorExpression() {

        skipWhitespace();

        String opers = "<>";

        CommonExpression firstOperand = null;

        firstOperand = parse2PriorExpression();
        skipWhitespace();
        while(in(opers)) {
            CommonExpression secondOperand = null;

            String operation = parseOperation();
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

    private  CommonExpression parseM1PriorExpression() {

        skipWhitespace();

        String opers = "*/";

        CommonExpression firstOperand = null;

        firstOperand = parse3PriorExpression();
        skipWhitespace();
        while(in(opers)) {

            CommonExpression secondOperand = null;

            String operation = parseOperation();
            if(!operation.equals("**") && !operation.equals("//")) {
                break;
            }
            skipWhitespace();
            secondOperand = parse2PriorExpression();
            skipWhitespace();
            if(operation.equals("**")) {
                firstOperand = new ShiftLeft(firstOperand, secondOperand);
            } else {
                firstOperand = new ShiftRight(firstOperand, secondOperand);
            }

        }
        return firstOperand;

    }

    private void skipWhitespace() {
        while (test(' ') || test('\r') || test('\n') || test('\t')) {
            // skip
        }
    }

}
