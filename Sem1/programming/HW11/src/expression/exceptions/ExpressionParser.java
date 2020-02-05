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
//        System.err.println("DEBUG String: " + src);
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

    private char parseOperation() {
//        System.err.println("DEBUG parsing operation: " + ch);
        if(in("+-*/")) {
            char c = ch;
            nextChar();
            return c;
        } else if(test('<')) {
            expect('<');
            return '<';
        } else if(test('>')) {
            expect('>');
            return '>';
        }
        throw error("One of \'+, -, *, <<, >>/\' expected");
    }

    private CommonExpression parseOperand() {
//        System.err.println("DEBUG parsing operand: " + ch);
        if(between('0','9')) {
            long n = parseNumber();
            if(n > Integer.MAX_VALUE) {
                throw error("Too large number");
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
                    throw error("Too large number");
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

        throw error("Operand expected, " + ch + " found");
    }

    public CommonExpression parseExpression() {
        return parseExpression(3);
    }

    private CommonExpression parseExpression(int prior) {

        skipWhitespace();
//        System.out.println("Testing ayayay:" + ch);

        if(prior == 0) {
            return parseOperand();
        }

        String opers;
        if(prior == 1) {
            opers = "*/";
        } else if(prior == 2) {
            opers = "+-";
        } else {
            opers = "<>";
        }

        CommonExpression firstOperand = null;
        if(prior == 1 && test('(')) {
            firstOperand = parseExpression();
            expect(')');
        } else {
            firstOperand = parseExpression(prior - 1);
        }
        skipWhitespace();
        while(in(opers)) {
            CommonExpression secondOperand = null;

            char operation = parseOperation();
            skipWhitespace();
            if(prior == 1 && test('(')) {
                secondOperand = parseExpression();
                expect(')');
            } else {
                secondOperand = parseExpression(prior - 1);
            }
            skipWhitespace();
            if(operation == '*') {
                firstOperand = new CheckedMultiply(firstOperand, secondOperand);
            } else if(operation == '/') {
                firstOperand = new CheckedDivide(firstOperand, secondOperand);
            } else if(operation == '+') {
                firstOperand = new CheckedAdd(firstOperand, secondOperand);
            } else if(operation == '-'){
                firstOperand = new CheckedSubtract(firstOperand, secondOperand);
            } else if(operation == '<') {
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
