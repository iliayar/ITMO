package expression.parser;

import expression.*;

public class ExpressionParser<T extends Number> extends BaseParser {

    Calculator<T> calc;

    public ExpressionParser(Calculator<T> calc) {
        this.calc = calc;
    }

    public ExpressionParser(ExpressionSource src, Calculator<T> calc) {
        this.calc = calc;
        this.src = src;
        nextChar();
    }


    @Override
    public CommonExpression parse(String src) {
        this.src = new StringSource(src);
        nextChar();
        return parseExpression();
    }

    private T parseNumber(boolean isNegate) {
        StringBuilder sb = new StringBuilder();
        if(isNegate) {
            sb.append('-');
        }
        while(between('0','9')) {
            sb.append(ch);
            nextChar();
        }
        return calc.parseNumber(sb.toString());
    }

    private char parseOperation() {
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
        if(between('0','9')) {
            return new Const(parseNumber(false));
        } else if(test('x')) {
            return new Variable("x");
        } else if(test('y')) {
            return new Variable("y");
        } else if(test('z')) {
            return new Variable("z");
        } else if(test('-')) {
            skipWhitespace();
            if(between('0','9')) {
                return new Const(parseNumber(true));
            } else if(test('(')) {
                CommonExpression expr = parseExpression();
                test(')');
                return new Negate<T>(expr, calc);
            } else {
                return new Negate<T>(parseOperand(), calc);
            }
        }
        // } else if(test('d')) {
        //     expect("igits");
        //     skipWhitespace();
        //     if(test('(')) {
        //         CommonExpression expr = parseExpression();
        //         expect(')');
        //         return new Digits(expr);
        //     } else {
        //         return new Digits(parseOperand());
        //     }
        // } else if(test('r')) {
        //     expect("everse");
        //     skipWhitespace();
        //     if(test('(')) {
        //         CommonExpression expr = parseExpression();
        //         expect(')');
        //         return new Reverse(expr);
        //     } else {
        //         return new Reverse(parseOperand());
        //     }
        // }

        throw error("Operand expected");
    }

    public CommonExpression parseExpression() {
        return parseExpression(3);
    }

    private CommonExpression parseExpression(int prior) {

        skipWhitespace();

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
                firstOperand = new Multiply<T>(firstOperand, secondOperand, calc);
            } else if(operation == '/') {
                firstOperand = new Divide<T>(firstOperand, secondOperand, calc);
            } else if(operation == '+') {
                firstOperand = new Add<T>(firstOperand, secondOperand, calc);
            } else if(operation == '-'){
                firstOperand = new Subtract<T>(firstOperand, secondOperand, calc);
            }
            // } else if(operation == '<') {
            //     firstOperand = new ShiftLeft(firstOperand, secondOperand, calc);
            // } else {
            //     firstOperand = new ShiftRight(firstOperand, secondOperand, calc);
            // }

        }

        return firstOperand;
    }

    private void skipWhitespace() {
        while (test(' ') || test('\r') || test('\n') || test('\t')) {
            // skip
        }
    }

}
