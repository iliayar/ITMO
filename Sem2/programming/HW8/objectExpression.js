"use strict";

let variables = {
    "x": 0,
    "y": 1,
    "z": 2
}

function Operation(symbol, evaluation, arity, ...operands) {
    this.symbol = symbol;
    this.operands = operands;
    this.evaluate = (...args) => evaluation(...operands.map(operand => operand.evaluate(...args)));
    this.arity = arity;
}
Operation.prototype.toString = function() {
    var res = "";
    for(const operand of this.operands) {
        res += operand.toString() + " ";
    }
    return res + this.symbol;
}
Operation.prototype.prefix = function() {
    var res = "(";
    res += this.symbol;
    for(const operand of this.operands) {
        res += " " + operand.prefix();
    }
    return res + ")";
}

function BinaryOperation(symbol, evaluation, a, b) {
    Operation.call(this, symbol, evaluation, 2, a, b);
}
BinaryOperation.prototype = Object.create(Operation.prototype);

function UnaryOperation(symbol, evaluation, a) {
    Operation.call(this, symbol, evaluation, 1, a);
}
UnaryOperation.prototype = Object.create(Operation.prototype);

function Operand(symbol, evaluation) {
    this.symbol = symbol;
    this.evaluate = evaluation;
}
Operand.prototype.toString = function() {
    return this.symbol;
}
Operand.prototype.prefix = function() {
    return this.symbol;
}

function Add(a, b) {
    BinaryOperation.call(this, "+", (a, b) => a + b, a, b);
    this.diff = arg => new Add(a.diff(arg), b.diff(arg));
}
Add.prototype = Object.create(BinaryOperation.prototype);

function Subtract(a, b) {
    BinaryOperation.call(this, "-", (a, b) => a - b, a, b);
    this.diff = arg => new Subtract(a.diff(arg), b.diff(arg));
}
Subtract.prototype = Object.create(BinaryOperation.prototype);

function Multiply(a, b) {
    BinaryOperation.call(this, "*", (a, b) => a * b, a, b);
    this.diff = arg => new Add(new Multiply(a, b.diff(arg)), new Multiply(a.diff(arg), b));
}
Multiply.prototype = Object.create(BinaryOperation.prototype);

function Divide(a, b) {
    BinaryOperation.call(this, "/", (a, b) => a / b, a, b);
    this.diff = arg => new Divide(new Subtract(new Multiply(a.diff(arg),b), new Multiply(a,b.diff(arg))), new Multiply(b,b));
}
Divide.prototype = Object.create(BinaryOperation.prototype);

function Log(a, b) {
    BinaryOperation.call(this, "log", (a, b) => Math.log(Math.abs(b))/Math.log(Math.abs(a)), a, b);
    this.diff = arg => new Divide(
        new Subtract(
            new Divide(new Multiply(b.diff(arg), new Log(E, a)), b),
            new Divide(new Multiply(a.diff(arg), new Log(E, b)), a)
        ),
        new Power(new Log(E, a), new Const(2))
    );
}
Log.prototype = Object.create(BinaryOperation.prototype);

function Power(a, b) {
    BinaryOperation.call(this, "pow", (a, b) => Math.pow(a, b), a, b);
    this.diff = arg => new Multiply(
        new Power(a, b),
        new Multiply(b,new Log(E, a)).diff(arg)
    );
}
Power.prototype = Object.create(BinaryOperation.prototype);

function Negate(a) {
    UnaryOperation.call(this, "negate", a => -a, a);
    this.diff = arg => new Negate(a.diff(arg));
}
Negate.prototype = Object.create(UnaryOperation.prototype);

function Sinh(a) {
    UnaryOperation.call(this, "sinh", a => Math.sinh(a), a);
    this.diff = arg => new Multiply(new Cosh(a), a.diff(arg));
}
Sinh.prototype = Object.create(UnaryOperation.prototype);

function Cosh(a) {
    UnaryOperation.call(this, "cosh", a => Math.cosh(a), a);
    this.diff = arg => new Multiply(new Sinh(a), a.diff(arg));
}
Cosh.prototype = Object.create(UnaryOperation.prototype);

function Const(a) {
    Operand.call(this, a.toString(), () => a);
    this.diff = () => new Const(0);
}
Const.prototype = Object.create(Operand.prototype);

function Variable(a) {
    Operand.call(this, a, (...args) => args[variables[a]]);
    this.diff = function(arg) {
        return arg == this.symbol ? new Const(1) : new Const(0);
    }
}
Variable.prototype = Object.create(Operand.prototype);

let E = new Const(Math.E);

let cachedVariables = {}
Object.keys(variables).forEach(v => cachedVariables[v] = new Variable(v));

// Parser

let tokens = {}
let addOperation = (token, arity, func) => tokens[token] = {"arity": arity, "func": func};
addOperation("sinh",   1, Sinh);
addOperation("cosh",   1, Cosh);
addOperation("negate", 1, Negate);
addOperation("+",      2, Add);
addOperation("-",      2, Subtract);
addOperation("/",      2, Divide);
addOperation("*",      2, Multiply);
addOperation("log",    2, Log);
addOperation("pow",    2, Power);

let processToken = function(token, stack) {
    // console.log(token);
   if(token in tokens) {
       var oper = tokens[token];
       // console.log(oper);
        return new oper.func(...stack.splice(stack.length - oper.arity));
   } else if(!isNaN(token)) {
       return new Const(+token);
   } else if(token in variables) {
       return cachedVariables[token];
   } else {
       throw new Error("Unkown token: " + token);
   }
}

let parseArray = function(arr) {
    var stack = [];
    for(const token of arr) {
        if(token.length == 0) continue;
        stack.push(processToken(token, stack));
        // console.log(stack);
    }
    return stack[0];
}

let parse = expressionString => parseArray(expressionString.split(' '));

// Prefix Parser

function PrefixParserError(msg, iterator) {
    this.message = msg + iterator.errorMessage();
}
PrefixParserError.prototype = Object.create(Error.prototype);


function Iterator(expression) {
    this.expression = expression;
    this.it = 0;
    this.next = () => this.it >= this.expression.length ? '\x00' : this.expression[this.it++];
    this.getChar = () => this.it >= this.expression.length ? '\x00' : this.expression[this.it];
    this.errorMessage = () => " at " + this.it + ", which is " + this.getChar();
}

let skipWhitespaces = function(iterator) {
    while(/\s/.test(iterator.getChar())) {
        iterator.next();
    }
}

let parseStringToken = function(iterator) {
    var res = "";
    skipWhitespaces(iterator);
    if(/[\(\)\0]/.test(iterator.getChar())) {
        return iterator.next();
    }
    while(!/[\s\(\)\0]/.test(iterator.getChar())) {
        res += iterator.next();
    }
    return res;
}

let getArity = function(stringToken) {
    if(stringToken in tokens) {
        return tokens[stringToken].arity;
    } else {
        return 0;
    }
}


let parseOperand = function(operandString, iterator) {
    if(getArity(operandString) == 0) {
        return processToken(operandString);
    }
    throw new PrefixParserError("Invalid operand " + operandString, iterator);
}

let parseOperation = function(iterator) {
    var operationString = parseStringToken(iterator);
    var operationArity = getArity(operationString);
    var operands = [];
    if(operationArity == 0) {
        throw new PrefixParserError("Invalid operation " + operationString, iterator);
    }
    for(var i = 0; i < operationArity; ++i){
        var operand = parseStringToken(iterator);
        if(operand == '(') {
            operand = parseOperation(iterator);
            if(parseStringToken(iterator) != ')') {
                throw new PrefixParserError("Miss close parenthesis for operation " + operand.symbol, iterator);
            }
            operands.push(operand);
            continue;
        }
        if(operand == ')') {
            throw new PrefixParserError("Too few operands for " + operationString + ". Need " + operationArity + ", only " + i + " provided", iterator);
        }
        operands.push(parseOperand(operand, iterator));
    }
    // console.log(operands);
    return processToken(operationString, operands);

}

let parsePrefixExpression = function(iterator) {
    var token = parseStringToken(iterator);
    if(token == '(') {
        var res = parseOperation(iterator);
        if(parseStringToken(iterator) != ')') {
            throw new PrefixParserError("Miss close parenthesis for operation " + res.symbol, iterator);
        }
    } else {
        var res = parseOperand(token, iterator);
    }
    if(parseStringToken(iterator) != '\x00') {
        throw new PrefixParserError("End of expression expected", iterator);
    }
    return res;
}

let parsePrefix = prefixExpressionString => parsePrefixExpression(new Iterator(prefixExpressionString));

console.log(parsePrefix('(+ x 2)').prefix());

// module.exports = {
//     parse: parse,
//     parsePrefix: parsePrefix
// };
