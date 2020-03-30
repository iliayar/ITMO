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

let parseToken = function(token, stack) {
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
        stack.push(parseToken(token, stack));
        // console.log(stack);
    }
    return stack[0];
}

let parse = expressionString => parseArray(expressionString.split(' '));

// console.log(tokens);
console.log(parse("2 8 log").diff("x").evaluate(0,0,0));
