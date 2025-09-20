"use strict";

let variables = {
    "x": 0,
    "y": 1,
    "z": 2
}

function AbstractOperation(...operands) {
    this.operands = operands;
}
AbstractOperation.prototype.evaluate = function(...args ){
    return this._evaluate(...this.operands.map(operand => operand.evaluate(...args)));
}
AbstractOperation.prototype.toString = function() {
    return this.operands.map(a => a.toString()).join(" ").concat(" ", this.symbol);
}
AbstractOperation.prototype.diff = function(arg) {
    return this._diff(arg, ...this.operands.concat(this.operands.map(a => a.diff(arg))));
}


function Operation(symbol, arity, evaluate, diff) {
    this.symbol = symbol;
    this.arity = arity;
    this._evaluate = evaluate;
    this._diff = diff;
}
Operation.prototype = AbstractOperation.prototype

function createOperation(symbol, arity, evaluate, diff) {
    function op(...operands) {
        AbstractOperation.call(this, ...operands);
    }
    op.prototype = new Operation(symbol, arity, evaluate, diff);
    return op;
}

function createBinaryOperation(symbol, evaluate, diff) {
    return createOperation(symbol, 2, evaluate, diff);
}

function createUnaryOperation(symbol, evaluate, diff) {
    return createOperation(symbol, 1, evaluate, diff);
}

function AbstractOperand(value) {
    this.value = value;
}
AbstractOperand.prototype.toString = function() {
    return this.value.toString();
}
AbstractOperand.prototype.evaluate = function(...args) {
    return this._evaluate(this.value, ...args);
}
AbstractOperand.prototype.diff = function(arg) {
    return this._diff(this.value, arg);
}

function Operand(evaluate, diff) {
    this._evaluate = evaluate;
    this._diff = diff;
}
Operand.prototype = AbstractOperand.prototype;

function createOperand(evaluate, diff) {
    function op(value) {
        AbstractOperand.call(this, value);
    }
    op.prototype = new Operand(evaluate, diff);
    return op;
}

const Add = createBinaryOperation('+',
                                  (a, b) => a + b,
                                  (arg, a, b, da, db) => new Add(da, db)
                                 );
const Subtract = createBinaryOperation('-',
                                       (a, b) => a - b,
                                       (arg, a, b, da, db) => new Subtract(da, db),
                                      );
const Multiply = createBinaryOperation('*',
                                       (a, b) => a * b,
                                       (arg, a, b, da, db) => new Add(
                                           new Multiply(a, db),
                                           new Multiply(da, b)
                                       )
                                      );
const Divide = createBinaryOperation('/',
                                     (a, b) => a / b,
                                     (arg, a, b, da, db) => new Divide(
                                         new Subtract(
                                             new Multiply(da,b),
                                             new Multiply(a,db)
                                         ),
                                         new Multiply(b,b)
                                     )
                                    );
const Log = createBinaryOperation('log',
                                  (a, b) => Math.log(Math.abs(b))/Math.log(Math.abs(a)),
                                  (arg, a, b, da, db) => new Divide(
                                      new Subtract(
                                          new Divide(new Multiply(db, new Log(Const.E, a)), b),
                                          new Divide(new Multiply(da, new Log(Const.E, b)), a)
                                      ),
                                      new Power(new Log(Const.E, a), new Const(2))
                                  )
                                 );
const Power = createBinaryOperation('pow',
                                    (a, b) => Math.pow(a, b),
                                    (arg, a, b, da, db) => new Multiply(
                                        new Power(a, b),
                                        new Add(
                                            new Multiply(db, new Log(Const.E, a)),
                                            new Divide(new Multiply(b, da), a)
                                        )
                                    )
                                   );
const Negate = createUnaryOperation('negate',
                                    a => -a,
                                    (arg, a, da) => new Negate(da)
                                   );
const Const = createOperand(a => a,
                            () => Const.ZERO
                           );
const Variable = createOperand((a, ...args) => args[variables[a]],
                               (a, arg) => arg == a ? Const.ONE : Const.ZERO
                              );
Const.E = new Const(Math.E);
Const.ZERO = new Const(0);
Const.ONE = new Const(1);

let cachedVariables = {}
Object.keys(variables).forEach(v => cachedVariables[v] = new Variable(v));

// Parser

let tokens = {}
let addOperation = (token, arity, func) => tokens[token] = {"arity": arity, "func": func};
addOperation("negate", 1, Negate);
addOperation("+",      2, Add);
addOperation("-",      2, Subtract);
addOperation("/",      2, Divide);
addOperation("*",      2, Multiply);
addOperation("log",    2, Log);
addOperation("pow",    2, Power);

let processToken = function(token, stack) {
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

console.log(new Add(new Variable('x'), new Const(2)).diff('x'))
