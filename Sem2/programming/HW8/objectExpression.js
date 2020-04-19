"use strict";

let variables = {
    "x": 0,
    "y": 1,
    "z": 2
};

const ANY_ARITY = -1;

function AbstractOperation(...operands) {
    this.operands = operands;
}
AbstractOperation.prototype.evaluate = function(...args ){
    return this._evaluate(...this.operands.map(operand => operand.evaluate(...args)));
}
AbstractOperation.prototype.toString = function() {
    return this.operands.join(" ").concat(" ", this.symbol);
}
AbstractOperation.prototype.diff = function(arg) {
    return this._diff(arg, ...this.operands.concat(this.operands.map(a => a.diff(arg))));
}
AbstractOperation.prototype.prefix = function() {
    return "(".concat(this.symbol, " ", this.operands.map(a => a.prefix()).join(" "), ")");
}
AbstractOperation.prototype.postfix = function() {
    return "(".concat(this.operands.map(a => a.postfix()).join(" "), " ", this.symbol + ")");
}



function Operation(symbol, evaluate, diff) {
    this.symbol = symbol;
    this._evaluate = evaluate;
    this._diff = diff;
}
Operation.prototype = AbstractOperation.prototype

function createOperation(symbol, evaluate, diff) {
    function op(...operands) {
        AbstractOperation.call(this, ...operands);
    }
    op.prototype = new Operation(symbol, evaluate, diff);
    op.prototype.constructor = op;
    return op;
}

function AbstractOperand(value) {
    this.value = value;
    this.index = variables[value];
}
AbstractOperand.prototype.toString = function() {
    return this.value.toString();
};
AbstractOperand.prototype.prefix = AbstractOperand.prototype.toString;
AbstractOperand.prototype.postfix = AbstractOperand.prototype.toString;
AbstractOperand.prototype.evaluate = function(...args) {
    return this._evaluate(this.value, ...args);
};
AbstractOperand.prototype.diff = function(arg) {
    return this._diff(this.value, arg);
};

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
    op.prototype.constructor = op;
    return op;
}

const Add = createOperation('+',
                                  (a, b) => a + b,
                                  (arg, a, b, da, db) => new Add(da, db)
                                 );
const Subtract = createOperation('-',
                                       (a, b) => a - b,
                                       (arg, a, b, da, db) => new Subtract(da, db),
                                      );
const Multiply = createOperation('*',
                                       (a, b) => a * b,
                                       (arg, a, b, da, db) => new Add(
                                           new Multiply(a, db),
                                           new Multiply(da, b)
                                       )
                                      );
const Divide = createOperation('/',
                                     (a, b) => a / b,
                                     (arg, a, b, da, db) => new Divide(
                                         new Subtract(
                                             new Multiply(da,b),
                                             new Multiply(a,db)
                                         ),
                                         new Multiply(b,b)
                                     )
                                    );
const Log = createOperation('log',
                            (a, b) => Math.log(Math.abs(b))/Math.log(Math.abs(a)),
                            function(arg, a, b, da, db){
                                var LnA = new Log(Const.E, a);
                                var LnB = new Log(Const.E, b);
                                return new Divide(
                                    new Subtract(
                                        new Divide(new Multiply(db, LnA), b),
                                        new Divide(new Multiply(da, LnB), a)
                                    ),
                                    new Multiply(LnA, LnA)
                                );
                            }
                           );
const Power = createOperation('pow',
                                    (a, b) => Math.pow(a, b),
                                    (arg, a, b, da, db) => new Multiply(
                                        new Power(a, b),
                                        new Add(
                                            new Multiply(db, new Log(Const.E, a)),
                                            new Divide(new Multiply(b, da), a)
                                        )
                                    )
                                   );
const Negate = createOperation('negate',
                                    a => -a,
                                    (arg, a, da) => new Negate(da)
                                   );
const Sumexp = createOperation('sumexp',
                               (...operands) => operands.reduce((a, b) => a + Math.exp(b), 0),
                               (arg, ...operands) => {
                                   var res = Const.ZERO;
                                   var diff_operands = operands.splice(operands.length / 2);
                                   for(const i in operands) {
                                       res = new Add(new Multiply(diff_operands[i], new Power(Const.E, operands[i])), res);
                                   }
                                   return res;
                               }
                              );
const Softmax = createOperation('softmax',
                                (...operands) => Math.exp(operands[0])/operands.reduce((a, b) => a + Math.exp(b), 0),
                                (arg, ...operands) => {
                                    operands.splice(operands.length / 2);
                                    return new Divide(new Power(Const.E, operands[0]), new Sumexp(...operands)).diff(arg);
                                }
                               );
const Const = createOperand(a => a,
                            () => Const.ZERO
                           );
const Variable = createOperand(function(a, ...args) {
                                   return args[this.index];
                               },
                               (a, arg) => arg == a ? Const.ONE : Const.ZERO
                              );
Const.E = new Const(Math.E);
Const.ZERO = new Const(0);
Const.ONE = new Const(1);

let cachedVariables = {};
Object.keys(variables).forEach(v => cachedVariables[v] = new Variable(v));

// Parser

let tokens = {};
let addOperation = (token, func) => tokens[token] = {"arity": func.prototype._evaluate.length, "func": func};
addOperation("negate", Negate);
addOperation("+",      Add);
addOperation("-",      Subtract);
addOperation("/",      Divide);
addOperation("*",      Multiply);
addOperation("log",    Log);
addOperation("pow",    Power);
addOperation("sumexp", Sumexp);
addOperation("softmax",Softmax);

function processToken(token, stack, iterator) {
    // console.log(token);
   if(token in tokens) {
       var oper = tokens[token];
       // console.log(oper);
       if(oper.arity == ANY_ARITY) {
           return new oper.func(...stack);
       }
       return new oper.func(...stack.splice(stack.length - oper.arity));
   } else if(!isNaN(token)) {
       return new Const(+token);
   } else if(token in variables) {
       return cachedVariables[token];
   } else {
       throw new UnknownTokenError(iterator, token);
   }
}

function parseArray (arr) {
    var stack = [];
    for(const token of arr) {
        if(token.length == 0) continue;
        stack.push(processToken(token, stack));
        // console.log(stack);
    }
    return stack[0];
}

let parse = expressionString => parseArray(expressionString.split(' '));

// Errors, Postfix, Prefix

function AbstractParserError(iterator, ...args) {
    this.message = this.getMessage(...args) + iterator.errorMessage();
}
AbstractParserError.prototype = Object.create(Error.prototype);
AbstractParserError.prototype.constructor = AbstractParserError;

function createError() {
    var err = function(iterator, ...args) {
        AbstractParserError.call(this, iterator, ...args);
    }
}
function initError(err, getMessage) {
    err.prototype = Object.create(AbstractParserError.prototype);
    err.prototype.getMessage = getMessage;
    err.prototype.constructor = err;
}

function ParserError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(ParserError, msg => msg);

function UnmatchedParenthesisError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(UnmatchedParenthesisError, (parenthesis, operation) =>
            "Miss " + (parenthesis == "(" ? "open" : "close") + " parenthesis for operation " + operation
           );

function UnknownTokenError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(UnknownTokenError, (symb) =>
            "Unknown token: " + symb
           );

function InvalidOperationError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(InvalidOperationError, (symb) => {
    if(symb == undefined) {
        return "Empty operation";
    } else {
        return "Invalid operation " + symb;
    }
});

function InvalidOperandError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(InvalidOperandError, (symb) =>
            "invalid operand " + symb
           );

function InvalidArgsCountError(iterator, ...args) {
    AbstractParserError.call(this, iterator, ...args);
}
initError(InvalidArgsCountError, (need, passed, operation) => {
    if(need < passed) {
        return "Too many operands for " + operation + ". Need " + need + ", but " + passed + " provided";
    }
    if(need > passed) {
        return "Too few operands for " + operation + ". Need " + need + ", only " + passed + " provided";
    }
});

function Iterator(expression) {
    this.expression = expression;
    this.it = 0;
    this.next = () => this.it >= this.expression.length ? '\x00' : this.expression[this.it++];
    this.getChar = () => this.it >= this.expression.length ? '\x00' : this.expression[this.it];
    this.errorMessage = () => " at position " + this.it;
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
        return processToken(operandString, undefined, iterator);
    }
    throw new InvalidOperandError(iterator, operandString);
}

let parsePrefixOperation = function(iterator) {
    var operationString = parseStringToken(iterator);
    var operationArity = getArity(operationString);
    var operands = [];
    if(operationArity == 0) {
        throw new InvalidOperationError(iterator, operationString);
    }
    for(var i = 0; operationArity == ANY_ARITY || i < operationArity; ++i){
        var operand = parseStringToken(iterator);
        if(operand == '(') {
            operand = parsePrefixOperation(iterator);
            if(parseStringToken(iterator) != ')') {
                throw new UnmatchedParenthesisError(iterator, ")", operand.symbol);
            }
            operands.push(operand);
            continue;
        }
        if(operand == ')') {
            if(operationArity == ANY_ARITY) {
                break;
            }
            throw new InvalidArgsCountError(iterator, operationArity, i, operationString)
        }
        operands.push(parseOperand(operand, iterator));
    }
    // console.log(operands);
    return processToken(operationString, operands, iterator);

}

let parsePostfixOperation = function(iterator) {
    var operands = [];
    var operationString;
    for(;;){
        var operand = parseStringToken(iterator);
        if(operand == '(') {
            operand = parsePostfixOperation(iterator);
            if(parseStringToken(iterator) != ')') {
                throw new UnmatchedParenthesisError(iterator, ")", operand.symbol);
            }
            operands.push(operand);
            continue;
        }
        if(operand == ')') {
            break;
        }
        operationString = operand;
        if(operationString in tokens) {
            break;
        }
        operands.push(parseOperand(operand, iterator));
    }
    var operationArity = getArity(operationString);
    if(operationArity == 0) {
        throw new InvalidOperationError(iterator, operationString);
    }
    if(operationArity != ANY_ARITY) {
        if(operationArity < operands.length) {
            throw new InvalidArgsCountError(iterator, operationArity, operands.length, operationString)
        }
        if(operationArity > operands.length) {
            throw new InvalidArgsCountError(iterator, operationArity, operands.length, operationString)
        }
    }

    // console.log(operands);
    return processToken(operationString, operands, iterator);

}

let parseExpression = function(iterator, parser) {
    var token = parseStringToken(iterator);
    if(token == '(') {
        var res = parser(iterator);
        if(parseStringToken(iterator) != ')') {
                throw new UnmatchedParenthesisError(iterator, ")", res.symbol);
        }
    } else {
        var res = parseOperand(token, iterator);
    }
    if(parseStringToken(iterator) != '\x00') {
        throw new ParserError(iterator, "End of expression expected");
    }
    return res;
}

let parsePrefix = prefixExpressionString => parseExpression(new Iterator(prefixExpressionString), parsePrefixOperation);
let parsePostfix = prefixExpressionString => parseExpression(new Iterator(prefixExpressionString), parsePostfixOperation);

console.log(Sumexp.prototype.arity);

// module.exports = {
//     parse: parse,
//     parsePrefix: parsePrefix
// };
