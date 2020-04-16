"use strict";

let variables = {
    "x": 0,
    "y": 1,
    "z": 2
};

let cnst = value => () => value;
let expressionVariable = variable => (...args) => args[variables[variable]];

let cachedVariables  = {};
Object.keys(variables).forEach(v => cachedVariables[v] = expressionVariable(v));
let variable = v => cachedVariables[v];

let binOperation = op => (a, b) => (...args) => op(a(...args), b(...args));
let multiply = binOperation((a, b) => a * b);
let add = binOperation((a, b) => a + b);
let subtract = binOperation((a, b) => a - b);
let divide = binOperation((a, b) => a / b);

let pi = cnst(Math.PI);
let e = cnst(Math.E);

let avg5 = (...values) =>
    (...args) => values.reduce((acc, value) => acc + value(...args), 0)/values.length;

let med3 = (...values) =>
    (...args) => values.map(x => x(...args)).sort((a, b) => a - b)[Math.floor(values.length/2)];


let unaryOpeartion = op => a => (...args) => op(a(...args));
let negate = unaryOpeartion(a => -a);

// Parser

let tokens = {}
let addOperation = (token, arity, func) => tokens[token] = {"arity": arity, "func": func};
let addVariables = () => Object.keys(variables).forEach(v => addOperation(v, 0, () => variable(v)));
addOperation("negate", 1, negate);
addOperation("+",      2, add);
addOperation("-",      2, subtract);
addOperation("/",      2, divide);
addOperation("*",      2, multiply);
addOperation("med3",   3, med3);
addOperation("avg5",   5, avg5);
addOperation("pi",     0, () => pi);
addOperation("e",      0, () => e);
addVariables();

let processToken = function(token, stack) {
   if(token in tokens) {
       var oper = tokens[token];
       // console.log(oper);
       return oper.func(...stack.splice(stack.length - oper.arity));
   } else if(!isNaN(token)) {
       return cnst(+token);
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

// console.log(tokens);
console.log(parse("x x *")(2,0,0));
