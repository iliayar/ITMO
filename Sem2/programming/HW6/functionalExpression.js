"use strict";


let cnst = value => () => value;
let variable = variable => (x, y, z) =>  {
    if(variable == "x") {
        return x;
    } else if(variable == "y") {
        return y;
    } else {
        return z;
    }
};

let binOperation = op => (a,b) => (x, y, z) => op(a(x, y, z),b(x, y, z));
let multiply = binOperation((a,b) => a*b);
let add = binOperation((a,b) => a+b);
let subtract = binOperation((a,b) => a-b);
let divide = binOperation((a,b) => a/b);

let pi = cnst(Math.PI);
let e = cnst(Math.E);

let avg5 = function() {
    return (x, y, z) => Array.from(arguments).slice(0, 5).reduce((acc, element) => acc + element(x,y,z), 0)/5;
};

let med3 = function() {
    return (x,y,z) => Array.from(arguments).slice(0,3).sort((a, b) => a(x,y,z) - b(x, y, z))[1](x, y, z);
}

let unaryOpeartion = op => a => (x, y, z) => op(a(x, y, z));
let negate = unaryOpeartion(a => -a);

// TESTS

console.log(avg5(cnst(5), cnst(3), variable("x"), variable("z"), cnst(-5))(3, 0, -3));
// console.log(med3(variable("y"), variable("x"), variable("z"))(0, 0, 1));
