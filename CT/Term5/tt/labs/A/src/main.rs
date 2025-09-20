use std::{borrow::{BorrowMut, Borrow}, cell::RefCell, collections::{HashMap, HashSet}, fmt::Display, io::stdin, ops::{DerefMut, Deref}, rc::Rc, slice::SliceIndex};

type ERef = Rc<RefCell<Expression>>;
type VRef = Rc<RefCell<String>>;

#[derive(Debug,Clone)]
enum Expression {
    Lambda(VRef, ERef),
    Application(ERef, ERef),
    Var(VRef),
    Memo(ERef),
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Lambda(v, e) => write!(f, "(\\{}.{})", v.as_ref().borrow(), e.as_ref().borrow()),
            Expression::Application(e1, e2) => write!(f, "({} {})", e1.as_ref().borrow(), e2.as_ref().borrow()),
            Expression::Var(v) => write!(f, "{}", v.as_ref().borrow()),
            Expression::Memo(e) => write!(f, "{}", e.as_ref().borrow()),
        }
    }
}

fn skip_whitespaces(inp: &mut [u8]) -> &mut [u8] {
    let mut inp = inp;
    while inp[0] == b' ' {
	inp = &mut inp[1..];
    }
    return inp;
}

fn parse_var(inp: &mut [u8]) -> (&mut [u8], Option<String>) {
    let mut inp = skip_whitespaces(inp);
    let mut ident = String::new();
    while inp[0].is_ascii_alphanumeric() || inp[0] == b'\'' {
	ident.push(inp[0] as char);
	inp = &mut inp[1..];
    }
    if ident.is_empty() {
	return (inp, None);
    } else {
	return (inp, Some(ident));
    }
}

fn parse_atom(inp: &mut [u8]) -> (&mut [u8], Option<Expression>) {
    let mut inp = skip_whitespaces(inp);
    if inp[0] == b'(' {
	inp = &mut inp[1..];
	let (mut inp, res) = parse_expression(inp);
	assert!(inp[0] == b')');
	assert!(res.is_some());
	inp = &mut inp[1..];
	return (inp, res);
    } else {
	let (inp, var) = parse_var(inp);
	if let Some(var) = var {
	    return (inp, Some(Expression::Var(Rc::new(RefCell::new(var)))));
	} else {
	    return (inp, None);
	}
    }

}

fn parse_application(inp: &mut [u8]) -> (&mut [u8], Option<Expression>) {
    let (mut inp, first) = parse_atom(inp);
    if let Some(first) = first {
	let mut expr = first;
	loop {
	    let (new_inp, next) = parse_atom(inp);
	    inp = new_inp;
	    if let Some(next) = next {
		expr = Expression::Application(Rc::new(RefCell::new(expr)), Rc::new(RefCell::new(next)));
	    } else {
		break;
	    }
	}
	return (inp, Some(expr));
    } else {
	return (inp, None);
    }
}

fn parse_lambda(inp: &mut [u8]) -> (&mut [u8], Option<Expression>) {
    let mut inp = skip_whitespaces(inp);
    if inp[0] == b'\\' {
	inp = &mut inp[1..];
	let (inp, var) = parse_var(inp);
	if let Some(var) = var {
	    let inp = skip_whitespaces(inp);
	    let mut inp = skip_whitespaces(inp);
	    assert!(inp[0] == b'.');
	    inp = &mut inp[1..];
	    let (inp, expr) = parse_expression(inp);
	    if let Some(expr) = expr {
		return (inp, Some(Expression::Lambda(Rc::new(RefCell::new(var)), Rc::new(RefCell::new(expr)))));
	    } else {
		return (inp, None);
	    }
	} else {
	    return (inp, None);
	}
    } else {
	return (inp, None);
    }
}

fn parse_expression(inp: &mut [u8]) -> (&mut [u8], Option<Expression>) {
    let (inp, app) = parse_application(inp);
    if let Some(app) = app {
	let (inp, lam) = parse_lambda(inp);
	if let Some(lam) = lam {
	    return (inp, Some(Expression::Application(Rc::new(RefCell::new(app)), Rc::new(RefCell::new(lam)))));
	} else {
	    return (inp, Some(app));
	}
    }
    return parse_lambda(inp);
}

fn through_memo(expr: ERef) -> ERef {
    match &*expr.as_ref().borrow() {
	Expression::Memo(e) => through_memo(e.clone()),
	e => expr.clone(),
    }
}

fn clone_memo(expr: ERef) -> ERef {
    match &*expr.as_ref().borrow() {
	Expression::Memo(e) => clone_memo(e.clone()),
	e => deep_clone_expr(expr.clone()),
    }
}

fn deep_clone_expr(expr: ERef) -> ERef {
    match &*expr.as_ref().borrow() {
	Expression::Lambda(v, e) =>
	    Rc::new(RefCell::new(
		Expression::Lambda(
		    Rc::new(RefCell::new(v.as_ref().borrow().clone())),
		    deep_clone_expr(e.clone()),
		))
	    ),
	Expression::Application(e1, e2) =>
	    Rc::new(RefCell::new(
		Expression::Application(
		    deep_clone_expr(e1.clone()),
		    deep_clone_expr(e2.clone()),
		))
	    ),
	Expression::Var(v) =>
	    Rc::new(RefCell::new(
		Expression::Var(
		    Rc::new(RefCell::new(v.as_ref().borrow().clone())),
		))
	    ),
	Expression::Memo(e) => deep_clone_expr(e.clone()),
    }
}

fn find_redex(expr: ERef) -> Option<ERef> {
    match &*expr.as_ref().borrow() {
	Expression::Lambda(_, e) => find_redex(e.clone()),
	Expression::Application(e1, e2) => {
	    match &*through_memo(e1.clone()).as_ref().borrow() {
		Expression::Lambda(_, _) => {
		    Some(expr.clone())
		}
		_ => {
		    find_redex(e1.clone()).or(find_redex(e2.clone()))
		}
	    }
	}
	Expression::Var(_) => None,
	Expression::Memo(e) => find_redex(e.clone()),
    }
}

fn rename_vars(expr: ERef, subst: &HashSet<String>, var_cnt: &mut usize, bindings: &mut HashMap<String, String>) {
    match &*expr.as_ref().borrow() {
        Expression::Lambda(v, e) => {
	    let v: &mut String = &mut *v.as_ref().borrow_mut();
	    let nv = format!("v{}", var_cnt);
	    let k = v.to_string();
	    let oldV = bindings.get(&k).map(String::clone);
	    bindings.insert(k.clone(), nv.clone());
	    *v = nv;
	    *var_cnt += 1;
	    rename_vars(e.clone(), subst, var_cnt, bindings);
	    bindings.remove(&k);
	    if let Some(oldV) = oldV {
		bindings.insert(k.clone(), oldV);
	    }
	},
        Expression::Application(e1, e2) => {
	    rename_vars(e1.clone(), subst, var_cnt, bindings);
	    rename_vars(e2.clone(), subst, var_cnt, bindings);
	},
        Expression::Var(v) => {
	    let v: &mut String = &mut *v.as_ref().borrow_mut();
	    if let Some(nv) = bindings.get(v) {
		*v = nv.to_string();
	    }
	},
        Expression::Memo(e) => {
	    rename_vars(e.clone(), subst, var_cnt, bindings);
	},
    }
}

fn get_vars(expr: ERef, vars: &mut HashSet<String>) {
    match &*expr.as_ref().borrow() {
        Expression::Lambda(v1, e) => {
	    vars.insert(v1.as_ref().borrow().to_string());
	    get_vars(e.clone(), vars);
	},
	Expression::Application(e1, e2) => {
	    get_vars(e1.clone(), vars);
	    get_vars(e2.clone(), vars);
	},
	Expression::Var(ov) => {
	    vars.insert(ov.as_ref().borrow().to_string());
	},
        Expression::Memo(e) => {
	    get_vars(e.clone(), vars);
	},
    }
}

fn has_var(expr: ERef, v: &str) -> bool {
    match &*expr.as_ref().borrow() {
        Expression::Lambda(v1, e) => {
	    has_var(e.clone(), v)
	},
	Expression::Application(e1, e2) => {
	    has_var(e1.clone(), v) || has_var(e2.clone(), v)
	},
	Expression::Var(ov) => {
	    &*ov.as_ref().borrow() == v
	},
        Expression::Memo(e) => {
	    has_var(e.clone(), v)
	},
    }
}


fn replace(expr: ERef, v: &str, nexpr: ERef) {
    let mut do_replace = false;
    let mut replace_memo = Option::None;
    match &*expr.as_ref().borrow() {
        Expression::Lambda(v1, e) => {
	    if &*v1.as_ref().borrow() != v {
		replace(e.clone(), v, nexpr.clone());
	    }
	},
	Expression::Application(e1, e2) => {
	    replace(e1.clone(), v, nexpr.clone());
	    replace(e2.clone(), v, nexpr.clone());
	},
	Expression::Var(ov) => {
	    if &*ov.as_ref().borrow() == v {
		do_replace = true;
	    }
	},
        Expression::Memo(e) => {
	    replace_memo = Some(deep_clone_expr(e.clone()))
	},
    }
    if do_replace {
	expr.replace(Expression::Memo(nexpr.clone()));
    }
    if let Some(e) = replace_memo {
	expr.swap(&e);
    }
}

fn reduce(expr_ref: ERef, var_cnt: &mut usize) {
    let mut nexpr = Option::None;
    let expr = expr_ref.as_ref().borrow_mut();
    if let Expression::Application(lam, arg) = &*expr {
	if let Expression::Lambda(v, e) = &*clone_memo(lam.clone()).as_ref().borrow() {
	    let mut vars = HashSet::new();
	    rename_vars(e.clone(), &vars, var_cnt, &mut HashMap::new());
	    replace(e.clone(), &*v.as_ref().borrow(), arg.clone());
	    nexpr = Some(e.clone());
	}
    }
    drop(expr);
    expr_ref.swap(&nexpr.take().unwrap());
}

fn main() {
    let mut s = String::new();
    stdin().read_line(&mut s).unwrap();
    let mut parts = s.split_whitespace().map(|s| s.parse::<i64>().unwrap());
    let (m, k) = (parts.next().unwrap(), parts.next().unwrap());

    s = String::new();
    stdin().read_line(&mut s).unwrap();

    let mut s = s.into_bytes();
    let (r, e) = parse_expression(&mut s);
    if let Some(e) = e {
	let e = Rc::new(RefCell::new(e));
	let mut var_cnt = 0usize;
	for i in 0..m {
	    if i % k == 0 {
		println!("{}", e.as_ref().borrow());
	    }

	    if let Some(r) = find_redex(e.clone()) {
		reduce(r, &mut var_cnt);
	    } else {
		if i % k != 0 {
		    println!("{}", e.as_ref().borrow());
		}
		break;
	    }
	}
    } else {
	println!("Could not parse: {:?}", r);
    }

    
}
