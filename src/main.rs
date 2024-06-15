use std::{borrow::Cow, collections::HashMap, fmt, fs, rc::Rc};

trait StrExt {
    fn nonempty_or_else<'a>(&'a self, other: impl FnOnce() -> &'a str) -> &'a str;
}

impl StrExt for str {
    fn nonempty_or_else<'a>(&'a self, other: impl FnOnce() -> &'a str) -> &'a str {
        match self {
            "" => other(),
            s => s,
        }
    }
}

#[derive(Debug, thiserror::Error)]
enum ParseError {
    #[error("expected {expected} at line {line_num}")]
    Expected {
        expected: Cow<'static, str>,
        line_num: usize,
    },
    #[error("unexpected token {token:?} at line {line_num}")]
    Unexpected {
        token: Cow<'static, str>,
        line_num: usize,
    },
    #[error("invalid variable name {name:?} at line {line_num}")]
    InvalidName {
        name: Cow<'static, str>,
        line_num: usize,
    },
}

#[derive(Debug, Clone)]
pub enum AstExpr<'a> {
    Lambda(&'a str, Rc<Self>),
    Call(Rc<Self>, Rc<Self>),
    Var(&'a str),
}

impl fmt::Display for AstExpr<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lambda(name, expr) => write!(f, "${name}. {expr}"),
            Self::Call(func, arg) => {
                match &**func {
                    Self::Lambda(..) => write!(f, "({func}) ")?,
                    Self::Call(func, arg) if matches!(**arg, Self::Lambda(..)) => {
                        write!(f, "{func} ({arg}) ")?
                    }
                    _ => write!(f, "{func} ")?,
                }
                match **arg {
                    Self::Call(..) => write!(f, "({arg})")?,
                    _ => write!(f, "{arg}")?,
                }
                Ok(())
            }
            Self::Var(name) => write!(f, "{name}"),
        }
    }
}

#[derive(Debug)]
pub enum AstStmt<'a> {
    Let(&'a str, Option<Rc<AstExpr<'a>>>),
    Print(Rc<AstExpr<'a>>),
    None,
}

impl fmt::Display for AstStmt<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AstStmt::Let(name, Some(expr)) => write!(f, "let {name} = {expr}"),
            AstStmt::Let(name, None) => write!(f, "let {name}"),
            AstStmt::Print(expr) => write!(f, "print {expr}"),
            AstStmt::None => Ok(()),
        }
    }
}

fn verify_name(line_num: usize, name: &str) -> Result<&str, ParseError> {
    match name.contains(|ch: char| "#$.()[]{}=".contains(ch) || ch.is_whitespace()) {
        true => Err(ParseError::InvalidName {
            name: name.to_owned().into(),
            line_num,
        }),
        false => Ok(name),
    }
}

fn parse_expr(line_num: usize, mut line: &str) -> Result<(&str, Rc<AstExpr>), ParseError> {
    let out_expr;
    if let Some(s) = line.strip_prefix('$') {
        let mut name;
        (name, line) = s.split_once('.').ok_or(ParseError::Expected {
            expected: Cow::Borrowed("dot after variable name in a lambda as in `$[var].[expr]"),
            line_num,
        })?;

        name = verify_name(line_num, name.trim())?;

        let expr;
        (line, expr) = parse_expr_rest(line_num, line.trim_start())?;
        out_expr = Rc::new(AstExpr::Lambda(name, expr));
    } else if let Some(s) = line.strip_prefix('(') {
        (line, out_expr) = parse_expr_rest(line_num, s.trim_start())?;
        line = line
            .strip_prefix(')')
            .ok_or(ParseError::Expected {
                expected: Cow::Borrowed(")"),
                line_num,
            })?
            .trim_start();
    } else {
        let i = line
            .find(|ch: char| ch.is_whitespace() || "()$#".contains(ch))
            .unwrap_or(line.len());
        out_expr = Rc::new(AstExpr::Var(verify_name(line_num, &line[..i])?));
        line = line[i..].trim_start();
    }

    Ok((line, out_expr))
}

fn parse_expr_rest(line_num: usize, mut line: &str) -> Result<(&str, Rc<AstExpr>), ParseError> {
    let mut expr;
    (line, expr) = parse_expr(line_num, line)?;
    while !line.is_empty() && !line.starts_with(&[')', '#']) {
        let arg_expr;
        (line, arg_expr) = parse_expr(line_num, line)?;
        expr = Rc::new(AstExpr::Call(expr, arg_expr));
    }
    Ok((line, expr))
}

fn parse(code: &str) -> Result<Vec<AstStmt>, ParseError> {
    let mut statements = Vec::new();

    for (line_num, line) in code.lines().map(str::trim).enumerate() {
        let line_num = line_num + 1;

        match line.trim().split_once(char::is_whitespace) {
            Some(("let", mut line)) => {
                let mut name;
                let Some(pair) = line.split_once("=") else {
                    let i = line.find(|ch: char| "#".contains(ch)).unwrap_or(line.len());
                    statements.push(AstStmt::Let(verify_name(line_num, line[..i].trim())?, None));
                    continue;
                };
                (name, line) = pair;
                name = verify_name(line_num, name.trim())?;

                let expr;
                (line, expr) = parse_expr_rest(line_num, line.trim_start())?;
                if line.starts_with(')') {
                    println!("let 1: line={line:?} expr={expr:?}");
                    return Err(ParseError::Unexpected {
                        token: ")".into(),
                        line_num,
                    });
                }

                statements.push(AstStmt::Let(name, Some(expr)));
            }
            Some(("print", mut line)) => {
                let expr;
                (line, expr) = parse_expr_rest(line_num, line.trim_start())?;
                if line.starts_with(')') {
                    println!("print 1: line={line:?} expr={expr:?}");
                    return Err(ParseError::Unexpected {
                        token: ")".into(),
                        line_num,
                    });
                }

                statements.push(AstStmt::Print(expr));
            }
            Some((token, _)) if token.starts_with("#") => {
                statements.push(AstStmt::None);
            }
            Some((token, _)) => {
                return Err(ParseError::Unexpected {
                    token: token.to_owned().into(),
                    line_num,
                })
            }
            None if !line.is_empty() => {
                return Err(ParseError::Unexpected {
                    token: line.to_owned().into(),
                    line_num,
                })
            }
            None => {
                statements.push(AstStmt::None);
            }
        }
    }

    Ok(statements)
}

#[derive(Debug, Clone)]
enum Value<'a> {
    Ast(Rc<AstExpr<'a>>),
    Argument(&'a str),
    Symbol(&'a str),
}

impl fmt::Display for Value<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ast(ast) => write!(f, "{ast}"),
            Self::Argument(name) => write!(f, "[arg {name:?}]"),
            Self::Symbol(name) => write!(f, "[sym {name:?}]"),
        }
    }
}

impl<'a> From<Rc<AstExpr<'a>>> for Value<'a> {
    fn from(ast: Rc<AstExpr<'a>>) -> Self {
        Value::Ast(ast)
    }
}

impl<'a> From<AstExpr<'a>> for Value<'a> {
    fn from(ast: AstExpr<'a>) -> Self {
        Value::Ast(Rc::new(ast))
    }
}

#[derive(Debug)]
struct Var<'a> {
    value: Value<'a>,
    shadowed: bool,
}

#[derive(Debug)]
struct State<'a> {
    vars: HashMap<&'a str, Var<'a>>,
}

impl<'a> State<'a> {
    fn shadow(&mut self, name: &'a str, value: Value<'a>) -> Option<Var<'a>> {
        self.vars.insert(
            name,
            Var {
                value,
                shadowed: true,
            },
        )
    }
    fn unshadow(&mut self, name: &'a str, shadow: Option<Var<'a>>) {
        match shadow {
            Some(value) => self.vars.insert(name, value),
            None => self.vars.remove(name),
        };
    }

    fn resolve_var(&mut self, full_eval: bool, name: &'a str) -> Value<'a> {
        match self.vars.get(name) {
            Some(var) => match var.value {
                Value::Ast(ref expr) => match full_eval || var.shadowed {
                    true => self.eval(full_eval, &expr.clone()),
                    false => Value::Symbol(name),
                },
                Value::Symbol(name) if full_eval => self.resolve_var(full_eval, name),
                Value::Symbol(name) => Value::Symbol(name),
                Value::Argument(name) => Value::Argument(name),
            },
            None => panic!("undefined variable {name:?}"),
        }
    }

    fn resolve_lambda(&mut self, expr: &Rc<AstExpr<'a>>) -> Rc<AstExpr<'a>> {
        match **expr {
            AstExpr::Var(name) => match self.vars.get(name) {
                Some(var) => match var.shadowed {
                    false => expr.clone(),
                    true => match var.value {
                        Value::Ast(ref expr) => self.resolve_lambda(&expr.clone()),
                        Value::Symbol(var_name) | Value::Argument(var_name) => {
                            if var_name != name {
                                AstExpr::Var(var_name).into()
                            } else {
                                expr.clone()
                            }
                        }
                    },
                },
                None => panic!("undefined variable {name:?}"),
            },
            AstExpr::Call(ref func, ref arg) => {
                let res_func = self.resolve_lambda(func);
                let res_arg = self.resolve_lambda(arg);
                match Rc::ptr_eq(&res_func, func) && Rc::ptr_eq(&res_arg, arg) {
                    true => expr.clone(),
                    false => AstExpr::Call(res_func, res_arg).into(),
                }
            }
            AstExpr::Lambda(arg, ref lam_expr) => {
                let shadow = self.shadow(arg, Value::Argument(arg));
                let res_lam_expr = self.resolve_lambda(lam_expr);
                self.unshadow(arg, shadow);
                match Rc::ptr_eq(&res_lam_expr, lam_expr) {
                    true => expr.clone(),
                    false => AstExpr::Lambda(arg, res_lam_expr).into(),
                }
            }
        }
    }

    fn eval(&mut self, full_eval: bool, expr: &Rc<AstExpr<'a>>) -> Value<'a> {
        match **expr {
            AstExpr::Call(ref func, ref arg) => {
                let func = self.eval(true, func);
                let arg = self.eval(false, arg);

                match func {
                    Value::Ast(func) => match &*func {
                        AstExpr::Lambda(name, expr) => indent(|| {
                            if debug() {
                                print_indent();
                                println!("SHADOW {name} = {arg}");
                            }
                            let shadow = self.shadow(name, arg);
                            let value = self.eval(full_eval, &expr);
                            self.unshadow(name, shadow);
                            if debug() {
                                print_indent();
                                println!("UNSHADOW {name}");
                            }
                            value
                        }),
                        _ => panic!("non-lambda {func} is not callable"),
                        // _ => AstExpr::Call(func, arg.to_ast()).into(),
                    },
                    Value::Symbol(name) => {
                        panic!("symbol {name:?} is not callable")
                    }
                    Value::Argument(name) => From::from(AstExpr::Call(
                        AstExpr::Var(name).into(),
                        match arg {
                            Value::Ast(ast) => ast,
                            Value::Symbol(name) | Value::Argument(name) => {
                                AstExpr::Var(name).into()
                            }
                        },
                    )),
                }
            }
            AstExpr::Var(name) => self.resolve_var(full_eval, name),
            AstExpr::Lambda(arg, ref lam_expr) => set_debug(false, || {
                let shadow = self.shadow(arg, Value::Argument(arg));
                let res_lam_expr = self.resolve_lambda(lam_expr);
                self.unshadow(arg, shadow);
                match Rc::ptr_eq(&res_lam_expr, &lam_expr) {
                    true => expr.clone().into(),
                    false => AstExpr::Lambda(arg, res_lam_expr).into(),
                }
            }),
        }
    }
}

static DEBUG: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
fn debug() -> bool {
    DEBUG.load(std::sync::atomic::Ordering::Relaxed)
}
fn set_debug<F: FnOnce() -> R, R>(new_debug: bool, f: F) -> R {
    let prev_debug = debug();
    DEBUG.store(new_debug, std::sync::atomic::Ordering::Relaxed);
    let r = f();
    DEBUG.store(prev_debug, std::sync::atomic::Ordering::Relaxed);
    r
}
static INDENT: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
fn print_indent() {
    for _ in 0..INDENT.load(std::sync::atomic::Ordering::Relaxed) {
        print!("  ");
    }
}
fn indent<F: FnOnce() -> R, R>(f: F) -> R {
    INDENT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let r = f();
    INDENT.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    r
}

fn main() {
    let code = fs::read_to_string("a.txt").unwrap();
    let ast = parse(&code).unwrap();

    let mut state = State {
        vars: HashMap::new(),
    };

    for stmt in &ast {
        println!("> {stmt}");
        match stmt {
            AstStmt::Let(name, expr) => {
                let value = match expr {
                    Some(expr) => state.eval(false, expr),
                    None => Value::Symbol(name),
                };
                state.vars.insert(
                    name,
                    Var {
                        value,
                        shadowed: false,
                    },
                );
            }
            AstStmt::Print(expr) => {
                println!("{}", state.eval(false, expr));
            }
            AstStmt::None => {}
        }
    }
}
