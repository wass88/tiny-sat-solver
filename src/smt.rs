use core::panic;
use sat::SATSolver;
use std::fmt::{self, Display, Formatter};
use std::str::FromStr;

type ID = String;

#[derive(Debug, Clone)]
pub struct SMT {
    vars: Vec<VarInfo>,
    bool_vars: Vec<VarBool>,
    predicates: Vec<Predicate>,
}

#[derive(Debug, Clone)]
pub struct SMTResult {
    pub vars: Vec<(ID, usize)>,
    pub bool_vars: Vec<(ID, bool)>,
}

#[derive(Debug, Clone)]
struct VarInfo {
    id: ID,
    min: usize,
    max: usize,
}

#[derive(Debug, Clone)]
struct VarBool {
    id: ID,
}

#[derive(Debug, Clone)]
enum Predicate {
    Var { id: ID },
    And { predicates: Vec<Predicate> },
    Or { predicates: Vec<Predicate> },
    Not { predicate: Box<Predicate> },
    Eq { lhs: Expr, rhs: Expr },
    AllDiff { exprs: Vec<Expr> },
}

#[derive(Debug, Clone)]
enum SMTDef {
    Int { id: ID, min: usize, max: usize },
    Bool { id: ID },
    Predicate { predicate: Predicate },
}

#[derive(Debug, Clone)]
enum Expr {
    Var { id: ID },
    Int { value: usize },
}

#[derive(Debug, Clone)]
struct SExpr {
    name: String,
    args: Vec<SExpr>,
}

#[derive(Debug, Clone)]
pub struct SMT2 {
    predicates: Vec<Predicate2>,
}

#[derive(Debug, Clone)]
enum Predicate2 {
    Var { id: ID },
    And { predicates: Vec<Predicate2> },
    Or { predicates: Vec<Predicate2> },
    Not { predicate: Box<Predicate2> },
}

#[derive(Debug, Clone)]
pub struct SMT3 {
    cnf: Vec<Term>,
}

#[derive(Debug, Clone)]
struct Term {
    vars: Vec<CnfVar>,
}

#[derive(Debug, Clone)]
enum CnfVar {
    Pos(ID),
    Neg(ID),
}
impl CnfVar {
    fn id(&self) -> &ID {
        match self {
            CnfVar::Pos(id) => id,
            CnfVar::Neg(id) => id,
        }
    }
    fn is_neg(&self) -> bool {
        match self {
            CnfVar::Neg(_) => true,
            _ => false,
        }
    }
    fn invert(&self) -> Self {
        match self {
            CnfVar::Pos(id) => CnfVar::Neg(id.clone()),
            CnfVar::Neg(id) => CnfVar::Pos(id.clone()),
        }
    }
    fn pos(id: ID) -> Self {
        CnfVar::Pos(id)
    }

    fn is_pos(&self) -> bool {
        match self {
            CnfVar::Pos(_) => true,
            _ => false,
        }
    }
}

impl SMT {
    pub fn solve<T: SATSolver>(&self, solver: &T) -> Option<SMTResult> {
        let s = self.convert();
        let res = s.solve(solver);
        let Some(res) = res else { return None };

        let mut int_res = vec![];
        for int in &self.vars {
            let mut min = int.min;
            let mut max = int.max;
            for i in int.min..int.max {
                let id = format!("$int_{}_{}", int.id, i);
                let Some(v) = res.iter().find(|v| v.id() == &id) else {
                    panic!("Not found {}", id)
                };
                if v.is_pos() {
                    min = i + 1;
                } else {
                    max = i;
                }
            }
            int_res.push((int.id.clone(), min));
        }
        let mut bool_res = vec![];
        for bool in &self.bool_vars {
            let id = bool.id.clone();
            let Some(v) = res.iter().find(|v| v.id() == &id) else {
                panic!("Not found {}", id)
            };
            bool_res.push((id, v.is_pos()));
        }
        Some(SMTResult {
            vars: int_res,
            bool_vars: bool_res,
        })
    }
    pub fn convert(&self) -> SMT2 {
        let mut res = vec![];
        for predicate in &self.predicates {
            let p = self.convert_predicate(predicate);
            res.push(p);
        }
        for int in &self.vars {
            res.extend(self.int_predicate(int))
        }
        SMT2 { predicates: res }
    }
    fn convert_predicate(&self, p: &Predicate) -> Predicate2 {
        match p {
            Predicate::Var { id } => Predicate2::Var { id: id.to_string() },
            Predicate::And { predicates } => Predicate2::And {
                predicates: predicates
                    .iter()
                    .map(|p| self.convert_predicate(p))
                    .collect(),
            },
            Predicate::Or { predicates } => Predicate2::Or {
                predicates: predicates
                    .iter()
                    .map(|p| self.convert_predicate(p))
                    .collect(),
            },
            Predicate::Not { predicate } => Predicate2::Not {
                predicate: Box::new(self.convert_predicate(predicate)),
            },
            Predicate::Eq { lhs, rhs } => {
                // TODO: Calculate the value of the expression
                if let Expr::Var { id } = lhs {
                    if let Expr::Int { value } = rhs {
                        let linfo = self.var_info(id);
                        return self.int_eq_const_predicate(&linfo, *value);
                    }
                }

                let Expr::Var { id: lid } = lhs else { todo!() };
                let Expr::Var { id: rid } = rhs else { todo!() };
                let linfo = self.var_info(lid);
                let rinfo = self.var_info(rid);
                self.int_eq_predicate(&linfo, &rinfo)
            }
            Predicate::AllDiff { exprs } => {
                let vars = exprs
                    .iter()
                    .map(|e| {
                        let Expr::Var { id } = e else { todo!() };
                        self.var_info(id)
                    })
                    .collect::<Vec<_>>();
                self.all_diff_predicate(&vars)
            }
        }
    }
    fn var_type(&self, id: ID) -> Option<VarType> {
        if self.vars.iter().any(|v| v.id == id) {
            Some(VarType::Int)
        } else if self.bool_vars.iter().any(|v| v.id == id) {
            Some(VarType::Bool)
        } else {
            None
        }
    }
    fn is_bool(&self, id: ID) -> bool {
        self.var_type(id) == Some(VarType::Bool)
    }
    fn is_int(&self, id: ID) -> bool {
        self.var_type(id) == Some(VarType::Int)
    }
    fn var_info(&self, id: &ID) -> VarInfo {
        self.vars.iter().find(|v| v.id == *id).unwrap().clone()
    }
    fn int_var(&self, id: ID, k: usize) -> ID {
        format!("$int_{}_{}", id, k)
    }
    fn int_predicate(&self, int: &VarInfo) -> Vec<Predicate2> {
        let VarInfo { id, min, max } = int;
        let mut res = vec![];
        for k in *min..*max - 1 {
            let id0 = self.int_var(id.clone(), k);
            let id1 = self.int_var(id.clone(), k + 1);
            res.push(Predicate2::Or {
                predicates: vec![
                    Predicate2::Not {
                        predicate: Box::new(Predicate2::Var { id: id1.clone() }),
                    },
                    Predicate2::Var { id: id0.clone() },
                ],
            });
        }
        if *min + 1 == *max {
            // Workaround for the case where width == 1
            let v = Predicate2::Var {
                id: self.int_var(id.clone(), *min),
            };
            res.push(Predicate2::Or {
                predicates: vec![
                    Predicate2::Not {
                        predicate: Box::new(v.clone()),
                    },
                    v,
                ],
            });
        }
        res
    }
    fn false_predicate(&self) -> Predicate2 {
        Predicate2::And {
            predicates: vec![
                Predicate2::Var {
                    id: "$false".to_string(),
                },
                Predicate2::Not {
                    predicate: Box::new(Predicate2::Var {
                        id: "$false".to_string(),
                    }),
                },
            ],
        }
    }
    fn int_eq_predicate(&self, lhs: &VarInfo, rhs: &VarInfo) -> Predicate2 {
        use std::cmp::{max, min};
        let VarInfo {
            id: lid,
            min: lmin,
            max: lmax,
        } = lhs.clone();
        let VarInfo {
            id: rid,
            min: rmin,
            max: rmax,
        } = rhs.clone();
        if lmax < rmin || rmax < lmin {
            return self.false_predicate();
        }
        let (r, l) = (min(rmin, lmin), max(rmax, lmax));
        let mut res = vec![];
        for i in r..l {
            let rvar = Predicate2::Var {
                id: self.int_var(rid.clone(), i),
            };
            let lvar = Predicate2::Var {
                id: self.int_var(lid.clone(), i),
            };
            if rmin <= i && i < lmin {
                res.push(Predicate2::Not {
                    predicate: Box::new(rvar),
                });
            } else if lmin <= i && i < rmin {
                res.push(Predicate2::Not {
                    predicate: Box::new(lvar),
                });
            } else if rmin <= i && i < rmax && lmin <= i && i < lmax {
                res.push(Predicate2::Or {
                    predicates: vec![
                        Predicate2::And {
                            predicates: vec![lvar.clone(), rvar.clone()],
                        },
                        Predicate2::And {
                            predicates: vec![
                                Predicate2::Not {
                                    predicate: Box::new(lvar),
                                },
                                Predicate2::Not {
                                    predicate: Box::new(rvar),
                                },
                            ],
                        },
                    ],
                });
            } else if rmax <= i && i < lmax {
                res.push(Predicate2::Not {
                    predicate: Box::new(lvar),
                });
            } else if lmax <= i && i < rmax {
                res.push(Predicate2::Not {
                    predicate: Box::new(rvar),
                });
            }
        }
        Predicate2::And { predicates: res }
    }

    fn all_diff_predicate(&self, vars: &[VarInfo]) -> Predicate2 {
        let mut res = vec![];
        for i in 0..vars.len() {
            for j in i + 1..vars.len() {
                let vi = &vars[i];
                let vj = &vars[j];
                res.push(Predicate2::Not {
                    predicate: Box::new(self.int_eq_predicate(vi, vj)),
                })
            }
        }
        Predicate2::And { predicates: res }
    }

    fn int_eq_const_predicate(&self, linfo: &VarInfo, value: usize) -> Predicate2 {
        let &VarInfo { ref id, min, max } = linfo;
        if value < min || max < value {
            return self.false_predicate();
        }
        let mut res = vec![];
        for i in min..max {
            let id = self.int_var(id.clone(), i);
            if i < value {
                res.push(Predicate2::Var { id });
            } else {
                res.push(Predicate2::Not {
                    predicate: Box::new(Predicate2::Var { id }),
                });
            }
        }
        Predicate2::And { predicates: res }
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
enum VarType {
    Int,
    Bool,
}

#[derive(Debug, Clone)]
struct IDGen {
    id: usize,
}
impl Default for IDGen {
    fn default() -> Self {
        IDGen { id: 0 }
    }
}
impl IDGen {
    fn gen(&mut self, prefix: &str) -> ID {
        self.id += 1;
        format!("{}{}", prefix, self.id)
    }
}

impl SMT2 {
    fn solve<T: SATSolver>(&self, solver: &T) -> Option<Vec<CnfVar>> {
        let s = self.convert();
        s.solve(solver)
    }
    pub fn convert(&self) -> SMT3 {
        let mut idgen = IDGen::default();
        let cnf = self
            .predicates
            .iter()
            .flat_map(|p| Self::convert_predicate(p, &mut idgen))
            .collect();
        SMT3 { cnf }
    }
    fn convert_predicate(p: &Predicate2, gen: &mut IDGen) -> Vec<Term> {
        match p {
            Predicate2::Var { id } => vec![Term {
                vars: vec![CnfVar::Pos(id.clone())],
            }],
            Predicate2::Not { predicate } => {
                if let Predicate2::Var { id } = &**predicate {
                    vec![Term {
                        vars: vec![CnfVar::Neg(id.clone())],
                    }]
                } else {
                    let p = Self::remove_not(&**predicate);
                    Self::convert_predicate(&p, gen)
                }
            }
            Predicate2::And { predicates } => predicates
                .iter()
                .flat_map(|p| Self::convert_predicate(p, gen))
                .collect(),
            Predicate2::Or { predicates } => {
                let cnf = predicates
                    .iter()
                    .map(|p| Self::convert_predicate(p, gen))
                    .collect::<Vec<_>>();
                let mut vars = vec![];
                let mut predicates = vec![];
                for ps in cnf {
                    let v = CnfVar::pos(gen.gen("$or_"));
                    vars.push(v.clone());
                    let nv = v.invert();
                    let ps = ps.iter().cloned().map(|mut p| {
                        p.vars.push(nv.clone());
                        p
                    });
                    predicates.extend(ps);
                }
                predicates.push(Term { vars });
                predicates
            }
        }
    }
    fn remove_not(p: &Predicate2) -> Predicate2 {
        match p {
            Predicate2::Var { id } => Predicate2::Not {
                predicate: Box::new(Predicate2::Var { id: id.clone() }),
            },
            Predicate2::Not { predicate } => *predicate.clone(),
            Predicate2::And { predicates } => Predicate2::Or {
                predicates: predicates.iter().map(|p| Self::remove_not(p)).collect(),
            },
            Predicate2::Or { predicates } => Predicate2::And {
                predicates: predicates.iter().map(|p| Self::remove_not(p)).collect(),
            },
        }
    }
}

use crate::sat;
impl SMT3 {
    pub fn convert(&self) -> (String, Vec<ID>) {
        let mut vars = vec![];
        let mut res = String::new();
        for cnf in &self.cnf {
            for var in &cnf.vars {
                let index = match vars.iter().position(|v| v == var.id()) {
                    Some(index) => index + 1,
                    None => {
                        let index = vars.len();
                        vars.push(var.id().clone());
                        index + 1
                    }
                };
                if var.is_neg() {
                    res.push_str(&format!("-{} ", index));
                } else {
                    res.push_str(&format!("{} ", index));
                }
            }
            res.push_str("0\n")
        }
        (res, vars)
    }
    fn solve<T: SATSolver>(&self, solver: &T) -> Option<Vec<CnfVar>> {
        let (str, map) = self.convert();
        let cnf = sat::Sat::try_from(str.as_str()).unwrap();
        let res = solver.solve(&cnf);
        let Some(res) = res else { return None };
        let res = res
            .assignment
            .iter()
            .map(|v| match v {
                sat::Var::Pos(i) => CnfVar::Pos(map[*i - 1].clone()),
                sat::Var::Neg(i) => CnfVar::Neg(map[*i - 1].clone()),
            })
            .collect();
        Some(res)
    }
}

impl SMT {
    pub fn parse(s: &str) -> Result<Self, String> {
        let sexprs = SExpr::read_all(s).map_err(|e| e.to_string())?;
        let mut vars = Vec::new();
        let mut bvar = Vec::new();
        let mut predicates = Vec::new();
        for sexpr in sexprs {
            match SMTDef::parse(&sexpr) {
                Ok(SMTDef::Int { id, min, max }) => {
                    vars.push(VarInfo { id, min, max });
                }
                Ok(SMTDef::Bool { id }) => {
                    bvar.push(VarBool { id });
                }
                Ok(SMTDef::Predicate { predicate }) => {
                    predicates.push(predicate);
                }
                Err(e) => return Err(e),
            }
        }
        Ok(SMT {
            vars,
            bool_vars: bvar,
            predicates,
        })
    }
}

impl Display for SMT {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for var in &self.vars {
            write!(f, "int {} {} {}\n", var.id, var.min, var.max)?;
        }
        for var in &self.bool_vars {
            write!(f, "bool {}\n", var.id)?;
        }
        for predicate in &self.predicates {
            write!(f, "{}\n", predicate)?;
        }
        Ok(())
    }
}

impl SMTDef {
    fn parse(sexpr: &SExpr) -> Result<Self, String> {
        match sexpr.name.as_str() {
            "int" => {
                let id = sexpr.args[0].name.clone();
                let min = sexpr.args[1]
                    .name
                    .parse::<usize>()
                    .map_err(|e| e.to_string())?;
                let max = sexpr.args[2]
                    .name
                    .parse::<usize>()
                    .map_err(|e| e.to_string())?;
                Ok(SMTDef::Int { id, min, max })
            }
            "bool" => {
                let id = sexpr.args[0].name.clone();
                Ok(SMTDef::Bool { id })
            }
            "?" => {
                let predicate = Predicate::parse(&sexpr.args[0]).map_err(|e| e.to_string())?;
                Ok(SMTDef::Predicate { predicate })
            }
            c => Err(format!("Invalid SMTDef {}", c)),
        }
    }
}
impl Predicate {
    fn parse(sexpr: &SExpr) -> Result<Self, String> {
        match sexpr.name.as_str() {
            "var" => {
                let id = sexpr.args[0].name.clone();
                Ok(Predicate::Var { id })
            }
            "and" | "or" | "not" => {
                let predicates = sexpr
                    .args
                    .iter()
                    .map(|s| Predicate::parse(s))
                    .collect::<Result<Vec<_>, _>>()?;
                match sexpr.name.as_str() {
                    "and" => Ok(Predicate::And { predicates }),
                    "or" => Ok(Predicate::Or { predicates }),
                    "not" => Ok(Predicate::Not {
                        predicate: Box::new(predicates[0].clone()),
                    }),
                    _ => Err(format!("Invalid Predicate {}", sexpr.name)),
                }
            }
            "eq" | "alldiff" => {
                let exprs = sexpr
                    .args
                    .iter()
                    .map(|s| Expr::parse(s))
                    .collect::<Result<Vec<_>, _>>()?;
                match sexpr.name.as_str() {
                    "eq" => Ok(Predicate::Eq {
                        lhs: exprs[0].clone(),
                        rhs: exprs[1].clone(),
                    }),
                    "alldiff" => Ok(Predicate::AllDiff { exprs }),
                    _ => Err(format!("Invalid Predicate {}", sexpr.name)),
                }
            }
            _ => Err(format!("Invalid Predicate {}", sexpr.name)),
        }
    }
}

impl Display for Predicate {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Predicate::Var { id } => write!(f, "(var {})", id),
            Predicate::And { predicates } => {
                write!(f, "(and")?;
                for p in predicates {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
            Predicate::Or { predicates } => {
                write!(f, "(or")?;
                for p in predicates {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
            Predicate::Not { predicate } => write!(f, "(not {})", predicate),
            Predicate::Eq { lhs, rhs } => write!(f, "(eq {} {})", lhs, rhs),
            Predicate::AllDiff { exprs } => {
                write!(f, "(alldiff")?;
                for e in exprs {
                    write!(f, " {}", e)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Expr {
    fn parse(sexpr: &SExpr) -> Result<Self, String> {
        match sexpr.name.as_str() {
            "var" => {
                let id = sexpr.args[0].name.clone();
                Ok(Expr::Var { id })
            }
            "int" => {
                let value = sexpr.args[0]
                    .name
                    .parse::<usize>()
                    .map_err(|e| e.to_string())?;
                Ok(Expr::Int { value })
            }
            c => Err(format!("Invalid Expr {}", c)),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Expr::Var { id } => write!(f, "(var {})", id),
            Expr::Int { value } => write!(f, "(int {})", value),
        }
    }
}

impl SExpr {
    fn read_all(s: &str) -> Result<Vec<Self>, String> {
        let mut level = 0;
        let mut content = String::new();
        let mut res = Vec::new();
        for c in s.chars() {
            match c {
                '(' => {
                    if level == 0 {
                        content.clear();
                    }
                    content.push(c);
                    level += 1;
                }
                ')' => {
                    level -= 1;
                    content.push(c);
                    if level == 0 {
                        res.push(SExpr::from_str(content.as_str())?);
                    }
                }
                _ => {
                    if level > 0 {
                        content.push(c);
                    }
                }
            }
        }
        Ok(res)
    }
}

impl Display for SMT2 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for p in &self.predicates {
            write!(f, "{}\n", p)?;
        }
        Ok(())
    }
}
impl Display for Predicate2 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Predicate2::Var { id } => write!(f, "(var {})", id),
            Predicate2::And { predicates } => {
                write!(f, "(and")?;
                for p in predicates {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
            Predicate2::Or { predicates } => {
                write!(f, "(or")?;
                for p in predicates {
                    write!(f, " {}", p)?;
                }
                write!(f, ")")
            }
            Predicate2::Not { predicate } => write!(f, "(not {})", predicate),
        }
    }
}

impl Display for SMT3 {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for term in &self.cnf {
            write!(f, "* {}\n", term)?;
        }
        Ok(())
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        for var in &self.vars {
            write!(f, "{} ", var)?;
        }
        Ok(())
    }
}

impl Display for CnfVar {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            CnfVar::Pos(id) => write!(f, "{}", id),
            CnfVar::Neg(id) => write!(f, "-{}", id),
        }
    }
}

#[derive(Debug, Clone)]
enum SToken {
    LParen,
    RParen,
    Atom(String),
}

impl SToken {
    fn from_str(s: &str) -> Self {
        match s {
            "(" => SToken::LParen,
            ")" => SToken::RParen,
            _ => SToken::Atom(s.to_string()),
        }
    }

    fn tokenize(s: &str) -> Vec<Self> {
        let mut res = Vec::new();
        let mut token = String::new();
        for c in s.chars() {
            match c {
                '(' | ')' => {
                    if !token.is_empty() {
                        res.push(SToken::from_str(token.as_str()));
                        token.clear();
                    }
                    res.push(Self::from_str(c.to_string().as_str()));
                }
                ' ' | '\n' | '\t' => {
                    if !token.is_empty() {
                        res.push(SToken::from_str(token.as_str()));
                        token.clear();
                    }
                }
                _ => {
                    token.push(c);
                }
            }
        }
        if !token.is_empty() {
            res.push(SToken::from_str(token.as_str()));
        }
        res
    }
}

impl Display for SExpr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "({}", self.name)?;
        for arg in &self.args {
            write!(f, " {}", arg)?;
        }
        write!(f, ")")
    }
}
impl FromStr for SExpr {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let tokens = SToken::tokenize(s);
        let mut stack = Vec::new();
        let mut name = String::new();
        let mut args = Vec::new();
        for token in tokens {
            match token {
                SToken::LParen => {
                    stack.push(SExpr {
                        name: name.clone(),
                        args: args.clone(),
                    });
                    name.clear();
                    args.clear();
                }
                SToken::RParen => {
                    let mut expr = stack.pop().unwrap();
                    expr.args.push(SExpr {
                        name: name.clone(),
                        args: args.clone(),
                    });
                    name = expr.name;
                    args = expr.args;
                }
                SToken::Atom(s) => {
                    if name.is_empty() {
                        name = s;
                    } else {
                        args.push(SExpr {
                            name: s,
                            args: Vec::new(),
                        });
                    }
                }
            }
        }
        Ok(args[0].clone())
    }
}

#[cfg(test)]
mod test {
    use crate::cdcl;

    use super::*;
    #[test]
    fn smt() {
        fn smt_test(s: &str) {
            let res = SMT::parse(s).unwrap();
            print!("# raw:\n{}", res);
            let c2 = res.convert();
            print!("# c2:\n{}", c2);
            let c3 = c2.convert();
            print!("# c3: \n{}", c3);
            let cnf = c3.convert();
            print!("# cnf:\n{}", cnf.0);
            print!("# vars:\n{:?}", cnf.1);
            let solver = &cdcl::CDCLSolver::new();
            let res = res.solve(solver);
            print!("# result:\n {:?}", res);
        }
        smt_test("(int x 0 3) (bool y) (? (var y))");
        smt_test("(int x 0 3) (int y 1 4) (? (eq (var x) (var y)))");
        smt_test("(int x 0 1) (int y 1 2) (? (alldiff (var x) (var y)))");
        smt_test("(bool x) (bool y) (? (not (or (and (var x) (var y)) (and (not (var x)) (not (var y))))))");
        smt_test("(int x 1 2) (int y 1 2) (? (alldiff (var x) (var y)))");
        smt_test("(int x 1 2) (int y 1 2) (? (and (eq (var x) (int 2)) (eq (var y) (int 1))))");
        smt_test("(bool x0) (bool y0) (?(not (or (and (var x0) (var y0)) (and (not (var x0)) (not (var y0))))))")
    }
    #[test]
    fn smt2() {
        fn v(id: &str) -> Predicate2 {
            Predicate2::Var { id: id.to_string() }
        }
        let s = SMT2 {
            predicates: vec![
                v("a"),
                Predicate2::And {
                    predicates: vec![v("a"), v("b")],
                },
                Predicate2::Or {
                    predicates: vec![v("a"), v("b")],
                },
                Predicate2::Not {
                    predicate: Box::new(v("a")),
                },
            ],
        };
        dbg!(s.convert());

        let s = SMT2 {
            predicates: vec![
                Predicate2::Or {
                    predicates: vec![
                        Predicate2::And {
                            predicates: vec![v("a"), v("b")],
                        },
                        Predicate2::And {
                            predicates: vec![v("a"), v("c")],
                        },
                    ],
                },
                Predicate2::Not {
                    predicate: Box::new(v("a")),
                },
            ],
        };
        let solver = &sat::DPLLSolver::new();
        dbg!(s.solve(solver));
    }

    #[test]
    fn smt3() {
        let s = SMT3 {
            cnf: vec![
                Term {
                    vars: vec![CnfVar::Pos("a".to_string())],
                },
                Term {
                    vars: vec![CnfVar::Neg("b".to_string())],
                },
            ],
        };
        let solver = &sat::DPLLSolver::new();
        dbg!(s.solve(solver));
    }
    #[test]
    fn read_smt() {
        let s = "(int x 0 3) (bool y) (? (var y))";
        let res = SMT::parse(s).unwrap();
        dbg!(res);
        let s = "(? (and (var x) (or (var y) (not (var z)))))";
        let res = SMT::parse(s).unwrap();
        dbg!(res);
    }

    #[test]
    fn read_sexpr() {
        let s = "(a b)";
        let res = SExpr::from_str(s).unwrap();
        dbg!(res.to_string());
        let s = "(a (b c) d)";
        let res = SExpr::from_str(s).unwrap();
        dbg!(res.to_string());
    }
    #[test]
    fn read_all_sexpr() {
        let s = "(a b) (a (b c))";
        let res = SExpr::read_all(s).unwrap();
        assert_eq!(res.len(), 2);
        let str = res
            .iter()
            .map(|s| s.to_string())
            .collect::<Vec<_>>()
            .join(" ");
        dbg!(str);
    }
}
