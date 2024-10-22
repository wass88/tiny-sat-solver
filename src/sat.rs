use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

pub trait SATSolver {
    fn solve(&self, sat: &Sat) -> Option<SatResult>;
}

#[derive(Debug, Clone)]
pub struct DPLLSolver {}
impl SATSolver for DPLLSolver {
    fn solve(&self, sat: &Sat) -> Option<SatResult> {
        let Some(mut assign) = self.solve_assign(sat) else {
            return None;
        };
        let vars = sat.vars();
        assign.extend_unused(vars);
        Some(assign)
    }
}
impl DPLLSolver {
    pub fn new() -> Self {
        DPLLSolver {}
    }
    fn solve_assign(&self, sat: &Sat) -> Option<SatResult> {
        let mut assignment = SatResult::default();
        let Some(sat) = Self::unit_propagate(sat, &mut assignment) else {
            return None;
        };

        let sat = Self::pure_literal_elimination(&sat, &mut assignment);
        if sat.is_empty() {
            return Some(assignment);
        }
        if sat.has_empty_clause() {
            return None;
        }
        let l = self.choose_literal(&sat);
        println!("Choosing literal: {} {:?}", l, sat.counts());
        let (pos, neg) = Self::split_literal(&sat, l);
        if let Some(pop_result) = self.solve(&pos) {
            assignment.extend(&pop_result);
            return Some(assignment);
        }
        if let Some(neg_result) = self.solve(&neg) {
            assignment.extend(&neg_result);
            return Some(assignment);
        }
        None
    }
    fn unit_propagate(sat: &Sat, assignment: &mut SatResult) -> Option<Sat> {
        let mut res = Sat::default();
        let mut for_subst = Vec::new();
        for cnf in &sat.predicates {
            if let Some(var) = cnf.get_singleton() {
                match assignment.push_ok(var) {
                    Ok(_) => for_subst.push(var),
                    Err(true) => continue,
                    Err(false) => return None,
                }
            } else {
                res.push(cnf.clone());
            }
        }
        for var in for_subst {
            res = res.remove_var(var);
        }
        Some(res)
    }
    fn pure_literal_elimination(sat: &Sat, assignment: &mut SatResult) -> Sat {
        let mut res = sat.clone();
        let pure_literals = sat.pure_literals();
        for var in pure_literals {
            match assignment.push_ok(var) {
                Ok(_) => (),
                Err(true) => (),
                Err(false) => unreachable!(),
            }
            res = res.remove_var(var);
        }
        res
    }
    fn choose_literal(&self, sat: &Sat) -> Var {
        sat.predicates[0].clauses[0]
    }
    fn split_literal(sat: &Sat, l: Var) -> (Sat, Sat) {
        let mut pos = sat.clone();
        pos.push(Cnf::singleton(l));
        let mut neg = sat.clone();
        neg.push(Cnf::singleton(l.invert()));
        (pos, neg)
    }
}

#[derive(Debug, Clone)]
pub struct SatResult {
    pub assignment: Vec<Var>,
}
impl SatResult {
    pub fn new(assignment: Vec<Var>) -> Self {
        SatResult { assignment }
    }
    fn push_ok(&mut self, var: Var) -> Result<Var, bool> {
        if self.assignment.contains(&var.invert()) {
            return Err(false);
        }
        if self.assignment.contains(&var) {
            return Err(true);
        }
        self.assignment.push(var);
        Ok(var)
    }
    fn include(&self, var: Var) -> bool {
        self.assignment.contains(&var)
    }
    fn extend(&mut self, other: &SatResult) {
        for var in &other.assignment {
            let res = self.push_ok(var.clone());
            if res == Err(false) {
                panic!("Conflict");
            }
        }
    }
    fn extend_unused(&mut self, vars: Vec<Var>) {
        for var in vars {
            if self.include(var) {
                continue;
            }
            if self.include(var.invert()) {
                continue;
            }
            self.assignment.push(var);
        }
    }
}
impl Default for SatResult {
    fn default() -> Self {
        SatResult {
            assignment: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Sat {
    pub predicates: Vec<Cnf>,
}
impl Sat {
    fn is_empty(&self) -> bool {
        self.predicates.is_empty()
    }
    fn has_empty_clause(&self) -> bool {
        self.predicates.iter().any(|cnf| cnf.is_empty())
    }
    pub fn push(&mut self, cnf: Cnf) {
        self.predicates.push(cnf);
    }
    fn remove_var(&self, var: Var) -> Self {
        let res = self
            .predicates
            .iter()
            .filter_map(|cnf| cnf.remove_var(var))
            .collect();
        Sat { predicates: res }
    }
    fn is_pure(&self, var: Var) -> bool {
        let mut pos = false;
        let mut neg = false;
        for cnf in &self.predicates {
            if cnf.include(var) {
                pos = true;
            }
            if cnf.include(var.invert()) {
                neg = true;
            }
        }
        pos & !neg
    }
    fn pure_literals(&self) -> Vec<Var> {
        let mut res = Vec::new();
        for var in &self.vars() {
            if self.is_pure(*var) {
                res.push(*var);
            }
        }
        res
    }

    pub fn vars(&self) -> Vec<Var> {
        let mut res = Vec::new();
        for cnf in &self.predicates {
            for var in &cnf.clauses {
                if res.contains(var) {
                    continue;
                }
                res.push(*var);
            }
        }
        res
    }

    fn counts(&self) -> (usize, usize) {
        let lines = self.predicates.len();
        let mut ids = vec![];
        for cnf in &self.predicates {
            for var in &cnf.clauses {
                let id = var.id();
                if ids.contains(&id) {
                    continue;
                }
                ids.push(id);
            }
        }
        (lines, ids.len())
    }

    pub fn tally(&self) -> Vec<(Var, usize)> {
        let mut res = HashMap::new();
        for cnf in &self.predicates {
            for var in &cnf.clauses {
                let count = res.entry(*var).or_insert(0);
                *count += 1;
            }
        }
        res.iter().map(|(k, v)| (*k, *v)).collect()
    }
}
impl Default for Sat {
    fn default() -> Self {
        Sat {
            predicates: Vec::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Cnf {
    pub clauses: Vec<Var>,
}
impl Cnf {
    fn is_empty(&self) -> bool {
        self.clauses.is_empty()
    }
    fn singleton(var: Var) -> Self {
        Cnf { clauses: vec![var] }
    }
    fn get_singleton(&self) -> Option<Var> {
        if self.clauses.len() == 1 {
            Some(self.clauses[0])
        } else {
            None
        }
    }
    pub fn remove_var(&self, var: Var) -> Option<Self> {
        if self.include(var) {
            return None;
        }
        let clauses = self
            .clauses
            .iter()
            .filter(|v| v != &&var.invert())
            .cloned()
            .collect();
        Some(Cnf { clauses })
    }
    pub fn drop_var(&self, var: Var) -> Option<Self> {
        if !self.include(var) {
            return None;
        }
        let clauses = self
            .clauses
            .iter()
            .filter(|v| v != &&var)
            .cloned()
            .collect();
        Some(Cnf { clauses })
    }
    pub fn include(&self, var: Var) -> bool {
        self.clauses.contains(&var)
    }
    pub fn extend(&mut self, other: &Cnf) {
        self.clauses.extend(&other.clauses);
    }

    pub fn satisfied_by(&self, determined_vars: &[Var]) -> bool {
        for var in &self.clauses {
            if determined_vars.contains(var) {
                return true;
            }
        }
        false
    }

    pub fn dedup(&mut self) {
        self.clauses.sort();
        self.clauses.dedup();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Var {
    Pos(usize),
    Neg(usize),
}

impl Var {
    fn pos(i: usize) -> Self {
        if i == 0 {
            panic!("Zero is not a valid variable number");
        }
        Var::Pos(i)
    }
    fn neg(i: usize) -> Self {
        if i == 0 {
            panic!("Zero is not a valid variable number");
        }
        Var::Neg(i)
    }
    pub fn invert(&self) -> Self {
        match self {
            Var::Pos(i) => Var::neg(*i),
            Var::Neg(i) => Var::pos(*i),
        }
    }
    pub fn id(self) -> usize {
        match self {
            Var::Pos(i) => i,
            Var::Neg(i) => i,
        }
    }
}

// Input and Output

impl Display for Var {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Var::Pos(i) => write!(f, " {}", i),
            Var::Neg(i) => write!(f, "-{}", i),
        }
    }
}

impl TryFrom<&str> for Var {
    type Error = &'static str;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let mut chars = s.chars();
        let first = chars.next().ok_or("Empty string")?;
        let rest = chars.as_str();
        if first == '-' {
            let number = rest.parse().map_err(|_| "Invalid number")?;
            if number == 0 {
                return Err("Zero is not a valid variable number");
            }
            Ok(Var::neg(number))
        } else {
            let number = s.parse().map_err(|_| "Invalid number")?;
            if number == 0 {
                return Err("Zero is not a valid variable number");
            }
            Ok(Var::pos(number))
        }
    }
}

impl Display for Cnf {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut first = true;
        for clause in &self.clauses {
            if first {
                first = false;
            } else {
                write!(f, " ")?;
            }
            write!(f, "{}", clause)?;
        }
        Ok(())
    }
}

impl TryFrom<&str> for Cnf {
    type Error = &'static str;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let mut clauses = Vec::new();
        for clause in s.trim().split_whitespace() {
            let var = Var::try_from(clause)?;
            clauses.push(var);
        }
        Ok(Cnf { clauses })
    }
}

impl Display for Sat {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let mut first = true;
        for cnf in &self.predicates {
            if first {
                first = false;
            } else {
                write!(f, "\n")?;
            }
            write!(f, "{}", cnf)?;
        }
        Ok(())
    }
}

impl TryFrom<&str> for Sat {
    type Error = &'static str;

    fn try_from(s: &str) -> Result<Self, Self::Error> {
        let mut predicates = Vec::new();
        let mut cnf = String::new();
        for clause in s.split_whitespace() {
            if clause == "0" {
                predicates.push(Cnf::try_from(cnf.as_str())?);
                cnf.clear();
            } else {
                cnf.push_str(clause);
                cnf.push(' ');
            }
        }
        if !cnf.is_empty() {
            return Err("Missing zero at the end of the input");
        }
        Ok(Sat { predicates })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_solver() {
        let solver = DPLLSolver {};
        let input = "1 -1 -3 0 -2 2 -3 0";
        let sat = Sat::try_from(input).unwrap();
        let result = solver.solve(&sat);
        assert!(result.is_some());
        let result = result.unwrap();
        assert_eq!(result.assignment.len(), 3);
        assert!(result.assignment.contains(&Var::neg(3)));
        dbg!(&result);
    }
    #[test]
    fn test_solver2() {
        let solver = DPLLSolver {};
        let input = "-1 -2 -3 0
2 5 -3 0
1 -6 -3 0
4 -7 -3 0
6 7 -3 0
3 0";
        let sat = Sat::try_from(input).unwrap();
        let result = solver.solve(&sat);
        dbg!(&result);
    }
    #[test]
    fn test_from_str_sat() {
        let input = "1 2 3 0 -1 -2 0";
        let sat = Sat::try_from(input).unwrap();
        assert_eq!(sat.predicates.len(), 2);
        assert_eq!(sat.predicates[0].clauses.len(), 3);
        assert_eq!(sat.predicates[1].clauses.len(), 2);
    }
}
