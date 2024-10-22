use std::{
    collections::HashSet,
    fmt::{self, Display, Formatter},
};

use crate::sat::{Cnf, SATSolver, Sat, SatResult, Var};

#[derive(Debug, Clone)]
pub struct CDCLSolver {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverEffect {
    Backtrack,
    Continue,
    Unsat,
}

impl SATSolver for CDCLSolver {
    fn solve(&self, sat: &Sat) -> Option<SatResult> {
        self.solve(sat)
    }
}

impl CDCLSolver {
    pub fn new() -> Self {
        CDCLSolver {}
    }
    pub fn solve(&self, sat: &Sat) -> Option<SatResult> {
        let mut sat = sat.clone();
        let vars = sat.vars().iter().map(|v| v.id()).collect::<Vec<_>>();
        let mut trail = Trail::new();
        while trail.determined_vars().len() < vars.len() {
            println!("sat={} trail={}", sat.predicates.len(), trail.stack.len());
            let found = Self::unit_propagate(&sat, &mut trail);
            match Self::backtrack(&mut sat, &mut trail) {
                SolverEffect::Backtrack => continue,
                SolverEffect::Unsat => return None,
                SolverEffect::Continue => (),
            }
            if found {
                continue;
            }
            let Some(var) = Self::choose_literal(&sat, &trail) else {
                break;
            };
            trail.push_decision(var);
            match Self::backtrack(&mut sat, &mut trail) {
                SolverEffect::Backtrack => continue,
                SolverEffect::Unsat => return None,
                SolverEffect::Continue => (),
            }
        }
        Some(SatResult::new(trail.determined_vars()))
    }

    fn unit_propagate(sat: &Sat, trail: &mut Trail) -> bool {
        for (reason, cnf) in sat.predicates.iter().enumerate() {
            if let Some(unit_var) = trail.unit_var(cnf) {
                trail.push_reason(unit_var, reason);
                return true;
            }
        }
        false
    }

    fn choose_literal(sat: &Sat, trail: &Trail) -> Option<Var> {
        let trail_vars = trail
            .determined_vars()
            .iter()
            .map(|v| v.id())
            .collect::<HashSet<_>>();
        for cnf in &sat.predicates {
            if cnf.satisfied_by(&trail.determined_vars()) {
                continue;
            }
            for var in &cnf.clauses {
                if !trail_vars.contains(&var.id()) {
                    return Some(*var);
                }
            }
        }
        None
        /* // slow scoring
        let tally = sat.tally();
        let vars = Self::all_free_vars(sat, trail);
        vars.iter().max_by_key(|var| tally[var.id()]).copied()
        */
    }

    fn all_free_vars(sat: &Sat, trail: &Trail) -> Vec<Var> {
        let mut vars = vec![];
        let trail_vars = trail
            .determined_vars()
            .iter()
            .map(|v| v.id())
            .collect::<HashSet<_>>();
        for cnf in &sat.predicates {
            if cnf.satisfied_by(&trail.determined_vars()) {
                continue;
            }
            for var in &cnf.clauses {
                if vars.contains(var) {
                    continue;
                }
                if !trail_vars.contains(&var.id()) {
                    vars.push(*var);
                }
            }
        }
        vars
    }

    fn backtrack(sat: &mut Sat, trail: &mut Trail) -> SolverEffect {
        let vars = trail.determined_vars();
        for cnf in &sat.predicates {
            if trail.contradiction(cnf, &vars) {
                if trail.decision_level() == 0 {
                    return SolverEffect::Unsat;
                }
                let cnf = trail.contradiction_infer(sat, cnf);
                sat.push(cnf);
                return SolverEffect::Backtrack;
            }
        }
        SolverEffect::Continue
    }
}

#[derive(Debug, Clone, Copy)]
struct TrailEntry {
    var: Var,
    decision_level: usize,
    reason: Option<CNFIndex>,
}

#[derive(Debug, Clone)]
struct Trail {
    stack: Vec<TrailEntry>,
}

type CNFIndex = usize;
impl Trail {
    fn new() -> Self {
        Trail { stack: Vec::new() }
    }

    fn determined_vars(&self) -> Vec<Var> {
        self.stack.iter().map(|entry| entry.var).collect()
    }

    fn unit_var(&self, cnf: &Cnf) -> Option<Var> {
        let mut ex_count = 0;
        let mut last_ex = None;
        let vars = self.determined_vars();
        for var in &cnf.clauses {
            if vars.contains(&var.invert()) {
                continue;
            }
            if vars.contains(var) {
                return None;
            }
            ex_count += 1;
            last_ex = Some(var);
            if ex_count > 1 {
                return None;
            }
        }
        last_ex.copied()
    }

    fn push_reason(&mut self, unit_var: Var, reason: CNFIndex) {
        self.stack.push(TrailEntry {
            var: unit_var,
            decision_level: self.decision_level(),
            reason: Some(reason),
        })
    }

    fn decision_level(&self) -> usize {
        if let Some(last) = self.stack.last() {
            return last.decision_level;
        }
        return 0;
    }

    fn push_decision(&mut self, var: Var) {
        self.stack.push(TrailEntry {
            var,
            decision_level: self.decision_level() + 1,
            reason: None,
        });
    }

    fn include(&self, var: Var) -> bool {
        self.determined_vars().iter().any(|v| *v == var)
    }

    fn include_id(&self, id: usize) -> bool {
        self.determined_vars().iter().any(|v| v.id() == id)
    }

    fn contradiction(&self, cnf: &Cnf, vars: &[Var]) -> bool {
        cnf.clauses.iter().all(|var| vars.contains(&var.invert()))
    }

    fn contradiction_infer(&mut self, sat: &Sat, cnf: &Cnf) -> Cnf {
        /*
        contra = !A !B !C  -> ant
        imply  =  A  Y  Z  -> cons
        infer = !B !C Y Z
        if another imply B U V
        infer =  !C Y Z U
        */
        let last_entry = self.stack.pop().unwrap();
        let last_var = last_entry.var;
        let last_reason = &sat.predicates[last_entry.reason.unwrap()];

        let mut ant = cnf.drop_var(last_var.invert()).unwrap();
        let mut cons = last_reason.drop_var(last_var).unwrap();

        for entry in self.max_level_entries() {
            let Some(reason) = entry.reason else {
                continue;
            };
            if !ant.include(entry.var.invert()) {
                continue;
            }
            ant = ant.drop_var(entry.var.invert()).unwrap();
            cons.extend(&sat.predicates[reason].drop_var(entry.var).unwrap());
            cons.dedup();
        }

        let max_level = self.search_max_level(&ant, &cons);
        self.drop_after_level(max_level);

        ant.extend(&cons);
        ant.dedup();
        ant
    }

    fn max_level_entries(&self) -> Vec<&TrailEntry> {
        let current_level = self.decision_level();
        let mut entries = vec![];
        for entry in self.stack.iter().rev() {
            if entry.decision_level < current_level {
                break;
            }
            entries.push(entry);
        }
        entries
    }

    fn search_max_level(&self, ant: &Cnf, cons: &Cnf) -> usize {
        let mut max_level = 0;
        let current_level = self.decision_level();
        for entry in self.stack.iter() {
            if entry.decision_level == current_level {
                continue;
            }
            let ant_included = ant.clauses.iter().any(|var| var.invert() == entry.var);
            let cons_included = cons.clauses.iter().any(|var| var == &entry.var);
            if (ant_included || cons_included) && entry.decision_level > max_level {
                max_level = entry.decision_level;
            }
        }
        max_level
    }

    fn drop_after_level(&mut self, level: usize) {
        self.stack.retain(|entry| entry.decision_level <= level);
    }
}

impl Display for Trail {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "Trail: [")?;
        for entry in &self.stack {
            write!(
                f,
                "({}, {}, {}), ",
                entry.var,
                entry.decision_level,
                entry.reason.map_or("_".to_owned(), |r| r.to_string())
            )?;
        }
        write!(f, "]")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::{Cnf, Sat, Var};

    #[test]
    fn test_contradiction_infer() {
        fn run_sat(sat: &str) {
            let sat = Sat::try_from(sat).unwrap();
            let solver = CDCLSolver::new();
            solver.solve(&sat);
        }
        /*
           1 2 <- decide 1 lv1
           -1 3 <- unit 3 lv1
           -1 -3 <- contradiction
        */
        //run_sat("1 2 0 -1 3 0 -1 -3 0");
        /*
           1 2 <- decide 1 lv1
           2 3 <- decide 2 lv2
           -2 3 <- unit 3 lv2
           -1 4 5 <- decide 4 lv3
           -4 6 <- unit 6 lv3
           -4 -1 -6 <- contradiction 6
           = reason -4 6
           = imply 1 5 1 6
        run_sat("1 2 0 2 3 0 -2 3 0 -1 4 5 0 -4 6 0 -4 -1 -6 0");
        */
        run_sat(
            "
2 5 -3 0
1 -6 -3 0
4 -7 -3 0
6 7 -3 0
3 0",
        )
    }
}
