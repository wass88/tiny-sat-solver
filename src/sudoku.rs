use crate::{
    sat::SATSolver,
    smt::{SMTResult, SMT},
};
use std::{cell, vec};

#[derive(Debug, Clone)]
pub struct Sudoku {
    board: Vec<Vec<usize>>,
    cell_width: usize,
    cell_height: usize,
}
impl Sudoku {
    pub fn empty(cell_width: usize, cell_height: usize) -> Self {
        let width = cell_width * cell_height;
        let board = vec![vec![0; width]; width];
        Sudoku {
            board,
            cell_width,
            cell_height,
        }
    }
    pub fn from_board(board: Vec<Vec<usize>>, cell_width: usize, cell_height: usize) -> Self {
        Sudoku {
            board,
            cell_width,
            cell_height,
        }
    }
    pub fn solve<T: SATSolver>(&self, solver: &T) -> Option<Sudoku> {
        let smt = self.convert();
        let smt = SMT::parse(&smt).unwrap();
        let smt1 = smt.convert();
        let smt2 = smt.convert().convert();
        let (sat, vars) = smt.convert().convert().convert();
        println!("==== smt:\n {}", smt);
        println!("==== smt1:\n {}", smt1);
        println!("==== smt2:\n {}", smt2);
        println!("=== sat: {}", sat);
        println!("vars: {:?}", vars);

        let Some(res) = smt.solve(solver) else {
            return None;
        };
        Some(self.remap(&res))
    }
    fn remap(&self, result: &SMTResult) -> Sudoku {
        let size = self.cell_width * self.cell_height;
        let mut board = self.clone();
        for y in 0..size {
            for x in 0..size {
                let var = format!("b_{}_{}", x, y);
                let val = result.vars.iter().find(|(k, _)| k == &var).unwrap().1;
                board.board[y][x] = val;
            }
        }
        board
    }
    fn convert(&self) -> String {
        let max_num = self.cell_width * self.cell_height;
        let mut res = String::new();
        fn var_num(y: usize, x: usize) -> String {
            format!("(var b_{}_{})", x, y)
        }
        for y in 0..max_num {
            for x in 0..max_num {
                res.push_str(&format!("(int b_{}_{} 1 {})\n", x, y, max_num));
            }
        }
        for y in 0..max_num {
            res.push_str("(? (alldiff");
            for x in 0..max_num {
                res.push_str(&format!(" {}", var_num(x, y)));
            }
            res.push_str("))\n");
        }
        for x in 0..max_num {
            res.push_str("(? (alldiff");
            for y in 0..max_num {
                res.push_str(&format!(" {}", var_num(x, y)));
            }
            res.push_str("))\n");
        }
        for cy in 0..self.cell_width {
            for cx in 0..self.cell_height {
                res.push_str("(? (alldiff");
                for y in 0..self.cell_height {
                    for x in 0..self.cell_width {
                        res.push_str(&format!(
                            " {}",
                            var_num(cx * self.cell_width + x, cy * self.cell_width + y)
                        ));
                    }
                }
                res.push_str("))\n");
            }
        }
        for y in 0..max_num {
            for x in 0..max_num {
                if self.board[y][x] != 0 {
                    res.push_str(&format!(
                        "(? (eq {} (int {})))\n",
                        var_num(x, y),
                        self.board[y][x]
                    ));
                }
            }
        }
        res
    }
}

impl std::fmt::Display for Sudoku {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let size = self.cell_width * self.cell_height;
        for y in 0..size {
            for x in 0..size {
                write!(f, "{}", self.board[x][y])?;
                if x != size - 1 {
                    write!(f, " ")?;
                }
            }
            write!(f, "\n")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    #[test]
    fn test_sudoku() {
        let mut sudoku = Sudoku::empty(1, 2);
        sudoku.board[0][0] = 2;
        let solver = &crate::sat::DPLLSolver::new();
        println!("{}", sudoku.solve(solver).unwrap());
    }
    use super::*;
    #[test]
    fn test_sudoku_cdcl() {
        let mut sudoku = Sudoku::empty(2, 2);
        sudoku.board[0][0] = 2;
        let solver = &crate::cdcl::CDCLSolver::new();
        println!("{}", sudoku.solve(solver).unwrap());
    }
}
