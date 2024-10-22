use tiny_sat_solver::{cdcl::CDCLSolver, sat::DPLLSolver, sudoku::Sudoku};

fn main() {
    let sudoku = Sudoku::from_board(
        vec![
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
            vec![0, 0, 0, 0, 0, 0, 0, 0, 0],
        ],
        3,
        3,
    );
    let sudoku = Sudoku::from_board(
        vec![
            vec![1, 0, 0, 3],
            vec![0, 0, 1, 0],
            vec![0, 0, 4, 0],
            vec![0, 2, 0, 0],
        ],
        2,
        2,
    );
    let solver = CDCLSolver::new();
    let solution = sudoku.solve(&solver);
    println!("{}", solution.unwrap());
}
