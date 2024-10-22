# CDCL SAT Solver and Simpl Integer SMT Solver

- Sample: Sudoku Solver

```
vec![
    vec![1, 0, 0, 3],
    vec![0, 0, 1, 0],
    vec![0, 0, 4, 0],
    vec![0, 2, 0, 0],
],
$ cargo run --release
sat=2136 trail=992
1 4 2 3
2 3 1 4
3 1 4 2
4 2 3 1
```

## References

- [CDCL (conflict-driven clause learning) アルゴリズムの SAT ソルバーを作る](https://zenn.dev/termoshtt/scraps/ae3372d290ed75)
