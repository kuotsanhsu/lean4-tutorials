## Unfolding

- https://leanprover-community.github.io/archive/stream/113489-new-members/topic/Unfold.20all.20definitions.html

## λP2

- https://news.ycombinator.com/item?id=27572561

## mvcgen

- RFC: "Safe" monadic assertions for use with `mvcgen` [#9580](https://github.com/leanprover/lean4/issues/9580)
    ```lean
    noncomputable def setZero : StateM (Array Nat) Unit := do
    let mut i := 0
    let len := (← get).size
    for _ in [0:len] do
        let ns ← get
        let h : i < ns.size := sorry -- need proof that `i < ns.size`
        modify fun _ => ns.set i 0 h
        i := i + 1
    -- What about `assert!`?
    ```
- mvcgen can produce proofs with unassigned metavariables [#10564](https://github.com/leanprover/lean4/issues/10564)
- https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#tactic-ref-mvcgen

## io_uring

- [Algebra: Notes from the Underground](https://www.amazon.com/Algebra-Underground-Cambridge-Mathematical-Textbooks-ebook/dp/B095KFLPLP)
- [The Low-level io_uring Interface](https://unixism.net/loti/low_level.html)
- [io_uring by example: Part 1 – Introduction](https://unixism.net/2020/04/io-uring-by-example-part-1-introduction/)
