# NeedlemanWunschLean

Formally verified Needleman–Wunsch global sequence alignment in Lean 4.

This project implements the classic dynamic-programming score of
Needleman and Wunsch (1970) as a function
`nw : (α → α → Int) → Int → List α → List α → Int` over an abstract
alphabet `α`, with machine-checked proofs of:

- **Base cases** (`nw_nil_left`, `nw_nil_right`): aligning either sequence against an empty string gives `gap * length`.
- **Bellman recurrence** (`nw_bellman`): the standard three-way maximum over diagonal, up, and left moves.
- **Lower bounds** (`nw_lower_bound_diag`, `_up`, `_left`): each of the three recursive candidates is a valid lower bound on the optimal score.
- **Optimality attainment** (`nw_achieves_one_of_three`): the optimal score is exactly one of the three candidate values.
- **Monotonicity in the scoring function** (`nw_mono_in_score`): if `s₁ a b ≤ s₂ a b` pointwise, then `nw s₁ g xs ys ≤ nw s₂ g xs ys` for all inputs.

Built with **Lean 4.11.0**, no `mathlib` dependency, pure core Lean.

## Build

```bash
elan default leanprover/lean4:v4.11.0
lake build
```

## Concrete examples (`#eval` in `Basic.lean`)

| Inputs | NW score |
|---|---|
| `GATTACA` vs `GCATGCU` (match=+1, mismatch=-1, gap=-2) | -1 |
| `HELLO` vs `HELLO` | 5 |
| `ABC` vs empty | -6 |
| empty vs `XYZ` | -6 |
| `GATTACA` vs `GATTACA` | 7 |

## File layout

```
NeedlemanWunschLean/
├── NeedlemanWunschLean.lean       -- library entry point
├── NeedlemanWunschLean/Basic.lean -- DP definition + all theorems
├── lakefile.lean                  -- Lake build config
├── lean-toolchain                 -- pinned to leanprover/lean4:v4.11.0
└── README.md
```

## Roadmap

- [x] DP definition with well-founded termination on `|xs| + |ys|`
- [x] Base cases + Bellman recurrence as theorems
- [x] Monotonicity in the scoring function
- [ ] Traceback: define an alignment data structure and a function returning an alignment achieving the optimal score
- [ ] Prove `score(traceback xs ys) = nw s g xs ys`
- [ ] Symmetry: under a symmetric scoring function, `nw s g xs ys = nw s g ys xs`
- [ ] Migrate to `Mathlib` and port to a `mathlib-bio` starter library

## Why this project

This is the theorem-prover complement of a mathematical-oncology portfolio (NMF mutation signatures, Cox PH survival, DP-mixture clonal evolution). It shows that alignment algorithms — the computational core of modern bioinformatics — can be mechanically checked by a proof assistant and therefore trusted in high-stakes clinical contexts.

## References

- S. B. Needleman and C. D. Wunsch. A general method applicable to the search for similarities in the amino acid sequence of two proteins. *J. Mol. Biol.* 48:443–453, 1970.
- The Lean 4 Theorem Prover. <https://lean-lang.org/>.
