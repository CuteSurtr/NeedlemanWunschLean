# NeedlemanWunschLean

Formally verified Needleman–Wunsch global sequence alignment in Lean 4
with `mathlib`.

This project implements the classic dynamic-programming score of
Needleman and Wunsch (1970) as a function
`nw : (α → α → Int) → Int → List α → List α → Int` over an abstract
alphabet `α`, together with a traceback function `align` and 38
machine-checked theorems about both. There are no `sorry`, `admit`, or
`axiom` uses anywhere in the source.

## What is verified

**Core DP (`Basic.lean`)**

- `nw_nil_left`, `nw_nil_right` — base cases: aligning either sequence against an empty string gives `gap * length`.
- `nw_bellman` — the three-way maximum over diagonal, up, and left moves.
- `nw_lower_bound_diag` / `_up` / `_left` — each candidate is a valid lower bound on the optimum.
- `nw_achieves_one_of_three` — the optimum is exactly one of the three candidates.
- `nw_mono_in_score` — if `s₁ ≤ s₂` pointwise then `nw s₁ g xs ys ≤ nw s₂ g xs ys`.

**Alignment, traceback, and optimality (`Alignment.lean`)**

- `align` — greedy traceback producing an `Alignment α := List (AlignStep α)`.
- `toXs_align`, `toYs_align` — projecting out the two sequences recovers `xs` and `ys`.
- `alignScore_nil_left`, `alignScore_nil_right` — arithmetic base cases.
- `alignScore_eq_nw` — **score of the traceback equals the DP optimum**.
- `nw_lower_bound_delete`, `nw_lower_bound_insert` — generalised lower bounds allowing empty second sequence.
- `alignScore_le_nw_project` — every well-formed alignment's score is bounded by the DP optimum of its projected sequences.
- `align_is_optimal` — **for every alignment `a` with `toXs a = xs` and `toYs a = ys`, `alignScore a ≤ alignScore (align xs ys)`**. This is the full correctness theorem for the DP.
- `nw_symm_of_symmetric_score` — under a symmetric scoring function, `nw s g xs ys = nw s g ys xs`.
- `alignScore_append`, `toXs_append`, `toYs_append` — structural lemmas.
- `diagSelf`, `alignScore_diagSelf`, `nw_ge_diag_self_score` — the self-alignment is a lower bound on `nw s g xs xs`.
- `example_hello_self`, `example_gattaca_self`, `example_abc_empty`, `example_empty_xyz`, `align_hello_self_correct` — concrete `native_decide`-proved identities.

## Build

```bash
elan default leanprover/lean4:v4.11.0
lake update   # fetches mathlib via the community binary cache (fast)
lake build
```

## Concrete examples

| Inputs | NW score |
|---|---|
| `GATTACA` vs `GCATGCU` (match=+1, mismatch=-1, gap=-2) | -1 |
| `HELLO` vs `HELLO` | 5 |
| `ABC` vs empty | -6 |
| empty vs `XYZ` | -6 |
| `GATTACA` vs `GATTACA` | 7 |

All five are emitted as `#eval` outputs in `Basic.lean`; the last four are also proved as theorems.

## File layout

```
NeedlemanWunschLean/
├── NeedlemanWunschLean.lean         -- library entry point
├── NeedlemanWunschLean/Basic.lean   -- DP definition + 9 theorems
├── NeedlemanWunschLean/Alignment.lean -- traceback, optimality, examples (29 theorems)
├── lakefile.lean                    -- Lake build config, mathlib dep
├── lean-toolchain                   -- pinned to leanprover/lean4:v4.11.0
└── README.md
```

## Why this project

This is the theorem-prover complement of a mathematical-oncology portfolio (NMF mutation signatures, Cox PH survival, DP-mixture clonal evolution). It shows that alignment algorithms .The computational core of modern bioinformatics can be mechanically checked by a proof assistant, including the full optimality statement that the traceback achieves the DP optimum over every possible alignment.

## References

- S. B. Needleman and C. D. Wunsch. A general method applicable to the search for similarities in the amino acid sequence of two proteins. *J. Mol. Biol.* 48:443–453, 1970.
- The Lean 4 Theorem Prover. <https://lean-lang.org/>.
- mathlib community. <https://leanprover-community.github.io/>.
