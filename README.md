# Needleman-Wunsch in Lean 4

[![build](https://github.com/CuteSurtr/NeedlemanWunschLean/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/CuteSurtr/NeedlemanWunschLean/actions/workflows/lean_action_ci.yml)

A Lean 4 + Mathlib formalization of Needleman-Wunsch global alignment with a
linear gap penalty. Sequences are lists over any type `α`, putting `x` against
`y` scores `s x y` for an arbitrary `s : α → α → Int`, and every gap costs `g`.
I prove that the traceback returns an alignment of the two input sequences,
that its score is the value of the recurrence, and that no other alignment of
the same two sequences scores higher. There is also an O(mn) table version,
proved equal to the recurrence, which is the one to run on real inputs.

There is no `sorry`, `admit` or `native_decide` in the source and no `axiom`
declarations, and the build checks that the main theorems rely only on Lean's
three standard axioms (see [Building](#building)).

## The recurrence

`nw` in `Basic.lean` is the recurrence written as a recursive function.
`nw s g xs ys` is the best score for aligning `xs` against `ys`, and it works
from the front of the lists, so each step looks at their first letters:

```lean
def nw (s : α → α → Int) (g : Int) : List α → List α → Int
  | [], ys => g * ys.length
  | x :: xs, [] => g * (x :: xs).length
  | x :: xs, y :: ys =>
    let diag := nw s g xs ys + s x y
    let up   := nw s g xs (y :: ys) + g
    let left := nw s g (x :: xs) ys + g
    max (max diag up) left
termination_by xs ys => xs.length + ys.length
```

The usual table is indexed by prefixes instead, with `F(i, j)` computed from
`F(i-1, j-1)`, `F(i-1, j)` and `F(i, j-1)`. Working with suffixes is the same
recurrence read from the other end. Either way the value is the best score
over all alignments, which is exactly what the theorems below prove about
`nw`.

This is the linear-gap recurrence that textbooks call Needleman-Wunsch. The
1970 paper itself allowed an arbitrary gap cost, and its version of the
recursion took cubic time; the quadratic form came later.

As a program, `nw` is only a specification. It has no memoization, so its call
tree has a leaf for every alignment of the two inputs. The number of
alignments is a Delannoy number: 48,639 for two 7-letter strings, and it grows
by a factor of about 5.8 each time both strings get one letter longer. Under
`lean --run`, two 12-letter strings already take about three minutes.
`nwFast` below is the one to use.

## Alignments and the traceback

`Alignment.lean` defines an alignment as a list of columns:

```lean
inductive AlignStep (α : Type u) where
  | diag   : α → α → AlignStep α
  | delete : α → AlignStep α
  | insert : α → AlignStep α
  deriving Repr

abbrev Alignment (α : Type u) := List (AlignStep α)
```

`diag x y` puts `x` above `y` and scores `s x y`, whether they match or not.
`delete x` puts `x` above a gap and `insert y` puts a gap above `y`, and both
cost `g`. `alignScore` adds up the columns, and `toXs`/`toYs` read the two
sequences back off an alignment. Every list of steps is an alignment of
`toXs a` against `toYs a`, so there is no separate well-formedness condition.

`align` is the traceback. At each step it compares the three candidates from
the recurrence and follows the best one, preferring diagonal, then delete,
then insert when there is a tie. The main theorems about it:

```lean
theorem toXs_align (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, toXs (align s g xs ys) = xs

theorem toYs_align (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, toYs (align s g xs ys) = ys

theorem alignScore_eq_nw (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, alignScore s g (align s g xs ys) = nw s g xs ys

theorem align_is_optimal (s : α → α → Int) (g : Int) (a : Alignment α)
    (xs ys : List α) (hx : toXs a = xs) (hy : toYs a = ys) :
    alignScore s g a ≤ alignScore s g (align s g xs ys)
```

The first two say that `align xs ys` really is an alignment of `xs` with
`ys`. `alignScore_eq_nw` says its score is `nw s g xs ys`, and
`align_is_optimal` says no alignment of the same sequences does better. The
optimality proof goes through `alignScore_le_nw_project`, which shows by
induction on `a` that `alignScore s g a ≤ nw s g (toXs a) (toYs a)` for every
alignment `a`. Each induction step uses one of three lower bounds
(`nw_lower_bound_diag`, `nw_lower_bound_delete`, `nw_lower_bound_insert`),
the first being `nw s g xs ys + s x y ≤ nw s g (x :: xs) (y :: ys)`.

## The table version

`DP.lean` is the dynamic program itself. Row `xs` of the table holds
`nw s g xs t` for every suffix `t` of `ys`, that is `ys.tails.map (nw s g xs)`,
and `nwRowCons` computes the row for `x :: xs` from the row for `xs` in one
pass. `nwFast` keeps only the latest row and takes O(mn) time. `nwTable`
keeps every row, and `alignFast` runs the same traceback as `align` but reads
the three candidates out of the table instead of recomputing them.

```lean
theorem nwFast_eq_nw (s : α → α → Int) (g : Int) (xs ys : List α) :
    nwFast s g xs ys = nw s g xs ys

theorem alignFast_eq_align (s : α → α → Int) (g : Int) (xs ys : List α) :
    alignFast s g xs ys = align s g xs ys
```

Because `alignFast` is equal to `align` (same tie-breaking, same output),
everything proved about `align` carries over. `alignFast_correct` collects it
in one statement:

```lean
theorem alignFast_correct (s : α → α → Int) (g : Int) (xs ys : List α) :
    toXs (alignFast s g xs ys) = xs ∧
    toYs (alignFast s g xs ys) = ys ∧
    alignScore s g (alignFast s g xs ys) = nwFast s g xs ys ∧
    ∀ a : Alignment α, toXs a = xs → toYs a = ys →
      alignScore s g a ≤ alignScore s g (alignFast s g xs ys)
```

Timings under `lean --run`, with the example scoring below:

| Lengths | `nw` | `nwFast` |
| --- | --- | --- |
| 8 and 8 | 0.18 s | about 1 ms |
| 10 and 10 | 5.9 s | under 1 ms |
| 12 and 12 | 181 s | under 1 ms |
| 2000 and 2000 | not feasible | 4.4 s |

`alignFast` on the 2000-letter pair takes 5.3 s, building the table included.

## Examples

`Basic.lean` defines an example scoring, +1 for a match, -1 for a mismatch and
-2 per gap (`exampleScore`, `exampleGap`), and `#eval`s `nw` on a few inputs.
`Examples.lean` proves the scores:

| Inputs | Score | Theorem |
| --- | --- | --- |
| `GATTACA`, `GCATGCU` | -1 | `example_gattaca_gcatgcu` |
| `GATTACA`, `GCATGCU`, gap cost -1 | 0 | `example_gattaca_gcatgcu_unit_gap` |
| `HELLO`, `HELLO` | 5 | `example_hello_self` |
| `GATTACA`, `GATTACA` | 7 | `example_gattaca_self` |
| `ABC`, empty | -6 | `example_abc_empty` |
| empty, `XYZ` | -6 | `example_empty_xyz` |

The second row is the standard GATTACA/GCATGCU example (match +1, mismatch
-1, gap -1), whose optimal score is 0. `alignFast` returns

```
G-ATTACA
GCATG-CU
```

for it, which is one of the optimal alignments.

The GATTACA and HELLO examples rewrite with `nwFast_eq_nw` and then call
`decide`, so the Lean kernel does the computation. That doesn't work on `nw`
directly: it is defined by well-founded recursion, and Lean makes such
definitions irreducible. The functions in `DP.lean` are structurally
recursive, so the kernel can run them. `native_decide` would also work, but
it trusts the compiler through the `Lean.ofReduceBool` axiom, which the axiom
check below would reject.

## Other results

- `nw_nil_left`, `nw_nil_right`: against an empty sequence the score is `g`
  times the length of the other one.
- `nw_bellman`: the recurrence as an equation.
- `nw_achieves_one_of_three`: the optimum equals at least one of the three
  candidates.
- `nw_mono_in_score`: if `s₁ a b ≤ s₂ a b` for all `a b`, then
  `nw s₁ g xs ys ≤ nw s₂ g xs ys`.
- `nw_symm_of_symmetric_score`: if `s a b = s b a` for all `a b`, then
  `nw s g xs ys = nw s g ys xs`.
- `nw_ge_diag_self_score`: `nw s g xs xs` is at least the sum of `s x x` over
  `xs`, because matching a sequence with itself column by column is one of
  the alignments.
- `alignScore_append`, `toXs_append`, `toYs_append`: scores and projections
  split over concatenation of alignments.

## Where things are

| File | Contents |
| --- | --- |
| `NeedlemanWunschLean/Basic.lean` | `nw`, `nw_bellman` and the lower bounds, monotonicity, the example scoring |
| `NeedlemanWunschLean/Alignment.lean` | `AlignStep`, `alignScore`, `toXs`, `toYs`, `align`, correctness, optimality, symmetry |
| `NeedlemanWunschLean/DP.lean` | `nwFast`, `nwTable`, `alignFast`, and the proofs that they agree with `nw` and `align` |
| `NeedlemanWunschLean/Examples.lean` | the concrete scores above |
| `NeedlemanWunschLean/AxiomAudit.lean` | the axiom check |

## Building

Lean is pinned to v4.11.0 in `lean-toolchain`, and Mathlib to its `v4.11.0`
tag in `lakefile.lean`. With [elan](https://github.com/leanprover/elan)
installed (it reads `lean-toolchain` and fetches the right Lean by itself):

```sh
lake exe cache get   # prebuilt Mathlib
lake build
```

The main theorems and the examples depend only on `propext`,
`Classical.choice` and `Quot.sound`. `AxiomAudit.lean` runs `#print axioms` on
13 of them inside `#guard_msgs`, so if one of them ever picks up a `sorry`,
`native_decide` or any other axiom, `lake build` fails. CI runs the same
build on every push.

## Notes on the formalization

- I recurse on the fronts of the lists instead of indexing into arrays. Every
  proof is then a plain induction on lists, and the table can be described
  with `List.tails`, which is what `nwRow_eq` and `nwTable_eq` do.
- `alignWith` checks the same conditions as `align`, in the same order, so the
  two make the same choice on ties. That is why `alignFast = align` holds as
  an equality of alignments and not just of scores.
- `alignFast` drops the used row or column of the table as it walks, and each
  drop maps over the remaining rows. So the walk costs O(m) per step on top of
  the O(mn) table. Fine at these sizes, but it is the obvious thing to improve.
- Only linear gap penalties. Affine gaps (Gotoh) would need three tables and a
  different traceback.
- The score function can be anything of type `α → α → Int`. Nothing assumes it
  is symmetric or that matches beat mismatches, except
  `nw_symm_of_symmetric_score`, which asks for symmetry explicitly.

## Background

I wrote this as the proof-assistant side of a set of mathematical oncology
projects (NMF mutation signatures, Cox proportional hazards survival,
Dirichlet-process mixtures for clonal evolution). Sequence alignment sits
underneath a lot of bioinformatics, and I wanted to see an alignment
algorithm checked end to end by a proof assistant, including the full
statement that no alignment scores higher than the traceback.

## References

- S. B. Needleman and C. D. Wunsch. A general method applicable to the search
  for similarities in the amino acid sequence of two proteins. *J. Mol. Biol.*
  48(3):443-453, 1970. [doi:10.1016/0022-2836(70)90057-4](https://doi.org/10.1016/0022-2836(70)90057-4)
- Lean 4: <https://lean-lang.org/>
- Mathlib: <https://leanprover-community.github.io/>

## License

MIT, see [LICENSE](LICENSE).
