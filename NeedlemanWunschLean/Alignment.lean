import NeedlemanWunschLean.Basic
import Mathlib.Tactic

namespace NW

variable {α : Type u}

inductive AlignStep (α : Type u) where
  | diag   : α → α → AlignStep α
  | delete : α → AlignStep α
  | insert : α → AlignStep α
  deriving Repr

abbrev Alignment (α : Type u) := List (AlignStep α)

def stepScore (s : α → α → Int) (g : Int) : AlignStep α → Int
  | .diag a b   => s a b
  | .delete _   => g
  | .insert _   => g

def alignScore (s : α → α → Int) (g : Int) : Alignment α → Int
  | [] => 0
  | step :: rest => stepScore s g step + alignScore s g rest

def toXs : Alignment α → List α
  | [] => []
  | .diag a _ :: rest   => a :: toXs rest
  | .delete a :: rest   => a :: toXs rest
  | .insert _ :: rest   => toXs rest

def toYs : Alignment α → List α
  | [] => []
  | .diag _ b :: rest   => b :: toYs rest
  | .delete _ :: rest   => toYs rest
  | .insert b :: rest   => b :: toYs rest

def align (s : α → α → Int) (g : Int) : List α → List α → Alignment α
  | [], [] => []
  | [], y :: ys => .insert y :: align s g [] ys
  | x :: xs, [] => .delete x :: align s g xs []
  | x :: xs, y :: ys =>
    if nw s g xs ys + s x y ≥ nw s g xs (y :: ys) + g ∧
       nw s g xs ys + s x y ≥ nw s g (x :: xs) ys + g then
      .diag x y :: align s g xs ys
    else if nw s g xs (y :: ys) + g ≥ nw s g (x :: xs) ys + g then
      .delete x :: align s g xs (y :: ys)
    else
      .insert y :: align s g (x :: xs) ys
termination_by xs ys => xs.length + ys.length

theorem toXs_align (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, toXs (align s g xs ys) = xs := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil => simp [align, toXs]
      | cons y ys ih => simp [align, toXs, ih]
  | cons x xs ihxs =>
      induction ys with
      | nil =>
          simp [align, toXs]
          exact ihxs []
      | cons y ys ihys =>
          simp only [align]
          split_ifs
          · simp [toXs]; exact ihxs ys
          · simp [toXs]; exact ihxs (y :: ys)
          · simp [toXs]; exact ihys

theorem toYs_align (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, toYs (align s g xs ys) = ys := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      induction ys with
      | nil => simp [align, toYs]
      | cons y ys ih => simp [align, toYs, ih]
  | cons x xs ihxs =>
      induction ys with
      | nil =>
          simp [align, toYs]
          exact ihxs []
      | cons y ys ihys =>
          simp only [align]
          split_ifs
          · simp [toYs]; exact ihxs ys
          · simp [toYs]; exact ihxs (y :: ys)
          · simp [toYs]; exact ihys

theorem toXs_length (s : α → α → Int) (g : Int) (xs ys : List α) :
    (toXs (align s g xs ys)).length = xs.length := by
  rw [toXs_align]

theorem toYs_length (s : α → α → Int) (g : Int) (xs ys : List α) :
    (toYs (align s g xs ys)).length = ys.length := by
  rw [toYs_align]

theorem alignScore_cons (s : α → α → Int) (g : Int)
    (step : AlignStep α) (rest : Alignment α) :
    alignScore s g (step :: rest) = stepScore s g step + alignScore s g rest := by
  simp [alignScore]

theorem alignScore_nil_left (s : α → α → Int) (g : Int) (ys : List α) :
    alignScore s g (align s g [] ys) = g * (ys.length : Int) := by
  induction ys with
  | nil => simp [align, alignScore]
  | cons y ys ih =>
      simp only [align, alignScore, stepScore, List.length_cons]
      rw [ih]
      push_cast
      ring

theorem alignScore_nil_right (s : α → α → Int) (g : Int) (xs : List α) :
    alignScore s g (align s g xs []) = g * (xs.length : Int) := by
  induction xs with
  | nil => simp [align, alignScore]
  | cons x xs ih =>
      simp only [align, alignScore, stepScore, List.length_cons]
      rw [ih]
      push_cast
      ring

theorem alignScore_eq_nw (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α, alignScore s g (align s g xs ys) = nw s g xs ys := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      rw [alignScore_nil_left, nw_nil_left]
  | cons x xs ihxs =>
      induction ys with
      | nil =>
          rw [alignScore_nil_right, nw_nil_right]
      | cons y ys ihys =>
          simp only [align]
          split_ifs with hd hu
          · simp only [alignScore_cons, stepScore]
            rw [ihxs ys, nw_bellman]
            obtain ⟨hdu, hdl⟩ := hd
            omega
          · simp only [alignScore_cons, stepScore]
            rw [ihxs (y :: ys), nw_bellman]
            rw [not_and_or] at hd
            rcases hd with hdu_lt | hdl_lt
            · push_neg at hdu_lt; omega
            · push_neg at hdl_lt; omega
          · simp only [alignScore_cons, stepScore]
            rw [ihys, nw_bellman]
            push_neg at hu
            rw [not_and_or] at hd
            rcases hd with hdu_lt | hdl_lt
            · push_neg at hdu_lt; omega
            · push_neg at hdl_lt; omega

theorem nw_ge_align_score (s : α → α → Int) (g : Int) (xs ys : List α) :
    nw s g xs ys ≥ alignScore s g (align s g xs ys) := by
  rw [alignScore_eq_nw]

theorem nw_lower_bound_delete (s : α → α → Int) (g : Int) (x : α) (xs ys : List α) :
    nw s g xs ys + g ≤ nw s g (x :: xs) ys := by
  cases ys with
  | nil =>
      simp only [nw_nil_right]
      push_cast [List.length_cons]
      ring_nf
      linarith
  | cons y ys' =>
      exact nw_lower_bound_up s g x xs y ys'

theorem nw_lower_bound_insert (s : α → α → Int) (g : Int) (y : α) (xs ys : List α) :
    nw s g xs ys + g ≤ nw s g xs (y :: ys) := by
  cases xs with
  | nil =>
      simp only [nw_nil_left]
      push_cast [List.length_cons]
      ring_nf
      linarith
  | cons x xs' =>
      exact nw_lower_bound_left s g x xs' y ys

theorem alignScore_le_nw_project (s : α → α → Int) (g : Int) (a : Alignment α) :
    alignScore s g a ≤ nw s g (toXs a) (toYs a) := by
  induction a with
  | nil => simp [alignScore, toXs, toYs]
  | cons step rest ih =>
      cases step with
      | diag x y =>
          simp only [toXs, toYs, alignScore, stepScore]
          linarith [nw_lower_bound_diag s g x (toXs rest) y (toYs rest)]
      | delete x =>
          simp only [toXs, toYs, alignScore, stepScore]
          linarith [nw_lower_bound_delete s g x (toXs rest) (toYs rest)]
      | insert y =>
          simp only [toXs, toYs, alignScore, stepScore]
          linarith [nw_lower_bound_insert s g y (toXs rest) (toYs rest)]

theorem alignScore_le_nw_of_aligned (s : α → α → Int) (g : Int)
    (a : Alignment α) (xs ys : List α)
    (hx : toXs a = xs) (hy : toYs a = ys) :
    alignScore s g a ≤ nw s g xs ys := by
  have := alignScore_le_nw_project s g a
  rw [hx, hy] at this
  exact this

theorem align_is_optimal (s : α → α → Int) (g : Int) (a : Alignment α)
    (xs ys : List α) (hx : toXs a = xs) (hy : toYs a = ys) :
    alignScore s g a ≤ alignScore s g (align s g xs ys) := by
  rw [alignScore_eq_nw]
  exact alignScore_le_nw_of_aligned s g a xs ys hx hy

theorem nw_symm_of_symmetric_score
    (s : α → α → Int) (g : Int)
    (hsymm : ∀ a b, s a b = s b a) :
    ∀ xs ys : List α, nw s g xs ys = nw s g ys xs := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => simp
      | cons y ys => simp
  | cons x xs ihxs =>
      induction ys with
      | nil =>
          simp
      | cons y ys ihys =>
          rw [nw_bellman, nw_bellman]
          rw [ihxs ys, ihxs (y :: ys), ihys, hsymm x y]
          omega

theorem exampleScore_symm : ∀ a b : Char, exampleScore a b = exampleScore b a := by
  intro a b
  simp only [exampleScore]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rfl

theorem nw_example_symm (xs ys : List Char) :
    nw exampleScore exampleGap xs ys = nw exampleScore exampleGap ys xs :=
  nw_symm_of_symmetric_score exampleScore exampleGap exampleScore_symm xs ys

theorem alignScore_append (s : α → α → Int) (g : Int) (a b : Alignment α) :
    alignScore s g (a ++ b) = alignScore s g a + alignScore s g b := by
  induction a with
  | nil => simp [alignScore]
  | cons step rest ih =>
      simp [alignScore, ih]
      ring

theorem toXs_append (a b : Alignment α) :
    toXs (a ++ b) = toXs a ++ toXs b := by
  induction a with
  | nil => simp [toXs]
  | cons step rest ih =>
      cases step <;> simp [toXs, ih]

theorem toYs_append (a b : Alignment α) :
    toYs (a ++ b) = toYs a ++ toYs b := by
  induction a with
  | nil => simp [toYs]
  | cons step rest ih =>
      cases step <;> simp [toYs, ih]

def diagSelf : List α → Alignment α
  | [] => []
  | x :: xs => .diag x x :: diagSelf xs

theorem toXs_diagSelf (xs : List α) : toXs (diagSelf xs) = xs := by
  induction xs with
  | nil => simp [diagSelf, toXs]
  | cons x xs ih => simp [diagSelf, toXs, ih]

theorem toYs_diagSelf (xs : List α) : toYs (diagSelf xs) = xs := by
  induction xs with
  | nil => simp [diagSelf, toYs]
  | cons x xs ih => simp [diagSelf, toYs, ih]

theorem alignScore_diagSelf (s : α → α → Int) (g : Int) (xs : List α) :
    alignScore s g (diagSelf xs) = (xs.map (fun x => s x x)).sum := by
  induction xs with
  | nil => simp [diagSelf, alignScore]
  | cons x xs ih =>
      simp [diagSelf, alignScore, stepScore, ih]

theorem nw_ge_diag_self_score (s : α → α → Int) (g : Int) (xs : List α) :
    (xs.map (fun x => s x x)).sum ≤ nw s g xs xs := by
  have h1 := alignScore_le_nw_of_aligned s g (diagSelf xs) xs xs
    (toXs_diagSelf xs) (toYs_diagSelf xs)
  rw [alignScore_diagSelf] at h1
  exact h1

theorem example_hello_self : nw exampleScore exampleGap "HELLO".toList "HELLO".toList = 5 := by
  native_decide

theorem example_gattaca_self : nw exampleScore exampleGap "GATTACA".toList "GATTACA".toList = 7 := by
  native_decide

theorem example_abc_empty : nw exampleScore exampleGap "ABC".toList [] = -6 := by
  simp [nw, exampleGap]

theorem example_empty_xyz : nw exampleScore exampleGap [] "XYZ".toList = -6 := by
  simp [nw, exampleGap]

theorem align_hello_self_correct :
    alignScore exampleScore exampleGap
      (align exampleScore exampleGap "HELLO".toList "HELLO".toList) = 5 := by
  rw [alignScore_eq_nw, example_hello_self]

end NW
