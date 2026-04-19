import NeedlemanWunschLean.Basic

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
          split
          · simp [toXs]; exact ihxs ys
          · split
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
          split
          · simp [toYs]; exact ihxs ys
          · split
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

theorem gap_times_succ (g : Int) (n : Nat) :
    g * ((n + 1 : Nat) : Int) = g * (n : Int) + g := by
  have h : ((n + 1 : Nat) : Int) = (n : Int) + 1 := by
    show Int.ofNat (n + 1) = Int.ofNat n + 1
    rfl
  rw [h, Int.mul_add, Int.mul_one]

theorem alignScore_nil_left (s : α → α → Int) (g : Int) (ys : List α) :
    alignScore s g (align s g [] ys) = g * (ys.length : Int) := by
  induction ys with
  | nil => simp [align, alignScore]
  | cons y ys ih =>
      simp only [align, alignScore, stepScore, List.length_cons]
      rw [ih, gap_times_succ]
      omega

theorem alignScore_nil_right (s : α → α → Int) (g : Int) (xs : List α) :
    alignScore s g (align s g xs []) = g * (xs.length : Int) := by
  induction xs with
  | nil => simp [align, alignScore]
  | cons x xs ih =>
      simp only [align, alignScore, stepScore, List.length_cons]
      rw [ih, gap_times_succ]
      omega

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

end NW
