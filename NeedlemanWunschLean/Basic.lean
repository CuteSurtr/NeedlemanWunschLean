namespace NW

variable {α : Type u}

def nw (s : α → α → Int) (g : Int) : List α → List α → Int
  | [], ys => g * ys.length
  | x :: xs, [] => g * (x :: xs).length
  | x :: xs, y :: ys =>
    let diag := nw s g xs ys + s x y
    let up   := nw s g xs (y :: ys) + g
    let left := nw s g (x :: xs) ys + g
    max (max diag up) left
termination_by xs ys => xs.length + ys.length

@[simp] theorem nw_nil_left (s : α → α → Int) (g : Int) (ys : List α) :
    nw s g [] ys = g * ys.length := by
  simp [nw]

@[simp] theorem nw_nil_right (s : α → α → Int) (g : Int) (xs : List α) :
    nw s g xs [] = g * xs.length := by
  cases xs with
  | nil      => simp [nw]
  | cons _ _ => simp [nw]

theorem nw_bellman (s : α → α → Int) (g : Int)
    (x : α) (xs : List α) (y : α) (ys : List α) :
    nw s g (x :: xs) (y :: ys) =
      max (max (nw s g xs ys + s x y)
               (nw s g xs (y :: ys) + g))
          (nw s g (x :: xs) ys + g) := by
  simp [nw]

theorem max_mono {a b c d : Int} (h1 : a ≤ c) (h2 : b ≤ d) :
    max a b ≤ max c d := by omega

theorem nw_lower_bound_diag (s : α → α → Int) (g : Int)
    (x : α) (xs : List α) (y : α) (ys : List α) :
    nw s g xs ys + s x y ≤ nw s g (x :: xs) (y :: ys) := by
  rw [nw_bellman]; omega

theorem nw_lower_bound_up (s : α → α → Int) (g : Int)
    (x : α) (xs : List α) (y : α) (ys : List α) :
    nw s g xs (y :: ys) + g ≤ nw s g (x :: xs) (y :: ys) := by
  rw [nw_bellman]; omega

theorem nw_lower_bound_left (s : α → α → Int) (g : Int)
    (x : α) (xs : List α) (y : α) (ys : List α) :
    nw s g (x :: xs) ys + g ≤ nw s g (x :: xs) (y :: ys) := by
  rw [nw_bellman]; omega

theorem nw_achieves_one_of_three (s : α → α → Int) (g : Int)
    (x : α) (xs : List α) (y : α) (ys : List α) :
    nw s g (x :: xs) (y :: ys) = nw s g xs ys + s x y ∨
    nw s g (x :: xs) (y :: ys) = nw s g xs (y :: ys) + g ∨
    nw s g (x :: xs) (y :: ys) = nw s g (x :: xs) ys + g := by
  rw [nw_bellman]
  have h : max (max (nw s g xs ys + s x y)
                    (nw s g xs (y :: ys) + g))
               (nw s g (x :: xs) ys + g)
           = (nw s g xs ys + s x y) ∨
           max (max (nw s g xs ys + s x y)
                    (nw s g xs (y :: ys) + g))
               (nw s g (x :: xs) ys + g)
           = (nw s g xs (y :: ys) + g) ∨
           max (max (nw s g xs ys + s x y)
                    (nw s g xs (y :: ys) + g))
               (nw s g (x :: xs) ys + g)
           = (nw s g (x :: xs) ys + g) := by omega
  exact h

theorem nw_mono_in_score
    (s₁ s₂ : α → α → Int) (g : Int)
    (hle : ∀ a b, s₁ a b ≤ s₂ a b) :
    ∀ xs ys : List α, nw s₁ g xs ys ≤ nw s₂ g xs ys := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ihxs =>
      induction ys with
      | nil =>
          simp
      | cons y ys ihys =>
          have ih_d : nw s₁ g xs ys ≤ nw s₂ g xs ys := ihxs ys
          have ih_u : nw s₁ g xs (y :: ys) ≤ nw s₂ g xs (y :: ys) := ihxs (y :: ys)
          have sxy  : s₁ x y ≤ s₂ x y := hle x y
          simp only [nw_bellman]
          have hd : nw s₁ g xs ys + s₁ x y ≤ nw s₂ g xs ys + s₂ x y :=
            Int.add_le_add ih_d sxy
          have hu : nw s₁ g xs (y :: ys) + g ≤ nw s₂ g xs (y :: ys) + g :=
            Int.add_le_add_right ih_u g
          have hl : nw s₁ g (x :: xs) ys + g ≤ nw s₂ g (x :: xs) ys + g :=
            Int.add_le_add_right ihys g
          have h1 : max (nw s₁ g xs ys + s₁ x y) (nw s₁ g xs (y :: ys) + g)
                  ≤ max (nw s₂ g xs ys + s₂ x y) (nw s₂ g xs (y :: ys) + g) :=
            max_mono hd hu
          exact max_mono h1 hl

def exampleScore (a b : Char) : Int := if a = b then 1 else -1
def exampleGap : Int := -2

#eval nw exampleScore exampleGap "GATTACA".toList "GCATGCU".toList
#eval nw exampleScore exampleGap "HELLO".toList "HELLO".toList
#eval nw exampleScore exampleGap "ABC".toList "".toList
#eval nw exampleScore exampleGap "".toList "XYZ".toList
#eval nw exampleScore exampleGap "GATTACA".toList "GATTACA".toList

theorem exampleScore_bound :
    ∀ a b : Char, exampleScore a b ≤ (fun _ _ => (2 : Int)) a b := by
  intro a b
  simp [exampleScore]
  split <;> omega

theorem nw_bounded_by_uniform_two (xs ys : List Char) :
    nw exampleScore exampleGap xs ys
      ≤ nw (fun _ _ => (2 : Int)) exampleGap xs ys :=
  nw_mono_in_score exampleScore (fun _ _ => (2 : Int)) exampleGap
    exampleScore_bound xs ys

end NW
