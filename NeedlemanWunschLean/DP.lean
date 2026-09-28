import NeedlemanWunschLean.Alignment

namespace NW

variable {α : Type u}

def nwRowNil (g : Int) : List α → List Int
  | [] => [0]
  | _ :: ys =>
    let rest := nwRowNil g ys
    (rest.headD 0 + g) :: rest

def nwRowCons (s : α → α → Int) (g : Int) (x : α) : List α → List Int → List Int
  | [], prev => [prev.headD 0 + g]
  | y :: ys, prev =>
    let rest := nwRowCons s g x ys prev.tail
    let diag := prev.tail.headD 0 + s x y
    let up   := prev.headD 0 + g
    let left := rest.headD 0 + g
    max (max diag up) left :: rest

def nwRow (s : α → α → Int) (g : Int) (ys : List α) : List α → List Int
  | [] => nwRowNil g ys
  | x :: xs => nwRowCons s g x ys (nwRow s g ys xs)

def nwFast (s : α → α → Int) (g : Int) (xs ys : List α) : Int :=
  (nwRow s g ys xs).headD 0

def nwTable (s : α → α → Int) (g : Int) (ys : List α) : List α → List (List Int)
  | [] => [nwRowNil g ys]
  | x :: xs =>
    let rows := nwTable s g ys xs
    nwRowCons s g x ys (rows.headD []) :: rows

def alignWith (s : α → α → Int) (g : Int) :
    List α → List α → List (List Int) → Alignment α
  | [], ys, _ => align s g [] ys
  | x :: xs, [], _ => align s g (x :: xs) []
  | x :: xs, y :: ys, rows =>
    let here  := rows.headD []
    let below := rows.tail.headD []
    let diag := below.tail.headD 0 + s x y
    let up   := below.headD 0 + g
    let left := here.tail.headD 0 + g
    if diag ≥ up ∧ diag ≥ left then
      .diag x y :: alignWith s g xs ys (rows.tail.map List.tail)
    else if up ≥ left then
      .delete x :: alignWith s g xs (y :: ys) rows.tail
    else
      .insert y :: alignWith s g (x :: xs) ys (rows.map List.tail)
termination_by xs ys _ => xs.length + ys.length

def alignFast (s : α → α → Int) (g : Int) (xs ys : List α) : Alignment α :=
  alignWith s g xs ys (nwTable s g ys xs)

theorem headD_map_tails {β : Type v} (f : List α → β) (ys : List α) (d : β) :
    (ys.tails.map f).headD d = f ys := by
  cases ys <;> simp

theorem nwRowNil_eq (s : α → α → Int) (g : Int) (ys : List α) :
    nwRowNil g ys = ys.tails.map (nw s g []) := by
  induction ys with
  | nil => simp [nwRowNil]
  | cons y ys ih =>
      simp only [nwRowNil, ih, headD_map_tails, List.tails, List.map_cons, nw_nil_left,
        List.length_cons]
      congr 1
      push_cast
      ring

theorem nwRowCons_eq (s : α → α → Int) (g : Int) (x : α) (xs : List α) :
    ∀ ys : List α,
      nwRowCons s g x ys (ys.tails.map (nw s g xs)) = ys.tails.map (nw s g (x :: xs)) := by
  intro ys
  induction ys with
  | nil =>
      simp only [nwRowCons, List.tails, List.map_cons, List.map_nil, List.headD_cons,
        nw_nil_right, List.length_cons]
      congr 1
      push_cast
      ring
  | cons y ys ih =>
      simp only [nwRowCons, List.tails, List.map_cons, List.tail_cons, List.headD_cons, ih,
        headD_map_tails]
      rw [nw_bellman]

theorem nwRow_eq (s : α → α → Int) (g : Int) (ys : List α) :
    ∀ xs : List α, nwRow s g ys xs = ys.tails.map (nw s g xs) := by
  intro xs
  induction xs with
  | nil => exact nwRowNil_eq s g ys
  | cons x xs ih => rw [nwRow, ih, nwRowCons_eq]

theorem nwFast_eq_nw (s : α → α → Int) (g : Int) (xs ys : List α) :
    nwFast s g xs ys = nw s g xs ys := by
  rw [nwFast, nwRow_eq, headD_map_tails]

theorem nwTable_eq (s : α → α → Int) (g : Int) (ys : List α) :
    ∀ xs : List α, nwTable s g ys xs = xs.tails.map (fun t => ys.tails.map (nw s g t)) := by
  intro xs
  induction xs with
  | nil => simp [nwTable, nwRowNil_eq s]
  | cons x xs ih =>
      simp only [nwTable, ih, headD_map_tails, nwRowCons_eq, List.tails, List.map_cons]

theorem alignWith_eq (s : α → α → Int) (g : Int) :
    ∀ xs ys : List α,
      alignWith s g xs ys (xs.tails.map (fun t => ys.tails.map (nw s g t))) =
        align s g xs ys := by
  intro xs ys
  induction xs generalizing ys with
  | nil => simp [alignWith]
  | cons x xs ihxs =>
      induction ys with
      | nil => simp [alignWith]
      | cons y ys ihys =>
          have hd := ihxs ys
          have hu := ihxs (y :: ys)
          simp only [List.tails, List.map_cons, List.map_map, Function.comp_def,
            List.tail_cons] at hd hu ihys ⊢
          rw [alignWith, align]
          simp only [List.tails, List.map_cons, List.map_map, Function.comp_def,
            List.tail_cons, List.headD_cons, headD_map_tails]
          split_ifs
          · rw [hd]
          · rw [hu]
          · rw [ihys]

theorem alignFast_eq_align (s : α → α → Int) (g : Int) (xs ys : List α) :
    alignFast s g xs ys = align s g xs ys := by
  rw [alignFast, nwTable_eq, alignWith_eq]

theorem alignFast_correct (s : α → α → Int) (g : Int) (xs ys : List α) :
    toXs (alignFast s g xs ys) = xs ∧
    toYs (alignFast s g xs ys) = ys ∧
    alignScore s g (alignFast s g xs ys) = nwFast s g xs ys ∧
    ∀ a : Alignment α, toXs a = xs → toYs a = ys →
      alignScore s g a ≤ alignScore s g (alignFast s g xs ys) := by
  rw [alignFast_eq_align, nwFast_eq_nw]
  exact ⟨toXs_align s g xs ys, toYs_align s g xs ys, alignScore_eq_nw s g xs ys,
    fun a hx hy => align_is_optimal s g a xs ys hx hy⟩

end NW
