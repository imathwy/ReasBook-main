module

public import Mathlib.Data.Real.Basic

@[expose] public section

/-- Compare real numbers first by their squares and then, when the squares agree,
by the usual order. -/
def squareLexLt (x y : ℝ) : Prop :=
  x ^ 2 < y ^ 2 ∨ x ^ 2 = y ^ 2 ∧ x < y

/-- The explicit comparison formula defining `squareLexLt`. -/
theorem squareLexLt_iff (x y : ℝ) :
    squareLexLt x y ↔ x ^ 2 < y ^ 2 ∨ x ^ 2 = y ^ 2 ∧ x < y :=
  Iff.rfl

/-- The square-lexicographic relation is a strict total order on `ℝ`. -/
instance instIsStrictTotalOrderSquareLexLt :
    IsStrictTotalOrder ℝ squareLexLt := {
  toTrichotomous := Std.trichotomous_of_rel_or_eq_or_rel_swap fun {x y} ↦
    match lt_trichotomy (x ^ 2) (y ^ 2) with
    | Or.inl h => .inl (Or.inl h)
    | Or.inr (Or.inl h) =>
        match lt_trichotomy x y with
        | Or.inl hxy => .inl (Or.inr ⟨h, hxy⟩)
        | Or.inr (Or.inl hxy) => .inr (.inl hxy)
        | Or.inr (Or.inr hxy) => .inr (.inr (Or.inr ⟨h.symm, hxy⟩))
    | Or.inr (Or.inr h) => .inr (.inr (Or.inl h))
  irrefl _ h :=
    match h with
    | Or.inl h => lt_irrefl _ h
    | Or.inr ⟨_, h⟩ => lt_irrefl _ h
  trans _ _ _ hxy hyz :=
    match hxy, hyz with
    | Or.inl hxy, Or.inl hyz => Or.inl (lt_trans hxy hyz)
    | Or.inl hxy, Or.inr ⟨hyz, _⟩ => Or.inl (hyz ▸ hxy)
    | Or.inr ⟨hxy, _⟩, Or.inl hyz => Or.inl (hxy ▸ hyz)
    | Or.inr ⟨hxy, hxy'⟩, Or.inr ⟨hyz, hyz'⟩ =>
        Or.inr ⟨hxy.trans hyz, lt_trans hxy' hyz'⟩ }
