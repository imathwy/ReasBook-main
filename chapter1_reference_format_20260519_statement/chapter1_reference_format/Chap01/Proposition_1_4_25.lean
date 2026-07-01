import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set Submodule

universe u v

section

variable {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]

/- Proposition 1.4.25 is `bridge/view`: the source uses `Fin n`-indexed families and an explicit
dimension equality `finrank K V = n`, while the canonical owner is `Module.Basis`. The primitive
data are linear independence or spanning, and the corresponding basis is derived canonically. -/

/-- Proposition 1.4.25 (1): in an `n`-dimensional `K`-vector space, any linearly independent
family of `n` vectors forms a basis. -/
noncomputable def basis_of_linearIndependent_of_finrank_eq
    [FiniteDimensional K V] {n : ℕ} {v : Fin n → V} (hV : Module.finrank K V = n)
    (hv : LinearIndependent K v) : Module.Basis (Fin n) K V :=
  Module.Basis.mk hv <|
    (hv.span_eq_top_of_card_eq_finrank' <| (Fintype.card_fin n).trans hV.symm).ge

/-- Derived consequence of Proposition 1.4.25 (1): such a family spans the whole space. -/
theorem span_eq_top_of_linearIndependent_of_finrank_eq
    [FiniteDimensional K V] {n : ℕ} {v : Fin n → V} (hV : Module.finrank K V = n)
    (hv : LinearIndependent K v) : span K (range v) = ⊤ := by
  simpa [basis_of_linearIndependent_of_finrank_eq] using
    (basis_of_linearIndependent_of_finrank_eq hV hv).span_eq

/-- Proposition 1.4.25 (2): any spanning family of `n` vectors in a vector space of dimension `n`
forms a basis. -/
noncomputable def basis_of_span_eq_top_of_finrank_eq
    {n : ℕ} {v : Fin n → V} (hV : Module.finrank K V = n) (hv : span K (range v) = ⊤) :
    Module.Basis (Fin n) K V :=
  basisOfTopLeSpanOfCardEqFinrank v hv.ge <| (Fintype.card_fin n).trans hV.symm

/-- Derived consequence of Proposition 1.4.25 (2): such a family is linearly independent. -/
theorem linearIndependent_of_span_eq_top_of_finrank_eq
    {n : ℕ} {v : Fin n → V} (hV : Module.finrank K V = n) (hv : span K (range v) = ⊤) :
    LinearIndependent K v := by
  simpa [basis_of_span_eq_top_of_finrank_eq] using
    (basis_of_span_eq_top_of_finrank_eq hV hv).linearIndependent

end
