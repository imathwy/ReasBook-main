import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape HomologicalComplex

universe u v

noncomputable section

namespace CategoryTheory.ShortComplex

variable {V : Type u} [Category.{v} V] [Abelian V]
variable {S : ShortComplex (CochainComplex V ℤ)}
variable (hS : S.ShortExact)
variable (spl : ∀ n : ℤ, (S.map (HomologicalComplex.eval V (up ℤ) n)).Splitting)

/-
Domain-style sampling in the cohomology-boundary owner API:
- primitive split datum: `CochainComplex.homOfDegreewiseSplit`
- degreewise companion formula: `CochainComplex.homOfDegreewiseSplit_f`
- owner short-exact boundary: `ShortComplex.ShortExact.δ`
- owner triangle boundary: `CochainComplex.homologyδOfTriangle`

Lemma 12.14.11 is a `bridge/view`: it identifies the triangle-level boundary map attached to the
degreewise split triangle with the short-exact-sequence boundary map `hS.δ`.
-/

-- Proof sketch: use the owner triangle boundary
-- `CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl)` for the
-- cohomology map induced by `CochainComplex.homOfDegreewiseSplit S spl`, then compare it with the
-- snake-lemma boundary `hS.δ` using `CochainComplex.homOfDegreewiseSplit_f` and the description of
-- `ShortComplex.ShortExact.δ`.
/-- Lemma 12.14.11: for a degreewise splitting of a short exact sequence
`0 ⟶ A^• ⟶ B^• ⟶ C^• ⟶ 0`, the cohomology boundary map of the degreewise split triangle, i.e. of
the canonical connecting morphism `CochainComplex.homOfDegreewiseSplit S spl : C^• ⟶ A^•[1]`, is
the connecting morphism in the associated long exact cohomology sequence. -/
theorem homologyMap_homOfDegreewiseSplit_eq_δ (i : ℤ) :
    CochainComplex.homologyδOfTriangle (CochainComplex.triangleOfDegreewiseSplit S spl) i (i + 1)
      rfl = hS.δ i (i + 1) rfl := by
  sorry

end CategoryTheory.ShortComplex
