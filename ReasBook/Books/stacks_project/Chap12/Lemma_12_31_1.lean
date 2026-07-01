import Mathlib

universe u v

open CategoryTheory
open CategoryTheory.Limits
open OrderDual (ofDual toDual)
open Opposite

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category C]

/- Domain-style sampling for Lemma 12.31.1 in the inverse-system exactness domain:
- primary domain: exactness of short complexes in the functor category `Iᵒᵈ ⥤ C`
- sampled owner declarations:
  `NatTrans.isIso_iff_isIso_app`,
  `JointlyReflectIsomorphisms.exact_iff`,
  `inferInstance : Abelian (Iᵒᵈ ⥤ C)`.
- owner abstraction: the evaluation family
    `((evaluation Iᵒᵈ C).obj : Iᵒᵈ → (Iᵒᵈ ⥤ C) ⥤ C)` viewed through
    `JointlyReflectIsomorphisms`
- primitive data: a short complex `S` of inverse systems and the evaluation functors at each index
- derived API: the stagewise short complex `S.app i` and the exactness criterion
  `inverse_system_exact_iff_exact_app`, both indexed by textbook stages `i : I`
- source/core/bridge triage: this theorem is a `source-facing` bridge specialization of the
  core/canonical theorem `JointlyReflectIsomorphisms.exact_iff`. -/

namespace ShortComplex

variable [HasZeroMorphisms C]

/-- The short complex obtained by evaluating a short complex of inverse systems at stage `i`. -/
abbrev app (S : ShortComplex (Iᵒᵈ ⥤ C)) (i : I) : ShortComplex C :=
  S.map ((evaluation Iᵒᵈ C).obj (toDual i))

end ShortComplex

section Additive

variable [Preadditive C]

/- Background recall: for a preadditive category `C`, the category of inverse systems
`Iᵒᵈ ⥤ C` inherits the canonical preadditive structure objectwise. -/
#check (inferInstance : Preadditive (Iᵒᵈ ⥤ C))

section Biproducts

variable [HasFiniteBiproducts C]

/- Background recall: if `C` has finite biproducts, then inverse systems with values in `C`
also have finite biproducts. -/
#check (HasFiniteBiproducts.of_hasFiniteProducts :
  HasFiniteBiproducts (Iᵒᵈ ⥤ C))

end Biproducts
end Additive

section Abelian

variable [Abelian C]

/- Background recall: if `C` is abelian, then the category of inverse systems with values in `C`
is abelian. -/
#check (inferInstance : Abelian (Iᵒᵈ ⥤ C))

/-- Lemma 12.31.1: a short complex of inverse systems is exact if and only if the evaluated
short complex is exact at every index. -/
theorem inverse_system_exact_iff_exact_app
    (S : ShortComplex (Iᵒᵈ ⥤ C)) :
    S.Exact ↔ ∀ i : I, (S.app i).Exact := by
  let hEval :
      JointlyReflectIsomorphisms
        ((evaluation Iᵒᵈ C).obj : Iᵒᵈ → (Iᵒᵈ ⥤ C) ⥤ C) := by
    refine ⟨fun {X Y} f _ ↦ ?_⟩
    rw [NatTrans.isIso_iff_isIso_app]
    intro i
    simpa using (inferInstance : IsIso (((evaluation Iᵒᵈ C).obj i).map f))
  constructor
  · intro hS i
    simpa [ShortComplex.app] using (hEval.exact_iff S).1 hS (toDual i)
  · intro hS
    exact (hEval.exact_iff S).2 fun i ↦ by
      simpa [ShortComplex.app] using hS (ofDual i)

end Abelian

end CategoryTheory
