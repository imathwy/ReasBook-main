import Mathlib.Algebra.Homology.HomologySequenceLemmas

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open HomologicalComplex
open HomologicalComplex.HomologySequence

universe v u

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Domain-style sampling:
- primary domain: connecting morphism naturality in the long exact homology sequence of short exact
  sequences of cochain complexes in an abelian category;
- sampled owner declarations: `HomologicalComplex.HomologySequence.δ_naturality`,
  `ShortComplex.SnakeInput.naturality_δ`, `CategoryTheory.CommSq`;
- best owner abstraction:
  `source-facing`: the Bockstein factorization square in degree `i ⟶ i + 1`;
  `core/canonical`: `HomologicalComplex.HomologySequence.δ_naturality`;
  `bridge/view`: the cochain-shape specialization `ComplexShape.up_mk i (i + 1) rfl`;
- primitive data vs derived API: the primitive inputs are the short exact rows and the morphism
  `φ`; the displayed factorization square is derived from the owner naturality theorem, so no
  separate `ModuleCat`-specific wrapper belongs in the public API. -/

/-- 15.96.5.1: the Bockstein factorization diagram is the `j = i + 1` specialization of the
naturality square for the connecting morphism attached to a morphism of short exact sequences of
cochain complexes. -/
-- Proof sketch: specialize the canonical owner square `δ_naturality` to the cochain-shape
-- relation `i ⟶ i + 1`. In the Berthelot-Ogus situation, `S₁` and `S₂` are the two successive
-- quotient short exact sequences, and the lower horizontal map is the diagonal Bockstein map.
theorem bockstein_factorization_naturality
    {S₁ S₂ : ShortComplex (CochainComplex C ℤ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (i : ℤ) :
    CommSq
      (homologyMap φ.τ₃ i)
      (hS₁.δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl))
      (hS₂.δ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl))
      (homologyMap φ.τ₁ (i + 1)) := by
  exact .mk <|
    (δ_naturality φ hS₁ hS₂ i (i + 1) (ComplexShape.up_mk i (i + 1) rfl)).symm

end
