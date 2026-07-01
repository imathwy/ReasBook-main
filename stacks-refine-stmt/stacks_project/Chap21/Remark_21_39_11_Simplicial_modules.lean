import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicTopology
open Opposite
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory

/-- The associated chain complex `s(M_•)` of a simplicial `B`-module `M_•`, given by the
alternating face map construction. -/
abbrev simplicialModuleAssociatedComplex (B : Type u) [CommRing B]
    (M : SimplicialObject (ModuleCat B)) : ChainComplex (ModuleCat B) ℕ :=
  (alternatingFaceMapComplex (ModuleCat B)).obj M

/-- A simplicial `B`-module is termwise flat if each module of simplices is flat over `B`. -/
abbrev simplicialModuleTermwiseFlat (B : Type u) [CommRing B]
    (M : SimplicialObject (ModuleCat B)) : Prop :=
  ∀ n : ℕ, Module.Flat B (M _⦋n⦌)

-- Proof sketch: unfold `simplicialModuleAssociatedComplex`; it is defined to be the alternating
-- face map complex attached to the simplicial module.
/-- The notation `s(M_•)` is implemented by the alternating face map complex of `M_•`. -/
theorem simplicialModuleAssociatedComplex_def {B : Type u} [CommRing B]
    (M : SimplicialObject (ModuleCat B)) :
    simplicialModuleAssociatedComplex B M =
      (alternatingFaceMapComplex (ModuleCat B)).obj M := sorry

-- Proof sketch: unfold `simplicialModuleTermwiseFlat`; the predicate is exactly the assertion
-- that each simplicial degree `M_n` is a flat `B`-module.
/-- Termwise flatness means flatness in every simplicial degree. -/
theorem simplicialModuleTermwiseFlat_iff {B : Type u} [CommRing B]
    (M : SimplicialObject (ModuleCat B)) :
    simplicialModuleTermwiseFlat B M ↔
      ∀ n : ℕ, Module.Flat B (M _⦋n⦌) := sorry

-- Proof sketch: specialize Lemma `21.39.10` to `\mathcal C = \Delta`, where `L\pi_!` is computed
-- by the alternating face map complex. Termwise flatness identifies the derived tensor products
-- with ordinary tensor products, and the resulting comparison map is the simplicial
-- Eilenberg-Zilber quasi-isomorphism.
/-- Remark 21.39.11 (Simplicial modules): if `M_•` and `M'_•` are termwise flat simplicial
`B`-modules, then the associated complex of their pointwise tensor product is quasi-isomorphic to
the total tensor product of the associated complexes `s(M_•)` and `s(M'_•)`. -/
theorem exists_quasiIso_simplicialModuleAssociatedComplex_tensor_of_termwiseFlat
    {B : Type u} [CommRing B]
    (M M' : SimplicialObject (ModuleCat B))
    (hM : simplicialModuleTermwiseFlat B M)
    (hM' : simplicialModuleTermwiseFlat B M') :
    ∃ α : simplicialModuleAssociatedComplex B (M ⊗ M') ⟶
        simplicialModuleAssociatedComplex B M ⊗ simplicialModuleAssociatedComplex B M',
      QuasiIso α := sorry

end CategoryTheory
