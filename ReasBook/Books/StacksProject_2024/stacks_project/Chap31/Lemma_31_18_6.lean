import Mathlib
import StacksProject_2024.Chap31.Definition_31_18_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced mathlib's open-restriction flatness API
-- `AlgebraicGeometry.Flat.instMorphismRestrict` together with the canonical open-subscheme
-- inclusion `Scheme.Opens.ι`. Following local Chapter 31 precedent, the relative effective
-- Cartier divisor is the ideal-sheaf datum `D : X.IdealSheafData`, and the source condition
-- `D ⊆ U` is expressed by the inclusion of supports `(D.support : Set X) ⊆ U`.

/-- Lemma 31.18.6: let `f : X ⟶ S` be a morphism of schemes and let `D ⊆ X` be a relative
effective Cartier divisor. If `f` is locally of finite presentation, then there exists an open
subscheme `U ⊆ X` containing `D`, represented here as `(D.support : Set X) ⊆ U`, such that the
restricted morphism `f|_U : U ⟶ S`, written as `U.ι ≫ f`, is flat. -/
@[stacks 062V]
theorem IsRelativeEffectiveCartierDivisor.exists_flat_openContaining_support_of_locallyOfFinitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) (D : X.IdealSheafData)
    [IsRelativeEffectiveCartierDivisor f D] [LocallyOfFinitePresentation f] :
    ∃ U : X.Opens, (D.support : Set X) ⊆ (U : Set X) ∧ Flat (U.ι ≫ f) := sorry

end AlgebraicGeometry
