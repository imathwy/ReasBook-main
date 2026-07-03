import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Lemma 20.47.2 (1): the intrinsic owner is the ringed-space predicate
`AlgebraicGeometry.RingedSpace.IsMPseudoCoherent`, and
`isMPseudoCoherent_iff_exists_openCover` is its open-cover bridge. -/
recall IsMPseudoCoherent

-- Proof sketch: unpack the intrinsic local strictly perfect approximation data witnessing
-- `DerivedCategory.IsMPseudoCoherent E m`, then use Lemma `20.46.8` to realize each derived local
-- map by an actual morphism of restricted complexes for the chosen representative `K`. Those
-- local morphisms satisfy the complex-level approximation criterion and therefore witness
-- `CochainComplex.IsMPseudoCoherent K m`.
/-- Lemma 20.47.2 (2): if a derived `\mathcal O_X`-module is `m`-pseudo-coherent, then every
cochain complex representing it is `m`-pseudo-coherent. -/
theorem representing_complex_isMPseudoCoherent_of_derived_isMPseudoCoherent
    (E : DModX) (m : ℤ) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e :
      E ≅
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX).obj K)
    (hE : IsMPseudoCoherent E m) :
    CochainComplex.IsMPseudoCoherent K m := sorry

end AlgebraicGeometry.RingedSpace
