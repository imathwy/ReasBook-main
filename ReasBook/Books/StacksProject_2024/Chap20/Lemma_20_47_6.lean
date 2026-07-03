import Mathlib
import stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: use the distinguished triangle from Derived Categories, Lemma `13.4.10` attached
-- to the projection `K ⊞ L ⟶ K`, identify the third term with `L ⊞ L⟦(1 : ℤ)⟧`, and apply
-- Lemma `20.47.4` repeatedly exactly as in the affine case to descend from large shifts back to
-- `K`.
/-- Lemma 20.47.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O_X)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DModX) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m := sorry

-- Proof sketch: apply the previous distinguished-triangle argument after swapping the two
-- biproduct factors, or equivalently use the symmetric triangle attached to the projection
-- `K ⊞ L ⟶ L`.
/-- Lemma 20.47.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O_X)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DModX) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent L m := sorry

-- Proof sketch: pseudo-coherence means `m`-pseudo-coherence for every integer. Apply part `(1)`
-- degreewise to the biproduct and then repackage the resulting family of statements.
/-- Lemma 20.47.6 (3): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O_X)`, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DModX)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K := sorry

-- Proof sketch: as in part `(3)`, pseudo-coherence is checked degreewise; apply part `(2)` for
-- every integer `m` and collect the resulting `m`-pseudo-coherence statements for `L`.
/-- Lemma 20.47.6 (4): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O_X)`, then `L` is
pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DModX)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent L := sorry

end AlgebraicGeometry.RingedSpace
