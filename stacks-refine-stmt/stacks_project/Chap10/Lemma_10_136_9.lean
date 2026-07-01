import stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

namespace Algebra

variable {R : Type u} {R' : Type v} {Rf : Type v} {S : Type w}
variable [CommRing R] [CommRing R'] [CommRing Rf] [CommRing S]
variable [Algebra R S] [Algebra R R'] [Algebra R Rf]

namespace IsRelativeGlobalCompleteIntersection

-- Proof sketch: choose a finite presentation witness for `S` over `R`, base change that
-- presentation along `R → R'` using `Algebra.Presentation.baseChange`, and identify the fibers of
-- the new presentation with the base changes of the original fibers to transport the dimension
-- condition via Lemma 10.116.5.
/-- Lemma 10.136.9 (1): relative global complete intersections are stable under base change. -/
theorem baseChange (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection R' (R' ⊗[R] S) := sorry

-- Proof sketch: write `Localization.Away g` as a localization of the chosen presentation of `S`,
-- realized by adjoining one generator and one relation `h * X - 1`, and then check that each
-- fiber is the corresponding localization of the original fiber, so the presentation dimension is
-- unchanged.
/-- Lemma 10.136.9 (2): localizing away from an element of a relative global complete
intersection again yields a relative global complete intersection over the same base. -/
theorem localizationAway (hS : IsRelativeGlobalCompleteIntersection R S) (g : S) :
    IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

variable [Algebra Rf S] [IsScalarTower R Rf S]

-- Proof sketch: identify `S` with the base change `Rf ⊗[R] S` coming from the factorization
-- `R → Rf → S`, apply the base-change statement to `hS`, and transport the result across the
-- canonical localization tensor-product equivalence.
/-- Lemma 10.136.9 (3): if `R → S` factors through a localization `R_f`, then `S` is a relative
global complete intersection over `R_f`. -/
theorem of_isLocalizationAway (f : R) [IsLocalization.Away f Rf]
    (hS : IsRelativeGlobalCompleteIntersection R S) :
    IsRelativeGlobalCompleteIntersection Rf S := sorry

end IsRelativeGlobalCompleteIntersection

end Algebra

end
