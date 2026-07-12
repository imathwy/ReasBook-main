import Mathlib
import StacksProject_2024.Chap10.Lemma_10_135_10
import StacksProject_2024.Chap29.Lemma_29_30_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory Limits
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced mathlib's base-change stability owners
  `AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange` and
  `AlgebraicGeometry.isSmooth_isStableUnderBaseChange`;
- local Chapter 29 precedent records base-changed scheme morphisms by the canonical projection
  `pullback.snd`, and Lemma 29.30.10 packages syntomicity at a point through the closed-fiber
  complete-intersection condition.
-/

variable {X S S' : Scheme.{u}}

/-- The locus of points whose closed fiber local ring is a complete intersection over the residue
field of the image point. -/
@[stacks 02V3]
def fiberCompleteIntersectionLocus (f : X ⟶ S) : Set X :=
  { x | f.closedFiberCompleteIntersectionAt x }

/-- Membership in `fiberCompleteIntersectionLocus` is exactly the closed-fiber complete-
intersection condition at that point. -/
theorem mem_fiberCompleteIntersectionLocus (f : X ⟶ S) (x : X) :
    x ∈ f.fiberCompleteIntersectionLocus ↔ f.closedFiberCompleteIntersectionAt x := sorry

/-- Lemma 29.30.12 (1): if `f : X ⟶ S` is locally of finite type and `g : S' ⟶ S` is any base
change, then the complete-intersection fiber locus of the base change `pullback.snd f g` is the
inverse image of the complete-intersection fiber locus of `f` under the projection
`pullback.fst f g`. -/
@[stacks 02V3]
theorem fiberCompleteIntersectionLocus_pullback_snd
    (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) :
    (pullback.snd f g).fiberCompleteIntersectionLocus =
      (pullback.fst f g) ⁻¹' f.fiberCompleteIntersectionLocus := sorry

/-- Lemma 29.30.12 (2): if `f : X ⟶ S` is flat and locally of finite presentation, then for every
point `x'` of the base change `pullback f g` the morphism `pullback.snd f g` is syntomic at `x'`
if and only if `f` is syntomic at the image point `(pullback.fst f g)(x')`. Equivalently, the
open syntomic locus commutes with arbitrary base change. -/
@[stacks 02V3]
theorem syntomicAt_iff_of_pullback_snd
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] (g : S' ⟶ S)
    (x' : (pullback f g : Scheme)) :
    SyntomicAt (pullback.snd f g) x' ↔ SyntomicAt f ((pullback.fst f g) x') := sorry

end Scheme.Hom

end AlgebraicGeometry
