import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import StacksProject_2024.stacks_project.Chap29.Lemma_29_35_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` was unavailable here (`HTTP 429`), so the owner names were verified from local
  precedent instead: `Scheme.Hom.QuasiFiniteAt` in `Chap10/Lemma_10_123_13.lean`,
  `LocallyQuasiFinite` in `Chap29/Lemma_29_20_16.lean`, and the ring-level bridge
  `quasiFiniteAt_of_isUnramifiedAt` in `Chap10/Lemma_10_151_6.lean`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A morphism of schemes is unramified at `x` if its pullback along
`Spec(𝒪_{X, x}) ⟶ X` is unramified. -/
def Scheme.Hom.UnramifiedAt (f : X ⟶ S) (x : X) : Prop :=
  Unramified (X.fromSpecStalk x ≫ f)

/-- Unfolding lemma for `Scheme.Hom.UnramifiedAt`. -/
@[simp] theorem Scheme.Hom.unramifiedAt_iff (f : X ⟶ S) (x : X) :
    f.UnramifiedAt x ↔ Unramified (X.fromSpecStalk x ≫ f) :=
  Iff.rfl

/-- Lemma 29.35.10 (1): if a morphism of schemes is unramified at `x`, then it is quasi-finite at
`x`. -/
@[stacks 02V5]
theorem quasiFiniteAt_of_unramifiedAt (x : X) (h : f.UnramifiedAt x) :
    f.QuasiFiniteAt x := sorry

namespace Scheme.Hom

/-- A pointwise unramified morphism is quasi-finite at that point. -/
theorem UnramifiedAt.quasiFiniteAt {f : X ⟶ S} {x : X}
    (h : f.UnramifiedAt x) :
    f.QuasiFiniteAt x :=
  quasiFiniteAt_of_unramifiedAt x h

end Scheme.Hom

/-- Lemma 29.35.10 (2): an unramified morphism is locally quasi-finite. -/
@[stacks 02V5]
theorem unramified_locallyQuasiFinite (f : X ⟶ S) [Unramified f] :
    LocallyQuasiFinite f := sorry

/-- An unramified morphism is locally quasi-finite. -/
theorem Unramified.locallyQuasiFinite {f : X ⟶ S} (h : Unramified f) :
    LocallyQuasiFinite f := by
  letI : Unramified f := h
  exact unramified_locallyQuasiFinite f

end AlgebraicGeometry
