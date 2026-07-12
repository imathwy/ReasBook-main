import StacksProject_2024.Chap29.Definition_29_36_1
import StacksProject_2024.Chap29.Lemma_29_35_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `AlgebraicGeometry.IsEtale`,
  `AlgebraicGeometry.IsSmooth`, and the instance `AlgebraicGeometry.IsEtale.instIsSmooth`;
- local Chapter 29 precedent already defines `Scheme.Hom.UnramifiedAt` in
  `Chap29/Lemma_29_35_10.lean`, so this item is stated as the pointwise stalk-pullback bridge.
-/

/- Lemma 29.36.5 uses the canonical global scheme-side owners `Smooth` and `Etale`; the
source-facing content here is their pointwise pullback along `Spec(𝒪_{X, x}) ⟶ X`. -/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- A morphism of schemes is smooth at `x` if its pullback along `Spec(𝒪_{X, x}) ⟶ X` is smooth. -/
def Scheme.Hom.SmoothAt (f : X ⟶ S) (x : X) : Prop :=
  Smooth (X.fromSpecStalk x ≫ f)

/-- Unfolding lemma for `Scheme.Hom.SmoothAt`. -/
@[simp] theorem Scheme.Hom.smoothAt_iff (f : X ⟶ S) (x : X) :
    f.SmoothAt x ↔ Smooth (X.fromSpecStalk x ≫ f) := Iff.rfl

/-- If `f` is étale at `x`, then it is smooth at `x`. -/
theorem Scheme.Hom.SmoothAt.of_etaleAt {f : X ⟶ S} {x : X} (h : f.EtaleAt x) :
    f.SmoothAt x := by
  sorry

/-- Lemma 29.36.5: a morphism of schemes is étale at `x` if and only if it is smooth and
unramified at `x`. -/
@[stacks 02GP]
theorem etaleAt_iff_smoothAt_and_unramifiedAt (x : X) :
    f.EtaleAt x ↔ f.SmoothAt x ∧ f.UnramifiedAt x := sorry

end AlgebraicGeometry
