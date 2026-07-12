import Mathlib
import StacksProject_2024.Chap28.Definition_28_4_2
import StacksProject_2024.Chap29.Definition_29_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- the source-facing scheme notions here are affine-local ring properties, and the Chapter 28
-- owner for that pattern is `HasRingPropertyLocally`; `Definition_29_47_1` provides the ring-side
-- owners `SeminormalRing` and `AbsolutelyWeaklyNormalRing`.

variable (X : Scheme.{u})

/-- Definition 29.47.3 (1): a scheme `X` is seminormal if every point of `X` admits an affine open
neighborhood whose ring of sections is seminormal. -/
@[stacks 0EUM]
abbrev Seminormal (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- On a seminormal scheme, every point lies in an affine open neighborhood with seminormal
coordinate ring. -/
theorem exists_affineOpen_seminormalRing (X : Scheme.{u}) [Seminormal X] (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ SeminormalRing (Γ(X, (U : X.Opens))) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ SeminormalRing A) x

/-- Unfold `Seminormal X` into the affine-open neighborhood condition on its points. -/
theorem seminormal_iff (X : Scheme.{u}) :
    Seminormal X ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        SeminormalRing (Γ(X, (U : X.Opens))) :=
  hasRingPropertyLocally_iff X (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- Definition 29.47.3 (2): a scheme `X` is absolutely weakly normal if every point of `X`
admits an affine open neighborhood whose ring of sections is absolutely weakly normal. -/
@[stacks 0EUM]
abbrev AbsolutelyWeaklyNormal (X : Scheme.{u}) : Prop :=
  X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

/-- On an absolutely weakly normal scheme, every point lies in an affine open neighborhood with
absolutely weakly normal coordinate ring. -/
theorem exists_affineOpen_absolutelyWeaklyNormalRing (X : Scheme.{u})
    [AbsolutelyWeaklyNormal X] (x : X) :
    ∃ U : X.affineOpens,
      x ∈ (U : X.Opens) ∧ AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) :=
  HasRingPropertyLocally.exists_affineOpen X
    (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A) x

/-- An absolutely weakly normal scheme is seminormal. -/
instance instSeminormalOfAbsolutelyWeaklyNormal (X : Scheme.{u}) [AbsolutelyWeaklyNormal X] :
    Seminormal X := by
  refine (seminormal_iff X).2 ?_
  intro x
  rcases exists_affineOpen_absolutelyWeaklyNormalRing X x with ⟨U, hxU, hU⟩
  let _ : AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) := hU
  exact ⟨U, hxU, inferInstance⟩

/-- Unfold `AbsolutelyWeaklyNormal X` into the affine-open neighborhood condition on its
points. -/
theorem absolutelyWeaklyNormal_iff (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∀ x : X,
        ∃ U : X.affineOpens,
          x ∈ (U : X.Opens) ∧ AbsolutelyWeaklyNormalRing (Γ(X, (U : X.Opens))) :=
  hasRingPropertyLocally_iff X
    (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

end AlgebraicGeometry.Scheme
