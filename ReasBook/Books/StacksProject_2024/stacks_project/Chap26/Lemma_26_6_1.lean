import Mathlib.AlgebraicGeometry.AffineScheme

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Source/core/bridge triage:
-- `source-facing`: the affine-target point formula of Stacks Lemma 26.6.1.
-- `core/canonical`: `LocallyRingedSpace.toΓSpecFun` and `identityToΓSpec.naturality`.
-- `bridge/view`: the induced pointwise `Spec.map` formula on canonical points.

-- Semantic recall: `lean_leansearch` surfaced `LocallyRingedSpace.toΓSpecFun` and the scheme-side
-- point formula `Scheme.toSpecΓ_apply`; for an affine target, the canonical bridge is `Y.isoSpec`.

variable {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y]

/-- For a morphism to an affine scheme, the induced map on points agrees with the canonical
`Spec.map` formula after identifying `Y` with `Spec Γ(Y, ⊤)`. -/
theorem isoSpec_hom_base_apply_eq_specMap_toΓSpecFun
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    Y.isoSpec.hom (f.base x) = (Spec.map (Γ.map f.op)) (X.toΓSpecFun x) := by
  have h :=
    congrArg
      (fun g : X ⟶ Spec.locallyRingedSpaceObj (Γ.obj (op Y.toLocallyRingedSpace)) ↦ g.base x)
      (identityToΓSpec.naturality f)
  simpa only [LocallyRingedSpace.comp_base, Scheme.toSpecΓ_apply, Scheme.isoSpec_hom] using h

/-- Lemma 26.6.1: if `f : X ⟶ Y.toLocallyRingedSpace` is a morphism from a locally ringed space to
an affine scheme, then for every `x : X` the image `f(x)` is the point of `Y` corresponding, via
`Y.isoSpec`, to the prime ideal of `Γ(Y, ⊤)` obtained by pulling back the maximal ideal of
`𝒪_{X, x}` along `Γ(Y, ⊤) → Γ(X, ⊤) → 𝒪_{X, x}`. -/
@[stacks 01HY]
theorem base_apply_eq_isoSpec_inv_specMap_toΓSpecFun
    (f : X ⟶ Y.toLocallyRingedSpace) (x : X) :
    f.base x =
      Y.isoSpec.inv ((Spec.map (Γ.map f.op)) (X.toΓSpecFun x)) := by
  simpa using congrArg Y.isoSpec.inv (isoSpec_hom_base_apply_eq_specMap_toΓSpecFun f x)

end AlgebraicGeometry.LocallyRingedSpace
