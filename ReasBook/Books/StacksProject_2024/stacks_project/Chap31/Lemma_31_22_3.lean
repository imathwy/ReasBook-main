import Mathlib
import StacksProject_2024.Chap29.Definition_29_25_1
import StacksProject_2024.Chap31.Definition_31_22_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-flatness owners
-- `AlgebraicGeometry.Flat` and `AlgebraicGeometry.Flat.iff_flat_stalkMap`; local Chapter 29/31
-- precedent packages the pointwise conclusion as `Scheme.Hom.flatAt` and the hypothesis as
-- `RelativeQuasiRegularImmersion f i`.

section

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- Lemma 31.22.3: if `i : Z ⟶ X` is a relative quasi-regular immersion over `f : X ⟶ S` and
`x : Z` has Noetherian local ring on its image in `X`, then `f` is flat at that image point. This
expresses the source condition `x ∈ Z` by taking `x` as a point of `Z`. -/
@[stacks 063T]
theorem RelativeQuasiRegularImmersion.flatAt
    [RelativeQuasiRegularImmersion f i] (x : Z)
    [IsNoetherianRing (X.presheaf.stalk (i.base x))] :
    Scheme.Hom.flatAt f (i.base x) := sorry

/-- Companion bridge to Lemma 31.22.3: under the same hypotheses, the induced stalk map on local
rings is flat at the image point of `x`. -/
theorem RelativeQuasiRegularImmersion.stalkMap_flat
    [RelativeQuasiRegularImmersion f i] (x : Z)
    [IsNoetherianRing (X.presheaf.stalk (i.base x))] :
    (f.stalkMap (i.base x)).hom.Flat := by
  simpa [Scheme.Hom.flatAt] using
    (RelativeQuasiRegularImmersion.flatAt x : Scheme.Hom.flatAt f (i.base x))

end

end AlgebraicGeometry
