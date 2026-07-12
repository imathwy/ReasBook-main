import Mathlib
import StacksProject_2024.Chap28.Definition_28_9_1
import StacksProject_2024.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the affine-open scheme infrastructure (`Scheme.affineOpens`,
-- `IsLocallyNoetherian.component_noetherian`) and local Chapter 28 precedent packages local scheme
-- properties through the scheme owner `Regular` together with affine-open section-ring conditions.
-- The source phrase “Noetherian and regular” is therefore recorded by `IsRegularRing`, whose owner
-- already includes the Noetherian part.

variable (X : Scheme.{u})

/-- Lemma 28.9.3 (1): a scheme `X` is regular if and only if for every affine open `U ⊆ X`, the
ring of sections `Γ(X, U)` is regular; this formalization uses `IsRegularRing`, which already
packages the source's “Noetherian and regular” condition. -/
@[stacks 02IU]
theorem regular_iff_forall_affineOpen_sectionsRing_isRegularRing :
    Regular X ↔
      ∀ U : X.affineOpens, IsRegularRing (Γ(X, (U : X.Opens))) := sorry

/-- Lemma 28.9.3 (2): a scheme `X` is regular if and only if it admits an affine open covering
whose section rings are regular; again `IsRegularRing` includes the Noetherian hypothesis from the
source. -/
@[stacks 02IU]
theorem regular_iff_exists_affineOpenCover_sectionsRing_isRegularRing :
    Regular X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, IsRegularRing (Γ(X, (𝒰.openCover.f i).opensRange)) := sorry

/-- Lemma 28.9.3 (3): a scheme `X` is regular if and only if it admits an open covering by regular
open subschemes. -/
@[stacks 02IU]
theorem regular_iff_exists_openCover_by_regularOpens :
    Regular X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Regular ((𝒰.f i).opensRange).toScheme := sorry

variable {X : Scheme.{u}}

/-- Lemma 28.9.3 (4): every open subscheme of a regular scheme is regular. -/
@[stacks 02IU]
theorem regular_toScheme (hX : Regular X) (U : X.Opens) :
    Regular U.toScheme := sorry

end AlgebraicGeometry.Scheme
