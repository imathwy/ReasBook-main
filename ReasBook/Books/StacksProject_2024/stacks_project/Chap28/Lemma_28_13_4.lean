import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check: `lean_leansearch` surfaced the affine-open/open-cover
-- locality API for schemes, and the local Chapter 28 analogue `Lemma_28_13_5` already packages
-- the same pattern for `UniversallyJapanese`. This item is the integral `N-2` specialization
-- through the existing owner `IsJapanese`, using bundled-object nonemptiness on opens and affine
-- opens so the public surface matches the canonical subscheme instance API.

variable (X : Scheme.{u}) [IsIntegral X]

/-- Lemma 28.13.4 (1): an integral scheme `X` is Japanese if and only if for every nonempty affine
open `U ⊆ X`, the coordinate ring `Γ(X, U)` is `N-2`, hence Japanese as a domain. -/
@[stacks 033V]
theorem isJapanese_iff_forall_affineOpen_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∀ U : X.affineOpens,
        ∀ hU : Nonempty U,
          affineOpenSectionsIsN2Ring X U hU := sorry

/-- Lemma 28.13.4 (2): an integral scheme `X` is Japanese if and only if it admits an affine
open covering whose nonempty members have `N-2` coordinate rings, hence Japanese domains. -/
@[stacks 033V]
theorem isJapanese_iff_exists_affineOpenCover_sectionsRing_isN2Ring :
    IsJapanese X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          ∀ hU : Nonempty (𝒰.f i).opensRange,
            affineOpenSectionsIsN2Ring X
              ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange (𝒰.f i)⟩ hU := sorry

/-- Lemma 28.13.4 (3): an integral scheme `X` is Japanese if and only if it admits an open
covering by nonempty Japanese open subschemes. -/
@[stacks 033V]
theorem isJapanese_iff_exists_openCover_by_isJapanese :
    IsJapanese X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀,
          ∀ hU : Nonempty (𝒰.f i).opensRange,
            IsJapanese ((𝒰.f i).opensRange).toScheme := sorry

variable {X : Scheme.{u}} [IsIntegral X]

/-- Lemma 28.13.4 (4): every nonempty open subscheme of an integral Japanese scheme is Japanese. -/
@[stacks 033V]
theorem isJapanese_toScheme (hX : IsJapanese X) (U : X.Opens) (hU : Nonempty U) :
    IsJapanese U.toScheme := sorry

end AlgebraicGeometry.Scheme
