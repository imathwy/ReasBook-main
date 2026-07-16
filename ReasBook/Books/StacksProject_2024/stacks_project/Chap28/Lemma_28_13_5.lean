import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_13_1
import StacksProject_2024.stacks_project.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the affine-open-cover locality API around schemes, including
-- `Scheme.affineCover` and `of_affine_open_cover`. The local project analogue `Lemma 28.4.3`
-- already packages the exact affine/open-cover criteria for `HasRingPropertyLocally`, so this
-- item is best exposed as its specialization to the existing scheme owner `UniversallyJapanese`.

variable (X : Scheme.{u})

/-- Lemma 28.13.5 (1): a scheme `X` is universally Japanese if and only if for every affine open
`U ⊆ X`, the ring of sections `Γ(X, U)` is universally Japanese. -/
@[stacks 033W]
theorem universallyJapanese_iff_forall_affineOpen_sectionsRing_universallyJapanese :
    UniversallyJapanese X ↔
      ∀ U : X.affineOpens, UniversallyJapaneseRing.{u, u} (Γ(X, U)) := sorry

/-- Lemma 28.13.5 (2): a scheme `X` is universally Japanese if and only if it admits an affine
open covering whose section rings are universally Japanese. -/
@[stacks 033W]
theorem universallyJapanese_iff_exists_affineOpenCover_sectionsRing_universallyJapanese :
    UniversallyJapanese X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, UniversallyJapaneseRing.{u, u} (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- Lemma 28.13.5 (3): a scheme `X` is universally Japanese if and only if it admits an open
covering by universally Japanese open subschemes. -/
@[stacks 033W]
theorem universallyJapanese_iff_exists_openCover_by_universallyJapanese :
    UniversallyJapanese X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, UniversallyJapanese ((𝒰.f i).opensRange).toScheme := sorry

/-- Lemma 28.13.5 (4): if a scheme `X` is universally Japanese, then every open subscheme of `X`
is universally Japanese. -/
@[stacks 033W]
theorem universallyJapanese_toScheme (hX : UniversallyJapanese X) (U : X.Opens) :
    UniversallyJapanese U.toScheme := sorry

end AlgebraicGeometry.Scheme
