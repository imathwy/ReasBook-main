import Mathlib
import StacksProject_2024.Chap28.Lemma_28_4_3
import StacksProject_2024.Chap29.Lemma_29_47_2
import StacksProject_2024.Chap29.Definition_29_47_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced generic affine-local/open-cover APIs, while the
-- local Chapter 28/29 owner for this source item is the scheme predicate
-- `HasRingPropertyLocally`; Lemma 28.4.3 supplies the cover/restriction interfaces used here.

/-- Lemma 29.47.4 (1): a scheme `X` is seminormal if and only if for every affine open
`U ⊆ X`, the ring of sections `Γ(X, U)` is seminormal. -/
@[stacks 0EUP]
theorem seminormal_iff_forall_affineOpen_sectionsRing (X : Scheme.{u}) :
    Seminormal X ↔
      ∀ U : X.affineOpens, SeminormalRing (Γ(X, U)) := by
  simpa [Seminormal] using
    hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
      (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- Lemma 29.47.4 (2): a scheme `X` is seminormal if and only if it admits an affine open
covering whose section rings are seminormal. -/
@[stacks 0EUP]
theorem seminormal_iff_exists_affineOpenCover_sectionsRing (X : Scheme.{u}) :
    Seminormal X ↔
      ∃ 𝒰 : X.AffineOpenCover, ∀ i : 𝒰.I₀, SeminormalRing (Γ(X, (𝒰.f i).opensRange)) := by
  simpa [Seminormal] using
    hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
      (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- Lemma 29.47.4 (3): a scheme `X` is seminormal if and only if it admits an open covering by
open subschemes that are seminormal. -/
@[stacks 0EUP]
theorem seminormal_iff_exists_openCover (X : Scheme.{u}) :
    Seminormal X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Seminormal ((𝒰.f i).opensRange).toScheme := by
  simpa [Seminormal] using
    hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
      (fun A : CommRingCat.{u} ↦ SeminormalRing A)

/-- Lemma 29.47.4 (4): if a scheme `X` is seminormal, then every open subscheme of `X` is
seminormal. -/
@[stacks 0EUP]
theorem seminormal_toScheme {X : Scheme.{u}} (hX : Seminormal X) (U : X.Opens) :
    Seminormal U.toScheme := by
  change U.toScheme.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ SeminormalRing A)
  exact hasRingPropertyLocally_toScheme hX U

/-- Lemma 29.47.4 (5): a scheme `X` is absolutely weakly normal if and only if for every affine
open `U ⊆ X`, the ring of sections `Γ(X, U)` is absolutely weakly normal. -/
@[stacks 0EUP]
theorem absolutelyWeaklyNormal_iff_forall_affineOpen_sectionsRing (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∀ U : X.affineOpens, AbsolutelyWeaklyNormalRing (Γ(X, U)) := by
  simpa [AbsolutelyWeaklyNormal] using
    hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
      (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

/-- Lemma 29.47.4 (6): a scheme `X` is absolutely weakly normal if and only if it admits an affine
open covering whose section rings are absolutely weakly normal. -/
@[stacks 0EUP]
theorem absolutelyWeaklyNormal_iff_exists_affineOpenCover_sectionsRing (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, AbsolutelyWeaklyNormalRing (Γ(X, (𝒰.f i).opensRange)) := by
  simpa [AbsolutelyWeaklyNormal] using
    hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
      (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

/-- Lemma 29.47.4 (7): a scheme `X` is absolutely weakly normal if and only if it admits an open
covering by open subschemes that are absolutely weakly normal. -/
@[stacks 0EUP]
theorem absolutelyWeaklyNormal_iff_exists_openCover (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, AbsolutelyWeaklyNormal ((𝒰.f i).opensRange).toScheme := by
  simpa [AbsolutelyWeaklyNormal] using
    hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
      (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)

/-- Lemma 29.47.4 (8): if a scheme `X` is absolutely weakly normal, then every open subscheme of
`X` is absolutely weakly normal. -/
@[stacks 0EUP]
theorem absolutelyWeaklyNormal_toScheme {X : Scheme.{u}}
    (hX : AbsolutelyWeaklyNormal X) (U : X.Opens) :
    AbsolutelyWeaklyNormal U.toScheme := by
  change U.toScheme.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ AbsolutelyWeaklyNormalRing A)
  exact hasRingPropertyLocally_toScheme hX U

end AlgebraicGeometry.Scheme
