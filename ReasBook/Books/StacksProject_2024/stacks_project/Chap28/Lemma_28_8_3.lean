import Mathlib
import StacksProject_2024.Chap28.Definition_28_8_1
import StacksProject_2024.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical affine-cover infrastructure around schemes, including
-- `Scheme.affineCover` and `isLocallyNoetherian_of_affine_cover`. In this chapter, the exact local
-- pattern is already expressed by `Lemma 28.4.3`, and Definition `28.8.1` now keeps the
-- Cohen-Macaulay condition directly as the `HasRingPropertyLocally` specialization, so this item
-- is best exposed as its affine/open-cover criteria.

variable (X : Scheme.{u})

/-- Lemma 28.8.3 (1): a scheme `X` is Cohen-Macaulay if and only if for every affine open
`U ⊆ X`, the ring of sections `Γ(X, U)` is Cohen-Macaulay; this formalization uses
`CohenMacaulayRing`, which already includes the source's Noetherian hypothesis. -/
@[stacks 02IQ]
theorem cohenMacaulay_iff_forall_affineOpen_sectionsRing_cohenMacaulayRing :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      ∀ U : X.affineOpens, CohenMacaulayRing (Γ(X, (U : X.Opens))) := sorry

/-- Lemma 28.8.3 (2): a scheme `X` is Cohen-Macaulay if and only if it admits an affine open
covering whose section rings are Cohen-Macaulay; again `CohenMacaulayRing` packages the source's
Noetherian and Cohen-Macaulay ring condition. -/
@[stacks 02IQ]
theorem cohenMacaulay_iff_exists_affineOpenCover_sectionsRing_cohenMacaulayRing :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, CohenMacaulayRing (Γ(X, (𝒰.openCover.f i).opensRange)) := sorry

/-- Lemma 28.8.3 (3): a scheme `X` is Cohen-Macaulay if and only if it admits an open covering
by Cohen-Macaulay open subschemes. -/
@[stacks 02IQ]
theorem cohenMacaulay_iff_exists_openCover_by_cohenMacaulay :
    X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀,
          ((𝒰.f i).opensRange).toScheme.HasRingPropertyLocally
            (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) := sorry

variable {X : Scheme.{u}}

/-- Lemma 28.8.3 (4): every open subscheme of a Cohen-Macaulay scheme is Cohen-Macaulay. -/
@[stacks 02IQ]
theorem hasRingPropertyLocally_cohenMacaulayRing_toScheme
    (hX : X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A))
    (U : X.Opens) :
    U.toScheme.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ CohenMacaulayRing A) := sorry

end AlgebraicGeometry.Scheme
