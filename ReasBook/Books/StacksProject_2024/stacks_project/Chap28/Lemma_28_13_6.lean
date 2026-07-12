import StacksProject_2024.Chap28.Definition_28_13_1
import StacksProject_2024.Chap28.Lemma_28_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical affine/open-cover scheme owners
-- `Scheme.affineOpenCover`, `Scheme.affineCover`, and `Scheme.Opens.toScheme`. In the current
-- project, arbitrary Nagata schemes are already packaged by `Scheme.Nagata`, while
-- `Lemma_28_4_3` gives the general affine/open-cover criterion for `HasRingPropertyLocally`.
-- This item is therefore the `NagataRing` specialization of that existing locality API.

/-- Lemma 28.13.6 (1): a scheme `X` is Nagata if and only if the ring of sections of every affine
open of `X` is Nagata. -/
@[stacks 033X]
theorem nagata_iff_forall_affineOpen_sectionsRing_nagataRing (X : Scheme.{u}) :
    Nagata X ↔
      ∀ U : X.affineOpens, NagataRing (Γ(X, U)) := by
  simpa [Nagata] using
    hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
      (fun A : CommRingCat.{u} ↦ NagataRing A)

/-- Lemma 28.13.6 (2): a scheme `X` is Nagata if and only if it admits an affine open cover whose
section rings are Nagata. -/
@[stacks 033X]
theorem nagata_iff_exists_affineOpenCover_sectionsRing_nagataRing (X : Scheme.{u}) :
    Nagata X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, NagataRing (Γ(X, (𝒰.f i).opensRange)) := by
  simpa [Nagata] using
    hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
      (fun A : CommRingCat.{u} ↦ NagataRing A)

/-- Lemma 28.13.6 (3): a scheme `X` is Nagata if and only if it admits an open cover by Nagata
open subschemes. -/
@[stacks 033X]
theorem nagata_iff_exists_openCover_by_nagata (X : Scheme.{u}) :
    Nagata X ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Nagata ((𝒰.f i).opensRange).toScheme := by
  simpa [Nagata] using
    hasRingPropertyLocally_iff_exists_openCover_by_hasRingPropertyLocally X
      (fun A : CommRingCat.{u} ↦ NagataRing A)

/-- Lemma 28.13.6 (4): every open subscheme of a Nagata scheme is Nagata. -/
@[stacks 033X]
theorem nagata_toScheme {X : Scheme.{u}} (hX : Nagata X) (U : X.Opens) :
    Nagata U.toScheme := by
  change U.toScheme.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ NagataRing A)
  exact hasRingPropertyLocally_toScheme hX U

end AlgebraicGeometry.Scheme
