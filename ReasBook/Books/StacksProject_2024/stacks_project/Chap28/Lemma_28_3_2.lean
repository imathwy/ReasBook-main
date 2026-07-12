import StacksProject_2024.Chap26.Lemma_26_12_2
import StacksProject_2024.Chap28.Lemma_28_4_3
import StacksProject_2024.Chap28.Lemma_28_4_4
import Mathlib.Tactic.Recall
import Mathlib.RingTheory.LocalProperties.Reduced

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace IsReduced

/-- Reducedness is a local ring property in the Chapter 28 affine-local sense. -/
@[instance]
theorem ringPropertyIsLocal :
    RingPropertyIsLocal (fun A : CommRingCat.{u} ↦ _root_.IsReduced A) := by
  sorry

end IsReduced

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

-- Source/core/bridge triage:
-- - source-facing: Lemma 28.3.2 records reducedness through affine section rings and affine open
--   covers;
-- - core/canonical: Chapter 26 already owns the open-level criterion `Scheme.isReduced_iff`, and
--   Chapter 28 owns affine-local ring properties through `Scheme.HasRingPropertyLocally`;
-- - bridge/view: this file specializes the existing local-ring-property criteria for reducedness,
--   keeping the affine-open and affine-cover forms as the source-facing surfaces.

/-- Lemma 28.3.2 (1): a scheme `X` is reduced iff it admits an affine open cover whose section
rings are reduced. -/
@[stacks 01OL]
theorem isReduced_iff_exists_affineOpenCover_sectionsRing_isReduced :
    IsReduced X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, _root_.IsReduced (Γ(X, (𝒰.f i).opensRange)) := by
  exact
    (isReduced_iff_hasRingPropertyLocally_isReduced X).trans
      (hasRingPropertyLocally_iff_exists_affineOpenCover_sectionsRing X
        (fun A : CommRingCat.{u} ↦ _root_.IsReduced A))

/-- Lemma 28.3.2 (2): a scheme `X` is reduced iff every affine open of `X` has reduced ring of
sections. -/
@[stacks 01OL]
theorem isReduced_iff_forall_affineOpen_sectionsRing_isReduced :
    IsReduced X ↔
      ∀ U : X.affineOpens, _root_.IsReduced (Γ(X, U)) := by
  exact
    (isReduced_iff_hasRingPropertyLocally_isReduced X).trans
      (hasRingPropertyLocally_iff_forall_affineOpen_sectionsRing X
        (fun A : CommRingCat.{u} ↦ _root_.IsReduced A))

/- Lemma 28.3.2 (3): the open-sections criterion is already the Chapter 26 canonical owner
`Scheme.isReduced_iff`, so this clause is a direct recall rather than a duplicate local wrapper. -/
recall isReduced_iff

end AlgebraicGeometry.Scheme
