import Mathlib
import StacksProject_2024.Chap29.Lemma_29_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced only generic normalization/reducedness APIs for
-- schemes, while local Chapter 29 precedent owns seminormal schemes via `Scheme.Seminormal` and
-- the seminormalization category via `SeminormalizationOver`. The Stacks tag evidence is
-- consistent: item tag `0H3G` agrees with the source URL ending in `/tag/0H3G`.

/-- Lemma 29.47.9 (1): a scheme `X` is seminormal if and only if the seminormalization morphism
`X^{sn} -> X` is an isomorphism. -/
@[stacks 0H3G]
theorem seminormal_iff_isIso_seminormalizationMap (X : Scheme.{u}) :
    Seminormal X ↔ IsIso ((⊥_ (SeminormalizationOver X)).1.hom) := sorry

/-- Lemma 29.47.9 (2): a scheme `X` is seminormal if and only if every universal homeomorphism
`Y -> X` inducing isomorphisms on residue fields, with `Y` reduced, is an isomorphism. -/
@[stacks 0H3G]
theorem seminormal_iff_universalHomeomorphism_residueFieldMap_isIso_isIso_of_isReduced
    (X : Scheme.{u}) :
    Seminormal X ↔
      ∀ {Y : Scheme.{u}} (π : Y ⟶ X), UniversalHomeomorphism π →
        (∀ y : Y, IsIso (π.residueFieldMap y)) → IsReduced Y → IsIso π := sorry

end AlgebraicGeometry.Scheme
