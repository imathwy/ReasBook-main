import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_47_9

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced only generic scheme-normalization APIs, while
-- local Chapter 29 precedent fixes the absolute weak normalization owner as the initial object of
-- `AbsoluteWeakNormalizationOver X`. The Stacks tag evidence is consistent: item tag `0H3H`
-- agrees with the source URL ending in `/tag/0H3H`.

/-- Lemma 29.47.10 (1): a scheme `X` is absolutely weakly normal if and only if the absolute weak
normalization morphism `X^{awn} -> X` is an isomorphism. -/
@[stacks 0H3H]
theorem absolutelyWeaklyNormal_iff_isIso_absoluteWeakNormalizationMap (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔ IsIso ((⊥_ (AbsoluteWeakNormalizationOver X)).1.hom) := sorry

/-- Lemma 29.47.10 (2): a scheme `X` is absolutely weakly normal if and only if every universal
homeomorphism `Y -> X` with `Y` reduced is an isomorphism. -/
@[stacks 0H3H]
theorem absolutelyWeaklyNormal_iff_universalHomeomorphism_isIso_of_isReduced
    (X : Scheme.{u}) :
    AbsolutelyWeaklyNormal X ↔
      ∀ {Y : Scheme.{u}} (π : Y ⟶ X), UniversalHomeomorphism π → IsReduced Y → IsIso π := sorry

end AlgebraicGeometry.Scheme
