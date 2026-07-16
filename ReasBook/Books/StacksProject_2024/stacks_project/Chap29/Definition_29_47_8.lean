import Mathlib
import StacksProject_2024.stacks_project.Chap29.Lemma_29_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

variable (X : Scheme.{u})

/- Definition 29.47.8: for a scheme `X`, the morphism `X^{sn} ⟶ X` constructed in
Lemma 29.47.7 is the seminormalization of `X`, and the morphism `X^{awn} ⟶ X` constructed there
is the absolute weak normalization of `X`.

Semantic recall: `lean_leansearch` recalled the canonical `HasInitial`/`initial.to`
initial-object API. Local Chapter 29 precedent already constructs the relevant initial
over-category objects in Lemma 29.47.7, so this definition is recorded as a recall of those
constructed morphisms rather than as new data. Axiom checking of a local abbreviation for either
map would depend on `sorryAx` through the statement-stage `HasInitial` proof from Lemma 29.47.7.
The Stacks tag evidence is consistent: item tag `0EUT` agrees with the source URL ending in
`/tag/0EUT`.
-/

#check ((⊥_ (SeminormalizationOver X)).1.hom :
    (⊥_ (SeminormalizationOver X)).1.left ⟶ X)

#check ((⊥_ (AbsoluteWeakNormalizationOver X)).1.hom :
    (⊥_ (AbsoluteWeakNormalizationOver X)).1.left ⟶ X)

end

end AlgebraicGeometry.Scheme
