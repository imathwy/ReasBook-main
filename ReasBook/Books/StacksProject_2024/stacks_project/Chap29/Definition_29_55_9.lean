import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_55_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

section

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

-- Semantic recall: `Definition_29_55_8` keeps the source-facing weak-normalization owner while
-- refining it to extend the canonical factorization core of `X.normalizationTo`. The present
-- item therefore states weak normality in terms of the weak-normalization morphism attached to
-- any chosen `WeakNormalization X`.

/-- Definition 29.55.9: a scheme `X` is weakly normal if the weak-normalization morphism
`X^{wn} ⟶ X` is an isomorphism. With the source-facing owner from Definition 29.55.8, this means
that every chosen weak normalization of `X` has an isomorphism to `X`. -/
@[stacks 0H3S]
class WeaklyNormal : Prop where
  /-- Any chosen weak-normalization morphism to `X` is an isomorphism. -/
  isIso_toScheme : ∀ W : WeakNormalization X, IsIso W.toScheme

/-- On a weakly normal scheme, every chosen weak-normalization morphism is an isomorphism. -/
@[stacks 0H3S, instance]
instance instIsIsoToSchemeOfWeaklyNormal [h : WeaklyNormal X] (W : WeakNormalization X) :
    IsIso W.toScheme :=
  h.isIso_toScheme W

/-- Source-facing specification: a weakly normal scheme makes every chosen weak-normalization map
to `X` an isomorphism. -/
@[stacks 0H3S]
theorem weaklyNormal_spec (hX : WeaklyNormal X) :
    ∀ W : WeakNormalization X, IsIso W.toScheme := sorry

/-- Field-level specification: weak normality supplies an isomorphism structure on the morphism
from any chosen weak normalization to `X`. -/
@[stacks 0H3S]
theorem WeaklyNormal.isIso_toScheme.spec (hX : WeaklyNormal X) (W : WeakNormalization X) :
    IsIso W.toScheme := sorry

/-- For a weakly normal scheme, the morphism from any chosen weak normalization to `X` is an
isomorphism. -/
@[stacks 0H3S]
theorem weaklyNormal_isIso_toScheme [WeaklyNormal X] (W : WeakNormalization X) :
    IsIso W.toScheme := sorry

/-- Unfold `WeaklyNormal X` into the condition that each chosen weak-normalization map is an
isomorphism. -/
@[stacks 0H3S]
theorem weaklyNormal_iff :
    WeaklyNormal X ↔ ∀ W : WeakNormalization X, IsIso W.toScheme := sorry

end

end AlgebraicGeometry.Scheme
