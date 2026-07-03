import Mathlib
import stacks_project.Chap15.Definition_15_50_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/- Domain-style sampling:
* primary domain: regular ring maps, `G`-rings, and adic completions in commutative algebra;
* sampled owner declarations of the same kind:
  `IsGRing`,
  `CompletedLocalizationAtPrime`,
  `IsRegularRingMap`,
  `isRegularRingMap_local_tfae`;
* best owner abstraction: the numbered item is a `bridge/view` recall, with `IsGRing` and
  `IsRegularRingMap` as the core/canonical owners;
* bridge/view: localization of `A → AdicCompletion I A` at maximal ideals of the completion,
  compared with the canonical completion maps already packaged by `IsGRing`.

Primitive data are only the ring `A`, the ideal `I`, and the owner hypothesis `[IsGRing A]`. The
maximal-ideal localization/completion comparisons are derived implementation detail and should not
be promoted to a separate public wrapper. The canonical owner-level bridge is the instance
`(algebraMap A (AdicCompletion I A)).IsRegularRingMap`, so the numbered item should be a direct
recall of that bridge rather than a second exact-interface theorem.
-/
-- Proof sketch: use the local criterion `isRegularRingMap_local_tfae` for the map
-- `A → AdicCompletion I A`. For a maximal ideal `m'` of `AdicCompletion I A` lying over
-- `m ⊂ A`, compare the localized map `A_m → (AdicCompletion I A)_(m')` with the canonical
-- completion map `A_m → CompletedLocalizationAtPrime m`. The latter is exactly the owner field
-- `IsGRing.regular_localization_completion m`, and the faithfully flat comparison from
-- `(AdicCompletion I A)_(m')` to its maximal-ideal completion lets one descend regularity back to
-- `A_m → (AdicCompletion I A)_(m')`.
/-- The canonical owner-level bridge: the `I`-adic completion map of a `G`-ring is regular. -/
instance [IsGRing A] : (algebraMap A (AdicCompletion I A)).IsRegularRingMap := by
  sorry

variable [IsGRing A]

/- Lemma 15.50.14: if `A` is a `G`-ring and `A^∧` is the `I`-adic completion of `A`, then the
canonical map `A → A^∧` is regular. This is the canonical instance above. -/
#check (inferInstance : (algebraMap A (AdicCompletion I A)).IsRegularRingMap)

end

end Algebra
