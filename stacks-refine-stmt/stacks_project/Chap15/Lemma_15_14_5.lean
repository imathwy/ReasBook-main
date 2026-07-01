import stacks_project.Chap15.Lemma_15_14_3
import stacks_project.Chap15.Lemma_15_14_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open scoped nonZeroDivisors

variable (A : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

/-
Domain-style sampling for Lemma 15.14.5:
- primary domain: commutative algebra of absolutely integrally closed domains, fraction fields,
  and integrally closedness;
- sampled owner-level declarations:
  `IsAbsolutelyIntegrallyClosed`,
  `IsAlgClosed`,
  `IsIntegrallyClosed`,
  `isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization`;
- best owner abstraction: the theorem is `source-facing`, but its proof should pass through the
  canonical owners `IsAbsolutelyIntegrallyClosed`, `IsAlgClosed`, and `IsIntegrallyClosed`, with
  the fraction field viewed through the canonical localization owner `Localization A⁰`;
- primitive data: the normal-domain hypothesis `[IsIntegrallyClosed A]`, which already means
  `IsIntegrallyClosedIn A (FractionRing A)`, and the fraction-field localization `Localization A⁰`;
- derived API: root-existence and splitting consequences from
  `IsAbsolutelyIntegrallyClosed.exists_root` and the field instance
  `IsAbsolutelyIntegrallyClosed (Localization A⁰)` induced by algebraic closedness.

Source/core/bridge triage:
- `source-facing`: the iff statement comparing absolute integral closedness of `A` with algebraic
  closedness of its fraction field;
- `core/canonical`: `IsAbsolutelyIntegrallyClosed`, `IsAlgClosed`, `IsIntegrallyClosed`;
- `bridge/view`: the identification `FractionRing A = Localization A⁰`, which lets the backward
  implication reuse Lemma `15.14.4` directly instead of introducing a parallel fraction-field
  descent wrapper.
-/

-- Proof sketch: for `→`, apply Lemma `15.14.3` to the fraction field, which is a localization of
-- `A`, and use that an absolutely integrally closed field is algebraically closed. For `←`, an
-- algebraically closed fraction field is absolutely integrally closed as a ring, and then
-- Lemma `15.14.4` descends splitting of monic polynomials from the fraction field back to `A`
-- using integrally closedness of the normal domain `A`.
/-- Lemma 15.14.5: for a normal domain `A`, the ring `A` is absolutely integrally closed if and
only if its fraction field is algebraically closed. -/
theorem isAbsolutelyIntegrallyClosed_iff_isAlgClosed_fractionRing :
    IsAbsolutelyIntegrallyClosed A ↔ IsAlgClosed (FractionRing A) := by
  constructor
  · intro hA
    letI : IsAbsolutelyIntegrallyClosed A := hA
    change IsAlgClosed (Localization A⁰)
    letI : IsAbsolutelyIntegrallyClosed (Localization A⁰) := inferInstance
    exact IsAbsolutelyIntegrallyClosed.isAlgClosed
  · intro hFrac
    change IsAlgClosed (Localization A⁰) at hFrac
    letI : IsAlgClosed (Localization A⁰) := hFrac
    exact isAbsolutelyIntegrallyClosed_of_isIntegrallyClosedIn_localization A⁰

end
