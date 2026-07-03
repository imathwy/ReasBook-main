import Mathlib
import StacksProject_2024.Chap10.Definition_10_166_2

open scoped TensorProduct

namespace Algebra

universe u v

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/- Domain-style sampling:
* primary domain: geometric regularity of algebras over a field, detected by regularity of tensor
  base changes along field extensions;
* sampled owner declarations:
  `IsGeometricallyRegular`,
  `isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing`,
  `Algebra.EssFiniteType`,
  `IsPurelyInseparable`;
* best owner abstraction: `IsGeometricallyRegular k A` is the canonical owner for this
  regularity notion; the finitely generated field-extension test in Lemma `10.166.1` is bridge
  data, not a second owner;
* primitive data vs. derived API: the primitive owner data are exactly the regularity statements
  for finite purely inseparable tensor base changes. The finitely generated field-extension test is
  a derived equivalent criterion. No separate `IsNoetherianRing A` hypothesis belongs in the
  public API, since regularity of the displayed tensor base changes already implies it.

Source/core/bridge triage:
* `source-facing`: the equivalence between the finitely generated field-extension test and the
  textbook finite purely inseparable test;
* `core/canonical`: `IsGeometricallyRegular k A`;
* `bridge/view`: the reformulation of Lemma `10.166.1` as an owner-level equivalence.
-/

-- Proof sketch: the reverse implication is immediate because finite purely inseparable extensions
-- are finitely generated. For the forward implication, start with a finitely generated field
-- extension `K / k`. By Lemma `10.45.3`, after a finite purely inseparable extension `K' / K` and
-- a finite purely inseparable extension `k' / k`, the field `K'` becomes separable over `k'`.
-- Lemma `10.158.10` realizes `K'` as the fraction field of a smooth `k'`-algebra `B`. Then
-- `k' ⊗[k] A` is regular by geometric regularity, smooth ascent gives regularity of
-- `B ⊗[k'] (k' ⊗[k] A)`, localization yields regularity of `K' ⊗[k] A`, and faithful flat
-- descent along `K ⊗[k] A → K' ⊗[k] A` gives regularity of `K ⊗[k] A`.
/-- Lemma 10.166.1, canonical owner form: for a `k`-algebra `A`, geometric regularity
over `k` is equivalent to requiring `K ⊗[k] A` to be regular for every finitely generated field
extension `K / k`, recorded canonically by `Algebra.EssFiniteType`; no extra Noetherian
hypothesis is needed in this criterion. -/
theorem isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing
    :
    IsGeometricallyRegular k A ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
        IsRegularRing (K ⊗[k] A) := sorry

/-- Lemma 10.166.1, unpacked source-facing form: for a `k`-algebra `A`, the base
change `K ⊗[k] A` is a regular ring for every finitely generated field extension `K / k` if and
only if it is regular for every finite purely inseparable field extension `K / k`; again, no
separate Noetherian assumption is part of the statement. -/
theorem forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing_iff_forall_finite_purelyInseparable
    :
    (∀ (K : Type (max u v)) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
      IsRegularRing (K ⊗[k] A)) ↔
      (∀ (K : Type (max u v)) [Field K] [Algebra k K] [FiniteDimensional k K]
        [IsPurelyInseparable k K],
        IsRegularRing (K ⊗[k] A)) := by
  rw [
    ← isGeometricallyRegular_iff_forall_essFiniteType_fieldExtension_tensorBaseChange_isRegularRing,
    isGeometricallyRegular_iff_forall_finite_purelyInseparable_tensorBaseChange_isRegularRing
  ]

end

end Algebra
