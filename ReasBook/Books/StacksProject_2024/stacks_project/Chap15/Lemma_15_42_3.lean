import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_163_5
import StacksProject_2024.stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [(algebraMap R S).IsRegularRingMap] [IsNoetherianRing S] [IsRegularRing R]

/-
Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of regularity through
  Serre's condition `(R_k)` with regular fibers;
- sampled owner declarations:
  `IsRegularRingMap`,
  `IsRegularRing`,
  `serreConditionR_of_flat_of_fiber`,
  `RingHom.IsRegularRingMap.isRegularRing_fiber`;
- best owner abstraction: the source-facing hypothesis is `IsRegularRingMap R S`, while the
  canonical owner for the conclusion is `IsRegularRing S`, built primewise from the owner
  `SerreConditionR`;
- primitive data: the regular-map owner assumption together with the target Noetherianity and the
  source regular-ring owner;
- derived API: `SerreConditionR A k` for a regular ring `A`, and the canonical fiber regularity
  theorem `RingHom.IsRegularRingMap.isRegularRing_fiber`.

Layering:
- `source-facing`: `isRegularRing_of_regularRingMap`;
- `core/canonical`: `IsRegularRing` and `serreConditionR_of_flat_of_fiber`;
- `bridge/view`: `IsGeometricallyRegular`.
-/

-- Proof sketch: a regular ring map is flat, and each fiber ring is geometrically regular over the
-- corresponding residue field, hence regular. A regular ring satisfies Serre's condition `(R_k)`
-- for every `k`, so Lemma `10.163.5` applied to the flat map `R → S` yields `(R_k)` for `S` for
-- every `k`. The prime-local characterization of regular rings then gives regularity of `S`.
/-- Lemma 15.42.3: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is a regular ring,
then `S` is a regular ring. -/
theorem isRegularRing_of_regularRingMap (R : Type u) [CommRing R]
    {S : Type v} [CommRing S] [Algebra R S] [(algebraMap R S).IsRegularRingMap]
    [IsNoetherianRing S] [IsRegularRing R] : IsRegularRing S := by
  let hRS : (algebraMap R S).IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  refine ⟨fun p ↦ ?_⟩
  let I := p.asIdeal
  have hp : I.height ≠ ⊤ := by
    exact Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  let k := I.height.toNat
  have hk : I.primeHeight ≤ k := by
    simpa [Ideal.height_eq_primeHeight, k] using (ENat.coe_toNat hp).symm.le
  letI : SerreConditionR R k := IsRegularRing.serreConditionR k
  letI : SerreConditionR S k :=
    let _ : Algebra R S := (algebraMap R S).toAlgebra
    serreConditionR_of_flat_of_fiber fun q ↦ by
      letI : IsRegularRing (q.asIdeal.Fiber S) := hRS.isRegularRing_fiber q
      change SerreConditionR (q.asIdeal.Fiber S) k
      exact IsRegularRing.serreConditionR k
  exact SerreConditionR.isRegularLocalRing_localizationAtPrime p hk

end

end Algebra
