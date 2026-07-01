import Mathlib
import stacks_project.Chap10.Lemma_10_163_5
import stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

/-
Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of regularity through
  Serre's condition `(R_k)` with geometrically regular fibers;
- sampled owner declarations:
  `IsRegularRingMap`,
  `IsRegularRing`,
  `serreConditionR_of_flat_of_fiber`,
  `IsGeometricallyRegular`;
- best owner abstraction: the source-facing hypothesis is `IsRegularRingMap R S`, while the
  canonical owner for the conclusion is `IsRegularRing S`, built primewise from the owner
  `SerreConditionR`;
- primitive data: the regular-map owner assumption together with the target Noetherianity and the
  source regular-ring owner;
- derived API: `SerreConditionR A k` for a regular ring `A`, and fiber regularity obtained from
  geometric regularity.

Layering:
- `source-facing`: `isRegularRing_of_regularRingMap`;
- `core/canonical`: `IsRegularRing` and `serreConditionR_of_flat_of_fiber`;
- `bridge/view`: `IsGeometricallyRegular`.
-/

private theorem serreConditionR_of_isRegularRing
    {A : Type*} [CommRing A] [IsRegularRing A] (k : ℕ) :
    SerreConditionR A k where
  toIsNoetherian := inferInstance
  isRegularLocalRing_localizationAtPrime p _ := IsRegularRing.isRegularLocalRing_atPrime p

-- Proof sketch: a regular ring map is flat, and each fiber ring is geometrically regular over the
-- corresponding residue field, hence regular. A regular ring satisfies Serre's condition `(R_k)`
-- for every `k`, so Lemma `10.163.5` applied to the flat map `R → S` yields `(R_k)` for `S` for
-- every `k`. The prime-local characterization of regular rings then gives regularity of `S`.
/-- Lemma 15.42.3: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is a regular ring,
then `S` is a regular ring. -/
theorem isRegularRing_of_regularRingMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRingMap R S] [IsNoetherianRing S] [IsRegularRing R] :
    IsRegularRing S := by
  refine
    { toIsNoetherian := inferInstance
      isRegularLocalRing_atPrime := fun p ↦ ?_ }
  let h := p.asIdeal.height
  have hp : h ≠ ⊤ := by
    simpa [h] using Ideal.height_ne_top (Ideal.IsPrime.ne_top inferInstance)
  let k := h.toNat
  let _ : SerreConditionR R k :=
    serreConditionR_of_isRegularRing k
  let _ : SerreConditionR S k :=
    serreConditionR_of_flat_of_fiber (fun q : PrimeSpectrum R ↦ by
      let _ : IsGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber S) :=
        IsRegularRingMap.isGeometricallyRegular_fiber q
      let _ : IsRegularRing (q.asIdeal.Fiber S) :=
        isRegularRing_of_isGeometricallyRegular q.asIdeal.ResidueField (q.asIdeal.Fiber S)
      exact serreConditionR_of_isRegularRing k)
  exact SerreConditionR.isRegularLocalRing_localizationAtPrime p <|
    by
      simp [h, k, ENat.coe_toNat hp]

end Algebra
