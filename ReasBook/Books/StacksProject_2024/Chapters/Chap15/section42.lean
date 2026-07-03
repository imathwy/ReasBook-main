import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_42_1 (from Chap15) -/
namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsReduced R]

/- Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of reducedness along flat
  maps with reduced fibers;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `isReduced_of_flat_of_fiber`,
  `RingHom.IsRegularRingMap.isReduced_fiber`,
  `IsReduced`;
- best owner abstraction: the source-facing hypothesis is the actual map owner
  `f.IsRegularRingMap`, with canonical ascent owner `isReduced_of_flat_of_fiber`; reducedness of
  the fibers is derived from the canonical owner theorem
  `RingHom.IsRegularRingMap.isReduced_fiber`.

Source/core/bridge triage:
- `source-facing`: `isReduced_of_regularRingMap`;
- `core/canonical`: `isReduced_of_flat_of_fiber`;
- `bridge/view`: the fiberwise implication chain packaged by
  `RingHom.IsRegularRingMap.isReduced_fiber`.
-/
-- Proof sketch: a regular ring map is flat, and every fiber ring is geometrically regular over the
-- corresponding residue field, hence reduced through the owner-level fiber theorem
-- `RingHom.IsRegularRingMap.isReduced_fiber`.
-- Apply Lemma `10.163.6` to the flat map `R → S`, using the chapter owner lemma
-- `RingHom.IsRegularRingMap.isReduced_fiber` directly to avoid rederiving fiber reducedness
-- locally.
/-- Lemma 15.42.1: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is Noetherian and
reduced, then `S` is reduced. -/
theorem isReduced_of_regularRingMap (f : R →+* S) [f.IsRegularRingMap] : IsReduced S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  exact isReduced_of_flat_of_fiber fun p ↦ hRS.isReduced_fiber p

end

end Algebra

/-! ### Lemma_15_42_2 (from Chap15) -/
namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsNormalRing R]

/-
Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of normality along flat maps
  with normal fibers;
- sampled owner declarations:
  `RingHom.IsRegularRingMap`,
  `isNormalRing_of_flat_of_fiber`,
  `RingHom.IsRegularRingMap.isRegularRing_fiber`,
  `isNormalRing_of_isRegularRing`,
  `IsNormalRing`;
- best owner abstraction: the source-facing hypothesis is a regular ring map
  `f : R →+* S`, while the
  canonical owner theorem for the conclusion is `isNormalRing_of_flat_of_fiber`;
- primitive data: the regular-map owner assumption on `f` and the normal/Noetherian hypotheses on
  `R` and `S`;
- derived API: fiberwise regularity from `RingHom.IsRegularRingMap.isRegularRing_fiber`, then
  fiberwise normality from `isNormalRing_of_isRegularRing`.

Layering:
- `source-facing`: `isNormalRing_of_regularRingMap`;
- `core/canonical`: `isNormalRing_of_flat_of_fiber`;
- `bridge/view`: the canonical implication chain
  `IsGeometricallyRegular → IsRegularRing → IsNormalRing` on each fiber.
-/

-- Proof sketch: a regular ring map `f : R →+* S` is flat, and each fiber ring is geometrically
-- regular over the
-- corresponding residue field, hence regular and therefore normal in the Noetherian case. Apply
-- `isNormalRing_of_flat_of_fiber` to the flat map `f`, using the algebra-side fiber
-- regularity theorem induced by `IsRegularRingMap`.
/-- Lemma 15.42.2: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is Noetherian and
normal, then `S` is normal. -/
theorem isNormalRing_of_regularRingMap
    (f : R →+* S) [f.IsRegularRingMap] : IsNormalRing S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  refine isNormalRing_of_flat_of_fiber fun p ↦ by
    let _ : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
    exact show IsNormalRing (p.asIdeal.Fiber S) from isNormalRing_of_isRegularRing

end

end Algebra

/-! ### Lemma_15_42_3 (from Chap15) -/
namespace Algebra

universe u v

/-
Domain triage:
- primary domain: commutative algebra of regular ring maps and ascent of regularity through
  LinearRepresentations_Serre_1977's condition `(R_k)` with geometrically regular fibers;
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
-- corresponding residue field, hence regular. A regular ring satisfies LinearRepresentations_Serre_1977's condition `(R_k)`
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

/-! ### Lemma_15_42_4 (from Chap15) -/
namespace Algebra

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
- primary domain: ascent of Cohen-Macaulayness along regular ring maps in commutative algebra;
- sampled owner declarations of the same kind:
  `CohenMacaulayRing`,
  `CohenMacaulayRing.serreConditionS`,
  `Module.LocallyCohenMacaulay`,
  `IsRegularRingMap`,
  `serreConditionS_of_flat_of_fiber`;
- best owner abstraction: `CohenMacaulayRing` for the target ring property, with
  `RingHom.IsRegularRingMap f` on the actual ring map `f : R →+* S` supplying the canonical
  fiberwise regularity input,
  `CohenMacaulayRing.serreConditionS` supplying the source and fiber `(S_k)` input, and
  `SerreConditionS` providing the derived ascent route from the proof sketch;
- primitive data: the ring map `f : R →+* S`, the owner assumptions `[f.IsRegularRingMap]`,
  `[CohenMacaulayRing R]`, and `[IsNoetherianRing S]`;
- derived API: the induced algebra structure on `S`, the flatness instance, and the resulting
  canonical conclusion `CohenMacaulayRing S`.

Layering:
- `cohenMacaulayRing_of_regularRingMap` is `source-facing`;
- the core/canonical owners are `CohenMacaulayRing` and `IsRegularRingMap`;
- the LinearRepresentations_Serre_1977-condition ascent argument is a `bridge/view`, not a new public owner.
-/
-- Proof sketch: for Noetherian rings, being Cohen-Macaulay is equivalent to satisfying LinearRepresentations_Serre_1977's
-- condition `(S_k)` for every `k`. A regular ring map is flat and its fibers are geometrically
-- regular, hence regular and therefore Cohen-Macaulay; therefore each fiber satisfies every
-- `(S_k)`. Apply Lemma
-- `10.163.4` for each `k` to ascend the LinearRepresentations_Serre_1977 conditions from `R` to `S`.
/-- Lemma 15.42.4: if `R → S` is a regular ring map, `S` is Noetherian, and `R` is
Cohen-Macaulay, then `S` is Cohen-Macaulay. -/
theorem cohenMacaulayRing_of_regularRingMap
    (f : R →+* S) [f.IsRegularRingMap] [CohenMacaulayRing R] [IsNoetherianRing S] :
    CohenMacaulayRing S := by
  let _ : Algebra R S := f.toAlgebra
  let hRS : f.IsRegularRingMap := inferInstance
  letI : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hRS.toFlat
  refine CohenMacaulayRing.of_serreConditionS S fun k ↦ ?_
  let _ : SerreConditionS R k := CohenMacaulayRing.serreConditionS R k
  refine serreConditionS_of_flat_of_fiber fun p : PrimeSpectrum R ↦ ?_
  let _ : IsRegularRing (p.asIdeal.Fiber S) := hRS.isRegularRing_fiber p
  exact CohenMacaulayRing.serreConditionS (p.asIdeal.Fiber S) k

end

end Algebra
