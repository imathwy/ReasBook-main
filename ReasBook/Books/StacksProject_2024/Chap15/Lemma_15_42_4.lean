import Mathlib
import StacksProject_2024.Chap10.Definition_10_104_6
import StacksProject_2024.Chap10.Lemma_10_163_4
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

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
