import Mathlib
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace RingHom.IsRegularRingMap

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/- Domain triage:
- primary domain: regular ring maps and composition through fiberwise geometric regularity in
  commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularRingMap`,
  `IsGeometricallyRegular`,
  `baseChange_of_essFiniteType`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`;
- best owner abstraction: `IsRegularRingMap` on composable ring homomorphisms
  `f : A →+* B` and `g : B →+* C`, with `IsGeometricallyRegular` supplying the canonical owner on
  each fiber over a residue field;
- primitive data: the ring homs `f` and `g`, regularity of `f` and `g`, and the Noetherianity
  hypothesis on the fibers `p.asIdeal.Fiber C` of the composite `g.comp f`;
- derived API: field-valued base change of regular maps and the local regularity criterion for flat
  local maps with regular closed fiber.

Layering:
- `comp_of_noetherianFibers` is `source-facing`;
- the core/canonical owners are `IsRegularRingMap` and `IsGeometricallyRegular`;
- the Noetherian-fiber hypothesis is auxiliary input, not a new owner-level wrapper.
-/

-- Proof sketch: for each prime `p : PrimeSpectrum A` and each finite purely inseparable extension
-- `κ(p) ⊂ k`, base change along `A → k` using
-- `baseChange_of_essFiniteType` to reduce to the case where the
-- source is the field `k`. Then `k ⊗[A] B` is regular because `A → B` is regular, and
-- `k ⊗[A] C` is Noetherian by the fiber hypothesis. The induced map `k ⊗[A] B → k ⊗[A] C` is
-- regular because `B → C` is regular, so Lemma `10.112.8` upgrades regularity of the source and
-- of the fibers to regularity of `k ⊗[A] C`, which is exactly the geometric regularity needed for
-- `A → C`.
/-- Lemma 15.41.4 (Composition of regular maps): let `f : A →+* B` and `g : B →+* C` be regular
ring maps. If every fiber ring `p.asIdeal.Fiber C = C ⊗[A] κ(p)` of `g.comp f : A →+* C` is
Noetherian, then `g.comp f` is a regular ring map. -/
theorem comp_of_noetherianFibers (hf : f.IsRegularRingMap) (hg : g.IsRegularRingMap)
    (hfiber_noetherian :
      let _ : Algebra A C := (g.comp f).toAlgebra
      ∀ p : PrimeSpectrum A, IsNoetherianRing (p.asIdeal.Fiber C)) :
    (g.comp f).IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  sorry

end

end RingHom.IsRegularRingMap
