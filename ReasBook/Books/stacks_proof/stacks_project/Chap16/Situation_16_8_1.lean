import Mathlib
import StacksProject_2024.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

section

variable {R : Type u} {Λ : Type v}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]
variable [IsNoetherianRing R] [IsNoetherianRing Λ] [(algebraMap R Λ).IsRegularRingMap]

/- Domain triage:
- primary domain: regular ring maps of Noetherian commutative rings;
- sampled owner declarations of the same kind:
  `RingHom.IsRegularRingMap`,
  `IsGeometricallyRegular`,
  `RingHom.IsRegularRingMap.baseChange_of_essFiniteType`,
  `RingHom.IsRegularRingMap.comp_of_noetherianFibers`;
- best owner abstraction: `(algebraMap R Λ).IsRegularRingMap` is the canonical owner for the
  regularity of the algebra map `R → Λ`;
- primitive data: the rings `R`, `Λ`, the algebra structure `R → Λ`, and the Noetherian
  assumptions on both rings;
- derived API: flatness and fiberwise geometric regularity come from the owner instance
  `[(algebraMap R Λ).IsRegularRingMap]`.

Source/core/bridge triage:
- `source-facing`: Situation 16.8.1 fixes a regular map `R → Λ` with `R` and `Λ` Noetherian;
- `core/canonical`: `[(algebraMap R Λ).IsRegularRingMap]`, `[IsNoetherianRing R]`, and
  `[IsNoetherianRing Λ]`;
- `bridge/view`: the flatness and fiberwise geometric-regularity consequences derived from
  `IsRegularRingMap`.

Since the source item only fixes ambient assumptions and adds no new mathematical data, the
correct refinement is direct checking of the canonical ambient instances rather than a packaged
wrapper.
-/

/- Situation 16.8.1: the algebra map `R → Λ` is a regular ring map. -/
#check (inferInstance : (algebraMap R Λ).IsRegularRingMap)

/- Situation 16.8.1 also assumes the source ring `R` is Noetherian. -/
#check (inferInstance : IsNoetherianRing R)

/- Situation 16.8.1 also assumes the target ring `Λ` is Noetherian. -/
#check (inferInstance : IsNoetherianRing Λ)

end

end Algebra
