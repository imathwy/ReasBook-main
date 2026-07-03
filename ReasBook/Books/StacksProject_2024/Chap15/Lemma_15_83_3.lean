import Mathlib
import StacksProject_2024.Chap15.Definition_15_83_1
import StacksProject_2024.Chap15.Lemma_15_82_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

section

variable {R : Type u} {A : Type u} [CommRing R] [IsNoetherianRing R]
variable [CommRing A] [Algebra R A] [Algebra.FiniteType R A]

/- Domain-style sampling for Lemma 15.83.3:
- primary domain: pseudo-coherent ring maps and relative pseudo-coherent modules over finite type
  algebras above a Noetherian base;
- sampled owner declarations:
  `RingHom.IsPseudoCoherentRingMap`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `Module.IsPseudoCoherentRelativeTo`,
  `Module.isPseudoCoherentRelativeTo_iff_finite`;
- best owner abstraction: `RingHom.IsPseudoCoherentRingMap` on the structure map `algebraMap R A`;
- primitive vs. derived:
  primitive data are the finite type map `R → A` and the owner field
  `(ModuleCat.of A A).IsPseudoCoherentRelativeTo R`;
  the derived API is the Noetherian finite-type criterion
  `Module.isPseudoCoherentRelativeTo_iff_finite`, specialized to the regular module `A`;
- source/core/bridge triage:
  `source-facing`: the numbered lemma asserting the Noetherian finite-type criterion;
  `core/canonical`: `RingHom.IsPseudoCoherentRingMap` and
    `Module.IsPseudoCoherentRelativeTo`;
  `bridge/view`: the bundled/unbundled module identification for `A` viewed as an `A`-module.
-/
/-- Lemma 15.83.3: a finite type ring map out of a Noetherian ring is pseudo-coherent. -/
instance isPseudoCoherentRingMap_of_finiteType_of_isNoetherianRing :
    (algebraMap R A).IsPseudoCoherentRingMap where
  finiteType := RingHom.finiteType_algebraMap.mpr inferInstance
  isPseudoCoherentRelativeTo := by
    have hfiniteType : (algebraMap R A).FiniteType :=
      RingHom.finiteType_algebraMap.mpr inferInstance
    let _ : Algebra R A := (algebraMap R A).toAlgebra
    let _ : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp hfiniteType
    simpa [Module.IsPseudoCoherentRelativeTo] using
      (Module.isPseudoCoherentRelativeTo_iff_finite : Module.IsPseudoCoherentRelativeTo R A A ↔
        Module.Finite A A).2 (Module.Finite.self A)

end

end Algebra
