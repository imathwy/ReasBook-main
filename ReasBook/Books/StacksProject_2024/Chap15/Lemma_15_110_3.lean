import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Noetherian.Basic
import StacksProject_2024.Chap05.Definition_5_10_5
import StacksProject_2024.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open TopologicalSpace

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing B] [Module.Flat A B]
variable [IsCatenaryRing B] [EquidimensionalSpace (PrimeSpectrum B)]

/- Domain-style sampling for local dimension theory over `PrimeSpectrum`:
- topological owners from Chapter 5: `EquidimensionalSpace`
- topological catenary owner from Chapter 5 / Chapter 10: `CatenarySpace (PrimeSpectrum A)`,
  with ring-level alias `IsCatenaryRing A`
- fiber-ring owner used throughout Chapter 10: `Ideal.Fiber`
- spectrum/fiber bridge: `PrimeSpectrum.preimageHomeomorphFiber`
- faithfully-flat local-map owner: `Module.FaithfullyFlat.of_flat_of_isLocalHom`
- Noetherian descent owner: `isNoetherianRing_of_faithfullyFlat`

Layer triage:
- `source-facing`: the equidimensionality conclusions for the quotient spectra `Spec (B / pB)` and
  for `Spec A`
- `core/canonical`: `CatenarySpace (PrimeSpectrum A)`, `EquidimensionalSpace`, and `Ideal.Fiber`
- `bridge/view`: the comparison between the source quotient `B ⧸ p.asIdeal.map (algebraMap A B)`
  and the canonical fiber ring `p.asIdeal.Fiber B`, together with the ring-level alias
  `IsCatenaryRing A`

The source statement of part `(1)` is the quotient-spectrum claim `Spec (B / pB)`, so that
quotient must remain the main public theorem surface. The canonical fiber ring `p.asIdeal.Fiber B`
is still the right comparison owner for any auxiliary bridge, but it should not replace the
source-facing quotient statement. Likewise, the catenary conclusion of part `(2)` should live
first on the canonical owner `CatenarySpace (PrimeSpectrum A)`, with `IsCatenaryRing A` retained
only as the source-facing bridge spelling.
-/

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent from the flat local
-- map `A → B` and `[IsNoetherianRing B]`. For a prime `p` of `A`, choose primes of `B` minimal
-- over `pB`. Going down for the flat map `A → B` and the catenary equidimensional hypotheses on
-- `B` identify the dimensions of the corresponding local rings, showing that all irreducible
-- components of the quotient spectrum `Spec (B ⧸ p.asIdeal.map (algebraMap A B))` have the same
-- dimension.
/-- Lemma 15.110.3 (1): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then for every prime ideal `p` of `A` the quotient
spectrum `Spec (B ⧸ p.asIdeal.map (algebraMap A B))`, equivalently `Spec (B / pB)`, is
equidimensional. -/
theorem primeSpectrum_quotient_equidimensional_of_flat_local_of_catenary_equidimensional
    (p : PrimeSpectrum A) :
    EquidimensionalSpace (PrimeSpectrum (B ⧸ p.asIdeal.map (algebraMap A B))) := sorry

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent. Then apply part `(1)`
-- to every quotient `A / p`, use the flat dimension formula to show that `p ↦ dim(A / p)` is a
-- dimension function, and conclude that the local ring `A` is catenary.
/-- Core canonical owner for Lemma 15.110.3 (2): under the flat local hypotheses, the prime
spectrum `Spec A` is catenary. The ring-level conclusion `IsCatenaryRing A` is the thin alias
bridge to this owner theorem. -/
theorem catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional :
    CatenarySpace (PrimeSpectrum A) := sorry

/-- Lemma 15.110.3 (2): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `A` is catenary. -/
theorem isCatenaryRing_of_flat_local_of_catenary_equidimensional :
    IsCatenaryRing A :=
  catenarySpace_primeSpectrum_of_flat_local_of_catenary_equidimensional

-- Proof sketch: first derive `IsNoetherianRing A` by faithful-flat descent. Then compare
-- `dim(A_p)` with `dim(B_q)` for primes `q` minimal over `pB`, deduce that `dim(A) - dim(A / p)`
-- is independent of the choice of a minimal prime of `A`, and conclude that all irreducible
-- components of `Spec A` have the same dimension.
/-- Lemma 15.110.3 (3): for a flat local map `A → B` of local rings, if `B` is Noetherian,
catenary, and `Spec B` is equidimensional, then `Spec A` is equidimensional. -/
theorem primeSpectrum_equidimensional_of_flat_local_of_catenary_equidimensional :
    EquidimensionalSpace (PrimeSpectrum A) := sorry

end
