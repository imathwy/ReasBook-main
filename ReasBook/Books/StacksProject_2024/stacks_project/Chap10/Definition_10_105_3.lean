import Mathlib
import StacksProject_2024.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace X`
- ring-level owner: `IsCatenaryRing A`
- bridge/view: `isCatenaryRing_iff_catenarySpace_primeSpectrum`

Layer triage:
- `source-facing`: Definition 10.105.3 introduces universal catenarity
- `core/canonical`: finite type algebras should be recorded as catenary rings via
  `IsCatenaryRing`
- `bridge/view`: catenary prime spectra are derived from the owner instance in
  `Lemma_10_105_2`

Primitive data belongs to the ring-level owner `IsCatenaryRing`; the `Spec` formulation is
derived API.
-/

/-- Definition 10.105.3: a Noetherian ring is universally catenary if every finite type
`R`-algebra is catenary. -/
class UniversallyCatenaryRing : Prop extends IsNoetherianRing R where
  catenary_of_finiteType {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    IsCatenaryRing A

/-- A universally catenary ring is catenary via the identity finite type algebra. -/
instance instIsCatenaryRingOfUniversallyCatenaryRing [UniversallyCatenaryRing.{u, u} R] :
    IsCatenaryRing R :=
  (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

end
