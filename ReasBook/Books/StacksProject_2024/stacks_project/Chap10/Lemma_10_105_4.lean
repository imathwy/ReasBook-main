import Mathlib
import StacksProject_2024.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R]

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)`
- ring owner: `IsCatenaryRing R`
- universal owner: `UniversallyCatenaryRing R`
- layer here: `bridge/view`, since this item records localization stability of the existing owners

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the localization instances.
-/

/-- Lemma 10.105.4 (1): any localization of a catenary ring is catenary. -/
-- Proof sketch: identify `Spec(Localization M)` with the subspace of `Spec(R)` consisting of
-- primes disjoint from `M`; catenarity is preserved under this localization subspace
-- identification.
instance localization_isCatenaryRing (M : Submonoid R) [IsCatenaryRing R] :
    IsCatenaryRing (Localization M) := sorry

/-- Lemma 10.105.4 (2): any localization of a Noetherian universally catenary ring is
universally catenary. -/
-- Proof sketch: if `A` is a finite type algebra over `Localization M`, then `A` is a localization
-- of some finite type `R`-algebra. Apply universal catenarity over `R` to that finite type
-- algebra, then use the first localization statement.
instance localization_universallyCatenaryRing (M : Submonoid R)
    [UniversallyCatenaryRing R] : UniversallyCatenaryRing (Localization M) := sorry

end
