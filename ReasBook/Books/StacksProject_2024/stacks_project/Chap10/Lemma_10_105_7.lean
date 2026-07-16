import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_105_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/-
Domain-style sampling in the catenary API:
- topological owner: `CatenarySpace (PrimeSpectrum R)` from `Chap05/Definition_5_11_4`
- ring owner: `IsCatenaryRing R` from `Lemma_10_105_2`
- universal owner: `UniversallyCatenaryRing R` from `Definition_10_105_3`
- layer here: `bridge/view`, since this item records quotient stability of the existing owners

Primitive data already belongs to the owner abstractions from `Lemma_10_105_2` and
`Definition_10_105_3`; this file should only expose the quotient instances.
-/

/-- Lemma 10.105.7 (1): any quotient of a catenary ring is catenary. -/
-- Proof sketch: by Lemma 10.17.7, `Spec (R ⧸ I)` is homeomorphic to the closed subset `V(I)` of
-- `Spec R`; closed subspaces of catenary spaces are catenary, so the quotient ring is catenary.
instance quotient_catenaryRing [IsCatenaryRing R] : IsCatenaryRing (R ⧸ I) := sorry

/-- Lemma 10.105.7 (2): any quotient of a Noetherian universally catenary ring is universally
catenary. -/
-- Proof sketch: the quotient `R ⧸ I` is a finite type `R`-algebra via the quotient map. Any
-- finite type algebra over `R ⧸ I` is also a finite type algebra over `R`, so the universal
-- catenarity hypothesis on `R` gives catenarity after composing the algebra structures.
instance quotient_universallyCatenaryRing [UniversallyCatenaryRing.{u, v} R] :
    UniversallyCatenaryRing.{u, v} (R ⧸ I) := by
  refine { catenary_of_finiteType := ?_ }
  intro A _ _ _
  let f : R →+* A := (algebraMap (R ⧸ I) A).comp (Ideal.Quotient.mk I)
  letI : Algebra R A := RingHom.toAlgebra f
  letI : IsScalarTower R (R ⧸ I) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  have hfinite : Algebra.FiniteType R A :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R (R ⧸ I)) inferInstance
  exact (inferInstance : UniversallyCatenaryRing R).catenary_of_finiteType

end
