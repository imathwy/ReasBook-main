import Mathlib
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

namespace Representation

namespace FDRep

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]

/-- A residue-field finite-dimensional representation has an `(R')`-lift for the fraction-field
setting `K/A` if it is obtained, up to equivariant isomorphism, by reducing a stable `A`-lattice
inside a simple finite-dimensional `K[G]`-representation. This is the per-object owner on the
canonical residue-field object `S : FDRep (IsLocalRing.ResidueField A) G` behind LinearRepresentations_Serre_1977's
condition `(R')`. -/
def HasRPrimeLift (S : FDRep (IsLocalRing.ResidueField A) G)
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] : Prop :=
  ∃ X : FDRep K G, Simple X ∧
    ∃ L : StableLattice A X.ρ, Nonempty (FDRep.of L.reductionRepresentation ≅ S)

end FDRep

section

variable (A : Type u) [CommRing A] [IsLocalRing A]
variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
variable (G : Type u) [Group G]

local notation "k" => IsLocalRing.ResidueField A

/- Domain-style sampling for this item:
* primary domain: modular lifting of simple residue-field representations through stable lattices
  inside simple finite-dimensional fraction-field representations;
* relevant owner declarations inspected before refining:
  `StableLattice.reductionRepresentation`,
  `Representation.exists_stableLattice`,
  `decompositionHom_finiteRepClass_eq`;
* best owner abstraction here is the per-object predicate `FDRep.HasRPrimeLift` on the canonical
  owner `S : FDRep k G`, with the global condition `(R')` obtained by quantifying over simple
  objects;
* source/core/bridge triage:
  source-facing: LinearRepresentations_Serre_1977's condition `(R')` for the fixed fraction-field setting `K/A`;
  core/canonical: the owner `FDRep.HasRPrimeLift` on residue-field objects together with the
  fraction-field owner `FDRep` for lifts;
  bridge/view: the canonical reduction `FDRep.of L.reductionRepresentation`.

Primitive data vs derived API:
* primitive data: a simple finite-dimensional `K[G]`-representation and a stable lattice in it;
* derived API: the bundled reduction `FDRep.of L.reductionRepresentation` and the global
  quantification forming `SatisfiesConditionRPrime`.
-/

/-- LinearRepresentations_Serre_1977's condition `(R')` for the fraction-field setting `K/A`: every simple finite-dimensional
representation over the residue field `k = IsLocalRing.ResidueField A` is obtained, up to
equivariant isomorphism, by reducing a stable `A`-lattice inside a simple finite-dimensional
`K[G]`-representation. -/
def SatisfiesConditionRPrime : Prop :=
  ∀ S : FDRep k G, Simple S →
    FDRep.HasRPrimeLift S K

-- Proof sketch: under LinearRepresentations_Serre_1977's sufficiently-large-field hypothesis, the decomposition map is
-- surjective on simple modular classes; realize a chosen lift by a stable `A`-lattice in a
-- finite-dimensional `K[G]`-module, and use the standard rigidity of simple reductions to arrange
-- the lifted representation to be irreducible.
/-- Remark 16-16.3-5: if `K` is sufficiently large, then the fraction-field setting `K/A`
satisfies LinearRepresentations_Serre_1977's condition `(R')`. Equivalently, every simple `k[G]`-module is the reduction
modulo the maximal ideal of a stable lattice in an irreducible finite-dimensional
`K[G]`-representation. -/
theorem satisfiesConditionRPrime_of_sufficiently_large
    [Finite G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    SatisfiesConditionRPrime A K G := sorry

end

end Representation
