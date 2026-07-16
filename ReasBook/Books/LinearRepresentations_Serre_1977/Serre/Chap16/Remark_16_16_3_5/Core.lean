import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Serre.Chap15.Exercise_15_15_2_5

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped Representation TensorProduct MonoidAlgebra ZeroObject

universe u

namespace Representation

namespace FDRep

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {G : Type u} [Group G]

/-- A residue-field finite-dimensional representation has an `(R')`-lift for the fraction-field
setting `K/A` if it is obtained, up to equivariant isomorphism, by reducing a stable `A`-lattice
inside a simple finite-dimensional `K[G]`-representation. This is the per-object owner on the
canonical residue-field object `S : FDRep (IsLocalRing.ResidueField A) G` behind Serre's
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

/-- Serre's condition `(R')` for the fraction-field setting `K/A`: every simple finite-dimensional
representation over the residue field `k = IsLocalRing.ResidueField A` is obtained, up to
equivariant isomorphism, by reducing a stable `A`-lattice inside a simple finite-dimensional
`K[G]`-representation. -/
def SatisfiesConditionRPrime : Prop :=
  ∀ S : FDRep k G, Simple S →
    FDRep.HasRPrimeLift S K

end

end Representation
