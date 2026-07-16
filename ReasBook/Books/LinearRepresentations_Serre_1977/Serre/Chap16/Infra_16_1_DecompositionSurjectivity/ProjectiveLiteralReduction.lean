import LinearRepresentations_Serre_1977.Serre.Chap15.Proposition_15_15_5_1.ProjectiveLiteralReduction

noncomputable section

open CategoryTheory
open scoped MonoidAlgebra Representation TensorProduct

universe u

namespace Representation

section

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]

/-- Helper for Infra 16 1 DecompositionSurjectivity: an honest projective scalar extension carries
the literal stable lattice whose reduction is exactly the intrinsic residue-field reduction of the
original projective module. -/
-- Route correction: this Chap16 helper is a duplicate API shim, so reuse the canonical Chapter 15
-- literal-reduction theorem instead of maintaining a second private proof chain.
theorem projective_scalarExtension_literal_reduction_class
    (Q : FiniteProjectiveGroupAlgebraModule A G) :
    ∃ L : StableLattice A (Q.scalarExtension K).ρ,
      [FDRep.of L.reductionRepresentation]₀ = [Q.residueFieldReduction.toFiniteRep]₀ := by
  -- The Chapter 15 theorem already proves the exact reduction-class statement for the same
  -- literal lattice construction, so this file only preserves the Chap16 theorem name.
  exact
    projective_scalarExtension_literal_reduction_class_support
      (A := A) (K := K) (G := G) Q

end

end Representation
