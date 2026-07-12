import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PointwiseReadbackDirectProofWorker

/-!
Audit for the coordinate-normalized Brauer-basis pointwise congruence.

The coordinate normalization of `regularClassCoordinateAddEquiv` already supplies the
simple-family bookkeeping (`PairwiseNonisomorphic` and completeness).  The remaining local
statement is exactly the fixed-coordinate Brauer-basis readback divisibility, equivalently the
direct row-value congruence for
`FDRep.modularCharacterOnPRegularConjClass (π c) primeToPRoot_canonicalLift`.

No Cartan cokernel/product/range endpoint is used here.
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section BrauerBasisCoordinateDefinitionAuditWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local notation "k" => IsLocalRing.ResidueField A

local instance brauerBasisCoordinateDefinitionAuditWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance brauerBasisCoordinateDefinitionAuditWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [HenselianLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- The coordinate-normalized hypotheses already provide the simple-family structure needed to
open `canonicalDVRBrauerBasis`.  Thus the missing pointwise congruence is not a
pairwise/completeness transport issue. -/
theorem coordinateNormalized_provides_pairwise_and_complete
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  exact
    ⟨pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_coord,
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (G := G) (π := π) hπ_simple hπ_coord⟩

/-- For a coordinate-normalized family, the requested direct Brauer-character pointwise
congruence is exactly the existing fixed-coordinate readback divisibility statement.  This is the
definition-level gap: proving either side proves the other, but `hπ_coord` alone is not unfolded by
the current API into this readback theorem. -/
theorem fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord) ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (G := G) (π := π) hπ_simple hπ_coord
  have hfixed :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
        brauerBasisFixedCoordinateReadbackDivisibility
          (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete :=
    coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_fixedCoordinateReadback
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  have hdirect :
      coordinateNormalizedBrauerBasisPointwiseReadbackSource
          (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
        brauerCharacterPointwiseReadbackCongruence
          (p := p) (A := A) (G := G) π :=
    coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π hπ_simple hπ_coord
  change
    brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G) π hπ_pairwise hπ_complete ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π
  exact hfixed.symm.trans hdirect

/-- If the fixed-coordinate readback divisibility is supplied, the desired local theorem follows
formally.  This is the smallest non-circular replacement for the attempted proof from
`hπ_coord` alone. -/
theorem brauerCharacterPointwiseReadbackCongruence_of_coordinateNormalized_fixedCoordinateReadback
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hread :
      brauerBasisFixedCoordinateReadbackDivisibility
        (p := p) (A := A) (G := G)
        π
        (pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_coord)
        (complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (G := G) (π := π) hπ_simple hπ_coord)) :
    brauerCharacterPointwiseReadbackCongruence
      (p := p) (A := A) (G := G) π :=
  (fixedCoordinateReadbackDivisibility_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord).1 hread

/-- Equivalently, the desired theorem for this fixed family is exactly the canonical-basis
pointwise readback source after unfolding `canonicalDVRBrauerBasis`; this records that the
notation transport to Brauer-character rows is already present. -/
theorem pointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (G := G) ([π c]₀ : R₀[k](G)) =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    coordinateNormalizedBrauerBasisPointwiseReadbackSource
        (p := p) (A := A) (G := G) π hπ_simple hπ_coord ↔
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π :=
  coordinateNormalizedBrauerBasisPointwiseReadbackSource_iff_brauerCharacterPointwiseReadbackCongruence
    (p := p) (A := A) (G := G) π hπ_simple hπ_coord

/-- Auditing consequence of the direct pointwise readback congruence at the identity
`p`-regular class.  The blocker forces the Brauer-character value at the identity, hence the
dimension of each chosen simple module, to match the chosen coordinate point mass modulo the
`p`-part of the centralizer of `1`. -/
theorem brauerCharacterPointwiseReadbackCongruence_identityColumn_finrank
    (π : PRegularConjClass G p → FDRep k G)
    (hapi :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π)
    (c : PRegularConjClass G p) :
    ∃ a : A,
      (Module.finrank k (π c).V : A) -
          ((Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)
            (PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩) : A) =
        (centralizerPPart p (1 : G) : A) * a := by
  classical
  let oneClass : PRegularConjClass G p :=
    PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩
  rcases hapi c oneClass with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  have hvalue :
      FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := A) (π c)
          (primeToPRoot_canonicalLift (p := p) (A := A)) oneClass =
        (Module.finrank k (π c).V : A) := by
    rw [show oneClass =
        PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩ from rfl]
    rw [FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
    convert
      (modularCharacter_one_eq_finrank
        (p := p)
        (lift := (Units.coeHom A).comp (primeToPRoot_unitsLift (p := p) (A := A)))
        (ρ := (π c).ρ)) using 1
  simpa [oneClass, hvalue, ConjClasses.centralizerPPart_mk] using ha

/-- Off the identity coordinate, the same identity-column consequence says that the dimension of
the chosen simple module is divisible by the centralizer `p`-part of `1`.  This is a useful
sanity check on any proposed non-circular proof of the current blocker. -/
theorem brauerCharacterPointwiseReadbackCongruence_identityColumn_offCoordinate_finrank
    (π : PRegularConjClass G p → FDRep k G)
    (hapi :
      brauerCharacterPointwiseReadbackCongruence
        (p := p) (A := A) (G := G) π)
    {c : PRegularConjClass G p}
    (hc :
      PRegularConjClass.ofSubtype (G := G) p ⟨1, isPRegular_one p⟩ ≠ c) :
    ∃ a : A,
      (Module.finrank k (π c).V : A) =
        (centralizerPPart p (1 : G) : A) * a := by
  rcases
      brauerCharacterPointwiseReadbackCongruence_identityColumn_finrank
        (p := p) (A := A) (G := G) π hapi c with
    ⟨a, ha⟩
  refine ⟨a, ?_⟩
  simpa [Pi.single_apply, hc] using ha

end BrauerBasisCoordinateDefinitionAuditWorker

end Representation
