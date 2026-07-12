import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanIntegerDescentFromProjectiveCharacterWorker

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanGeneratorSourceProofWorker2

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanGeneratorSourceProofWorker2FintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanGeneratorSourceProofWorker2DecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Local generator-side target left by the projective-character route.

For a coordinate-normalized simple family, this says that the inverse Brauer-coordinate readback
of each scaled integer point mass is already in Serre's regular-value divisibility lattice.  It is
the fixed-generator version of the reverse Brauer-stability obstruction, restricted to the
scaled-indicator generators rather than to the whole lattice. -/
def coordinateNormalizedReverseBrauerScaledIndicatorRegularValue
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) : Prop :=
  ∀ c : PRegularConjClass G p,
    (projectiveCartanASpanBrauerReprLinearEquiv
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).symm
        (regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c)) ∈
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)

/-- The local reverse Brauer scaled-indicator target gives the fixed Cartan generators.

The proof uses Serre `18.5(a)` only through the already-proved projective-character image theorem,
then descends the resulting integer point from the fixed Cartan-coordinate `A`-span back to the
integer Cartan coordinate range. -/
theorem cartan_generators_of_reverseBrauerScaledIndicatorRegularValue
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreverse :
      coordinateNormalizedReverseBrauerScaledIndicatorRegularValue
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord) :
    ∀ c : PRegularConjClass G p,
      ∃ x : P₀[IsLocalRing.ResidueField A](G),
        cartanHom (IsLocalRing.ResidueField A) G x =
          (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀ := by
  intro c
  let E := PRegularConjClass G p → K
  let D : Submodule A E :=
    regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)
  let S : Submodule A E :=
    Submodule.span A
      ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
        Set E)
  let fℤ : PRegularConjClass G p → ℤ :=
    scaled_regular_integer_indicator (p := p) (G := G) c
  let fK : E := regularIntegerFunctionCast (p := p) (K := K) (G := G) fℤ
  let T : E →ₗ[A] E :=
    projectiveCartanASpanBrauerRepr
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  let eT : E ≃ₗ[A] E :=
    projectiveCartanASpanBrauerReprLinearEquiv
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hmap_mem : T (eT.symm fK) ∈ Submodule.map T D := by
    exact ⟨eT.symm fK, by simpa [D, fK, eT] using hreverse c, rfl⟩
  have himage :
      Submodule.map T D = S := by
    simpa [T, D, S] using
      projectiveCharacterDivisibility_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  have hspan : fK ∈ S := by
    have hmemS : T (eT.symm fK) ∈ S := by
      simpa [himage] using hmap_mem
    have hTeq : T (eT.symm fK) = fK := by
      calc
        T (eT.symm fK) = (eT : E →ₗ[A] E) (eT.symm fK) := by
          rw [projectiveCartanASpanBrauerReprLinearEquiv_toLinearMap
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord]
        _ = fK := by simp
    simpa [hTeq] using hmemS
  have hmem_range :
      fℤ ∈
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
    exact
      (regularIntegerFunctionCast_mem_projectiveCartanCoordinate_span_iff_mem_cartanCoordinateAddHom_range
        (p := p) (A := A) (K := K) (G := G) fℤ).1
        (by simpa [S, fK])
  exact
    cartan_generator_of_scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord c
      (by simpa [fℤ] using hmem_range)

end CartanGeneratorSourceProofWorker2

end Representation
