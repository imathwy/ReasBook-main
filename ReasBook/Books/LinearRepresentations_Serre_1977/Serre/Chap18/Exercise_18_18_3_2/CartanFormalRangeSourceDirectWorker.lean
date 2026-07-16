import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.Serre18_5ASupportValueCriterionWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.RegularRestrictionExtensionSourceWorker
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.IntegerDivisibilityDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCoordinateRangeGenerators

/-!
Source-direct audit for the Cartan formal range.

This file deliberately stops before the downstream Cartan cokernel/product endpoints.  The
source-side Serre 18.5(a) API gives the regular-restriction divisibility lattice and, after the
Brauer-coordinate bridge, identifies the Cartan coordinate `A`-span with the image of that
lattice.  The remaining fixed-coordinate statement is isolated below as stability of that
divisibility lattice under the Brauer-coordinate map, plus the integer cast-saturation needed to
descend from the `A`-span to the `ℤ`-lattice.
-/

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section SourceRegularRestriction

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local instance sourceDirectFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceDirectDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Serre 18.5(a) in the exact regular-restriction lattice form used by the Cartan bridge. -/
theorem sourceDirect_projectiveCharacter_regularRestriction_eq_regularValueDivisibility
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s)) :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G) hω

/-- The same source-side lattice statement in the standard large-field regime. -/
theorem sourceDirect_projectiveCharacter_regularRestriction_eq_regularValueDivisibility_of_enoughRoots
    [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Submodule.map
        (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
        (projectiveCharacterSubmodule (A := A) (K := K) (G := G)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    sourceDirect_projectiveCharacter_regularRestriction_eq_regularValueDivisibility
      (p := p) (A := A) (K := K) (G := G) hω

/-- What the existing Serre 18.5(a) source API proves after the `c = d ∘ e`/Brauer-coordinate
bridge: the fixed Cartan-coordinate `A`-span is the Brauer-coordinate image of Serre's
regular-value divisibility lattice. -/
theorem sourceDirect_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    Submodule.map
        (projectiveCartanASpanBrauerRepr
          (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
      Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) :=
  projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

/-- Minimal fixed-coordinate blocker exposed by the source API: after Serre 18.5(a), the
desired `A`-span equality is equivalent to stability of the regular-value divisibility lattice
under the chosen Brauer-coordinate map. -/
theorem sourceDirect_cartanCoordinate_span_eq_regularValueDivisibility_iff_fixedCoordinateStability
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    (Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ↔
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  have hsource :=
    sourceDirect_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  constructor
  · intro hspan
    exact hsource.trans hspan
  · intro hstable
    exact hsource.symm.trans hstable

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Forward `ℤ`-divisibility from a fixed-coordinate `A`-span equality.  This direction is
available by the integer divisibility descent API and does not use a Cartan endpoint. -/
theorem sourceDirect_cartanCoordinate_range_le_regularIntegerDiagonal_of_span_eq
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rintro f ⟨x, rfl⟩
  change
    cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
      regularIntegerDiagonalSubmodule (p := p) (G := G)
  have hcast_span :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) := by
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G)]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hcast_div :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
    rw [← hspan]
    exact hcast_span
  exact
    (regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)).1 hcast_div

end SourceRegularRestriction

section FixedCoordinateFormalRange

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance sourceDirectFixedFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceDirectFixedDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The fixed Cartan-coordinate range is exactly the Cartan range transported by the fixed
regular-class coordinate equivalence. -/
theorem sourceDirect_cartanCoordinateAddHom_range_eq_cartanHom_range_map :
    (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
      (cartanHom k G).range.map
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)).toAddMonoidHom := by
  ext f
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨cartanHom k G x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Fixed-coordinate range equality implies the existential coordinate-equivalence statement
used in `CartanFormalRange.lean`. -/
theorem sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
    (hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    ⟨regularClassCoordinateAddEquiv (p := p) (k := k) (G := G), ?_⟩
  exact
    (sourceDirect_cartanCoordinateAddHom_range_eq_cartanHom_range_map
      (p := p) (k := k) (G := G)).symm.trans hrange

/-- Alternative scaled-indicator blocker: forward divisibility plus one Cartan preimage for each
scaled regular-class indicator is sufficient for the formal range target. -/
theorem sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_range_le_and_scaledIndicators
    (hsubset :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hrange :
      (cartanCoordinateAddHom (p := p) (k := k) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_range_le_and_scaled_mem
      (p := p) (k := k) (G := G) hsubset hscaled
  exact
    sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
      (p := p) (k := k) (G := G) hrange

end FixedCoordinateFormalRange

section ResidueEndpointFromSourceBlockers

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [CharZero K]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p]

local instance sourceDirectResidueFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance sourceDirectResidueDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A] in
/-- Residue-field endpoint from an `A`-span equality plus the remaining integer
cast-saturation descent.  The forward inclusion is supplied above by integer divisibility
descent, so the explicit hypothesis is exactly the reverse `A`-span-to-`ℤ` range descent. -/
theorem sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq_and_castSaturation
    (hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    sourceDirect_cartanCoordinate_range_le_regularIntegerDiagonal_of_span_eq
      (p := p) (A := A) (K := K) (G := G) hspan
  have hrange :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_span_eq_and_saturation
      (p := p) (A := A) (K := K) (G := G) hspan hsubset hsaturated
  exact
    sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_coordinateRange_eq
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) hrange

/-- Full residue-field source-direct conditional: Serre 18.5(a) reaches the final formal range
target once fixed-coordinate stability and integer cast-saturation are supplied. -/
theorem sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_fixedCoordinateStability_and_castSaturation
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hstable :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
    (hsaturated :
      ∀ f : PRegularConjClass G p → ℤ,
        regularIntegerFunctionCast (p := p) (K := K) (G := G) f ∈
            Submodule.span A
              ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
                Set (PRegularConjClass G p → K)) →
          f ∈
            (cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    ∃ e : R₀[IsLocalRing.ResidueField A](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom (IsLocalRing.ResidueField A) G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  have hspan :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    (sourceDirect_cartanCoordinate_span_eq_regularValueDivisibility_iff_fixedCoordinateStability
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 hstable
  exact
    sourceDirect_existsCartanRangeCoordinateEquiv_regularIntegerDiagonal_of_span_eq_and_castSaturation
      (p := p) (A := A) (K := K) (G := G) hspan hsaturated

end ResidueEndpointFromSourceBlockers

end Representation
