import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveCharacterDivisibility
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinateRangeGenerators
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularValueIntegerImage

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanIntegerDescentFromProjectiveCharacterWorker

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance cartanIntegerDescentFromProjectiveCharacterWorkerFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanIntegerDescentFromProjectiveCharacterWorkerDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- The direct output of `ProjectiveCharacterDivisibility` after applying the Brauer-coordinate
readback map: it identifies the Brauer-coordinate image of Serre's regular-value divisibility
lattice with the `A`-span of the fixed Cartan-coordinate range.

This is the strongest unconditional statement available from the regular-restriction image
theorem alone; it is `T(D) = S`, not yet `S = D`. -/
theorem projectiveCharacterDivisibility_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
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
          Set (PRegularConjClass G p → K)) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  rw [← projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
    (p := p) (A := A) (K := K) (G := G) hω]
  exact
    projectiveCharacterSubmodule_regularRestriction_brauerRepr_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Forward integer descent from the `A`-span level: if the fixed Cartan-coordinate `A`-span is
contained in Serre's regular-value divisibility lattice, then every integer Cartan coordinate row
lies in the integer diagonal lattice. -/
theorem cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_cartanCoordinate_span_le
    (hspan_le :
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  rintro f ⟨x, rfl⟩
  have hcast_span :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) := by
    rw [regularIntegerFunctionCast_cartanCoordinateAddHom
      (p := p) (A := A) (K := K) (G := G) x]
    exact Submodule.subset_span ⟨x, rfl⟩
  have hcast_regular :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    hspan_le hcast_span
  have hdiag :
      cartanCoordinateAddHom (p := p) (k := IsLocalRing.ResidueField A) (G := G) x ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) :=
    (regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_iff
      (p := p) (A := A) (K := K) (G := G)).1 hcast_regular
  simpa using hdiag

/-- The forward half of Brauer-coordinate stability is enough, together with the
regular-restriction image theorem, to prove the forward integer Cartan range inclusion. -/
theorem cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_projectiveCharacter_image_and_brauer_forward
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hforward :
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) ≤
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_cartanCoordinate_span_le
      (p := p) (A := A) (K := K) (G := G) ?_
  have himage :=
    projectiveCharacterDivisibility_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  simpa [himage] using hforward

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Reverse integer descent from the `A`-span level: if Serre's regular-value divisibility lattice
is contained in the fixed Cartan-coordinate `A`-span, then every scaled regular-class indicator is
already in the integer Cartan coordinate range. -/
theorem scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartanCoordinate_span_ge
    (hspan_ge :
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ≤
        Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K))) :
    ∀ c : PRegularConjClass G p,
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  intro c
  have hdiag :
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G) := by
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
      (p := p) (G := G)]
    exact Submodule.subset_span ⟨c, rfl⟩
  have hcast_regular :
      regularIntegerFunctionCast (p := p) (K := K) (G := G)
          (scaled_regular_integer_indicator (p := p) (G := G) c) ∈
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
    regularIntegerFunctionCast_mem_regularValueDivisibilitySubmodule_of_mem
      (p := p) (A := A) (K := K) (G := G) hdiag
  exact
    (regularIntegerFunctionCast_mem_projectiveCartanCoordinate_span_iff_mem_cartanCoordinateAddHom_range
      (p := p) (A := A) (K := K) (G := G)
      (scaled_regular_integer_indicator (p := p) (G := G) c)).1
      (hspan_ge hcast_regular)

/-- The reverse half of Brauer-coordinate stability is enough, together with the
regular-restriction image theorem, to realize all scaled regular-class indicators in the integer
Cartan coordinate range. -/
theorem scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_projectiveCharacter_image_and_brauer_reverse
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hreverse :
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ≤
        Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))) :
    ∀ c : PRegularConjClass G p,
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range := by
  refine
    scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartanCoordinate_span_ge
      (p := p) (A := A) (K := K) (G := G) ?_
  have himage :=
    projectiveCharacterDivisibility_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  simpa [himage] using hreverse

/-- Conditional closure: the regular-restriction image theorem plus Brauer-coordinate stability
of Serre's divisibility lattice gives the fixed integer Cartan range equality. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_projectiveCharacter_image_and_brauer_stable
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
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) :
    (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup := by
  refine
    cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_range_le_and_scaled_mem
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) ?_ ?_
  · exact
      cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_projectiveCharacter_image_and_brauer_forward
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord (le_of_eq hstable)
  · exact
      scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_projectiveCharacter_image_and_brauer_reverse
        (p := p) (A := A) (K := K) (G := G)
        π hπ_simple hπ_coord (le_of_eq hstable.symm)

/-- Minimal blocker theorem for this worker: after the regular-restriction image/divisibility
result is used, the desired fixed integer Cartan range equality is equivalent to stability of
Serre's regular-value divisibility lattice under the chosen Brauer-coordinate map. -/
theorem cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_iff_brauerRepr_stable_from_projectiveCharacter
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ)) :
    ((cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
      (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) ↔
      Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  constructor
  · intro hrange
    have hspan :
        Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K)) =
          regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
      refine
        projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_range_le_and_scaled_mem
          (p := p) (A := A) (K := K) (G := G) ?_ ?_
      · rw [hrange]
      · intro c
        rw [hrange]
        change
          scaled_regular_integer_indicator (p := p) (G := G) c ∈
            regularIntegerDiagonalSubmodule (p := p) (G := G)
        rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
          (p := p) (G := G)]
        exact Submodule.subset_span ⟨c, rfl⟩
    exact
      (projectiveCharacterDivisibility_brauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).trans hspan
  · intro hstable
    exact
      cartanCoordinateAddHom_range_eq_regularIntegerDiagonalSubmodule_of_projectiveCharacter_image_and_brauer_stable
        (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord hstable

end CartanIntegerDescentFromProjectiveCharacterWorker

end Representation
