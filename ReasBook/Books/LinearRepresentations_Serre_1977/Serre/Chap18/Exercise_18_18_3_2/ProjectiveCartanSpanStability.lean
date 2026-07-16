import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.ProjectiveCartanIntegerDescent
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCokernelSaturation
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanPPrimaryBridge
import LinearRepresentations_Serre_1977.Serre.Chap18.Exercise_18_18_3_2.CartanCoordinateRangeGenerators

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section ProjectiveCartanSpanStability

variable {p : ℕ}
variable {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G] [Finite G]
variable [IsDomain A] [IsDiscreteValuationRing A]
variable [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
variable [Fact p.Prime] [IsAlgClosed (IsLocalRing.ResidueField A)]
variable [CharP (IsLocalRing.ResidueField A) p] [CharZero K]
variable [HasEnoughRootsOfUnity K (Monoid.exponent G)]

local instance projectiveCartanSpanStabilityFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance projectiveCartanSpanStabilityDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: the desired fixed-coordinate `hspan` is exactly the assertion
that the Brauer-coordinate map preserves Serre's regular value-divisibility lattice.

This packages the current obstruction without strengthening Serre 18.5(a): the already proved
image formula identifies the Brauer-coordinate image of the divisibility lattice with the Cartan
coordinate span, so replacing that image by the original lattice is precisely the missing
stability claim. -/
theorem
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_iff_cartanCoordinate_span_eq
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
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) ↔
      Submodule.span A
          ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
            Set (PRegularConjClass G p → K)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  have himage :=
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_eq_cartanCoordinate_span
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
  constructor
  · intro hstable
    exact himage.symm.trans hstable
  · intro hspan
    exact himage.trans hspan

/-- Helper for Exercise 18-18.3-2: a named adapter from Brauer-coordinate stability to the fixed
coordinate span equality. This is useful when testing whether a proposed stability input is strong
enough, but the equivalence above shows it is not a consequence of the image theorem alone. -/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_brauerRepr_stable
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
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) :=
  (projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_iff_cartanCoordinate_span_eq
    (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).1 hstable

/-- Helper for Exercise 18-18.3-2: the fixed-coordinate integer range criterion is enough to
close the Brauer-coordinate stability statement.

This is the minimal fixed-coordinate form needed after Serre `18.5(a)`: the Cartan coordinate
range is contained in the regular integer diagonal lattice, and the diagonal generators themselves
occur in that range.  It deliberately does not claim that these fixed-coordinate hypotheses follow
from the invariant-factor statement of Serre `18.5(b)`. -/
theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_range_le_and_scaled_mem
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hscaled :
      ∀ c : PRegularConjClass G p,
        scaled_regular_integer_indicator (p := p) (G := G) c ∈
          (cartanCoordinateAddHom
            (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range) :
    Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine
    (projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_iff_cartanCoordinate_span_eq
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord).2 ?_
  exact
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_range_le_and_scaled_mem
      (p := p) (A := A) (K := K) (G := G) hsubset hscaled

omit [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [HasEnoughRootsOfUnity K (Monoid.exponent G)] in
/-- Fixed-coordinate generator/divisibility adapter for the `A`-span endpoint.

This is the direct endpoint form of the hypotheses isolated in
`CartanCoordinateRangeGenerators.lean`: coordinatewise divisibility gives the forward inclusion,
and one Cartan preimage of each centralizer-`p`-part multiple gives the scaled diagonal
generators. -/
theorem projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_coordinate_divisible_and_cartan_generators
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hdiv :
      ∀ x : P₀[IsLocalRing.ResidueField A](G), ∀ c : PRegularConjClass G p,
        ∃ a : ℤ,
          cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) x c =
            (ConjClasses.centralizerPPart p c.1 : ℤ) * a)
    (hgen :
      ∀ c : PRegularConjClass G p,
        ∃ x : P₀[IsLocalRing.ResidueField A](G),
          cartanHom (IsLocalRing.ResidueField A) G x =
            (ConjClasses.centralizerPPart p c.1 : ℤ) • [π c]₀) :
    Submodule.span A
        ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
          Set (PRegularConjClass G p → K)) =
      regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine
    projectiveCartanCoordinate_span_eq_regularValueDivisibilitySubmodule_of_range_le_and_scaled_mem
      (p := p) (A := A) (K := K) (G := G) ?_ ?_
  · exact
      cartanCoordinateAddHom_range_le_regularIntegerDiagonalSubmodule_of_coordinate_divisible
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) hdiv
  · exact
      scaled_regular_integer_indicator_mem_cartanCoordinateAddHom_range_of_cartan_generators
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord hgen

/-- Helper for Exercise 18-18.3-2: a fixed-coordinate equality of the integer Cartan range with
the regular diagonal lattice closes the Brauer-coordinate stability statement. -/
theorem projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_cartanCoordinate_range_eq
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hrange :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :
    Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  refine
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_range_le_and_scaled_mem
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord ?_ ?_
  · rw [hrange]
  · intro c
    rw [hrange]
    change
      scaled_regular_integer_indicator (p := p) (G := G) c ∈
        regularIntegerDiagonalSubmodule (p := p) (G := G)
    rw [regularIntegerDiagonalSubmodule_eq_span_scaled_regular_integer_indicator
      (p := p) (G := G)]
    exact Submodule.subset_span ⟨c, rfl⟩

/-- Fixed-coordinate p-primary criterion for the Brauer-coordinate stability statement.

Let `N` be the fixed Cartan coordinate range and `D` the regular integer diagonal lattice.  Once
`N ≤ D`, the quotient by `N` is already a finite `p`-group; therefore if the visible intermediate
quotient `D / N` has order prime to `p`, then `N = D`, and the fixed-coordinate range-equality
criterion above closes the stability statement. -/
theorem
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_range_le_and_coprime_diagonal_quotient
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (hsubset :
      (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range ≤
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
    (hcop :
      Nat.Coprime p
        (Nat.card
          ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup ⧸
            ((cartanCoordinateAddHom
              (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range).addSubgroupOf
              (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup))) :
    Submodule.map
          (projectiveCartanASpanBrauerRepr
            (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord)
          (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G)) =
        regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G) := by
  let N : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (cartanCoordinateAddHom
      (p := p) (k := IsLocalRing.ResidueField A) (G := G)).range
  let D : AddSubgroup (PRegularConjClass G p → ℤ) :=
    (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup
  haveI : Finite ((PRegularConjClass G p → ℤ) ⧸ N) := by
    simpa [N] using
      cartanCoordinateAddHom_range_quotient_finite
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  have hP : IsPGroup p (Multiplicative ((PRegularConjClass G p → ℤ) ⧸ N)) := by
    simpa [N] using
      cartanCoordinateAddHom_range_quotient_isPGroup
        (p := p) (k := IsLocalRing.ResidueField A) (G := G)
  have hND : N ≤ D := by
    simpa [N, D] using hsubset
  have hrange : N = D :=
    addSubgroup_eq_of_quotient_isPGroup_of_quotient_card_coprime
      (p := p) N D hND hP (by simpa [N, D] using hcop)
  exact
    projectiveCartanASpanBrauerRepr_regularValueDivisibility_stable_of_cartanCoordinate_range_eq
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord
      (by simpa [N, D] using hrange)

/-- Source-side quotient form of Serre 18.5(a): after regular restriction, the projective
character lattice has the same quotient as the coordinatewise divisibility lattice. This avoids
any assertion that the Brauer-coordinate change of basis preserves that divisibility lattice. -/
noncomputable def projectiveCharacterRegularRestrictionQuotientLinearEquivPi :
    ((PRegularConjClass G p → K) ⧸
        Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G))) ≃ₗ[A]
      ∀ c : PRegularConjClass G p,
        K ⧸ Submodule.span A
          ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    (Submodule.Quotient.equiv
        (Submodule.map
          (regularRestrictionLinearMap (p := p) (A := A) (K := K) (G := G))
          (projectiveCharacterSubmodule (A := A) (K := K) (G := G)))
        (regularValueDivisibilitySubmodule (p := p) (A := A) (K := K) (G := G))
        (LinearEquiv.refl A (PRegularConjClass G p → K))
        (by
          simpa using
            projectiveCharacterSubmodule_map_regularRestriction_eq_regularValueDivisibilitySubmodule
              (p := p) (A := A) (K := K) (G := G) hω)).trans
      (regularValueDivisibilityQuotientLinearEquivPi (p := p) (A := A) (K := K) (G := G))

/-- Source-side product bridge for the Cartan coordinate span: choosing the normalized Brauer
family gives a quotient decomposition for the Cartan coordinate `A`-span by transporting Serre
18.5(a) through the Brauer-coordinate equivalence, without identifying that span with the original
divisibility lattice. -/
theorem projectiveCartanCoordinateASpanQuotientLinearEquivPi_nonempty :
    Nonempty
      (((PRegularConjClass G p → K) ⧸
          Submodule.span A
            ((projectiveCartanCoordinateCast (p := p) (A := A) (K := K) (G := G)).range :
              Set (PRegularConjClass G p → K))) ≃ₗ[A]
        ∀ c : PRegularConjClass G p,
          K ⧸ Submodule.span A
            ({algebraMap A K (ConjClasses.centralizerPPart p c.1 : A)} : Set K)) := by
  rcases
      exists_coordinate_normalized_complete_family_with_projective_envelopes
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) with
    ⟨π, hπ_simple, hπ_coord, _hπ_pairwise, _hπ_complete, _P, _hP_envelope⟩
  exact
    ⟨projectiveCartanCoordinateASpanQuotientLinearEquivPi
      (p := p) (A := A) (K := K) (G := G) π hπ_simple hπ_coord⟩

end ProjectiveCartanSpanStability

end Representation
