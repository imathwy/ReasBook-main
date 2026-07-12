import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_3_3
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Definition_15_15_1_1
import LinearRepresentations_Serre_1977.Chap15.Theorem_15_15_2_2
import LinearRepresentations_Serre_1977.Chap16.Corollary_16_16_1_6
import LinearRepresentations_Serre_1977.Chap18.Definition_18_18_1_1
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCoordinates
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.PrimeToPRootLift

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u x

namespace Representation

section CartanCokernel

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]
variable {ι : Type x}

local instance :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _
/-- Helper for Exercise 18-18.3-2: in the Exercise `18.4` Brauer basis attached to a
coordinate-normalized family `π`, the coordinates of
`virtualModularCharacterOnPRegularConjClass x` are exactly the fixed
`regularClassCoordinateAddEquiv` coordinates of `x`, after coefficientwise casting. -/
theorem virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
    {K' : Type u} [Field K']
    (lift : PrimeToPRoot p k →* K'ˣ)
    (hlift : Function.Injective lift)
    (π : PRegularConjClass G p → FDRep k G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : R₀[k](G)) (c : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := k) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := k) (G := G) (π := π) hπ_simple hπ_coord
    (exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := k) (K := K')
        lift hlift
        π hπ_pairwise hπ_complete).repr
      (virtualModularCharacterOnPRegularConjClass
        (p := p) (k := k) (A := K') (G := G) (PrimeToPRoot.toFieldLift lift) x) c =
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) x c : K') := by
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_simple hπ_coord
  let bK' :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (k := k) (K := K')
      lift hlift
      π hπ_pairwise hπ_complete
  let bR :=
    simple_finiteRep_classes_basis_of_complete_family π hπ_pairwise hπ_complete
  let φ : R₀[k](G) →ₗ[ℤ] (PRegularConjClass G p → K') :=
    (virtualModularCharacterOnPRegularConjClass
      (p := p) (k := k) (A := K') (G := G) (PrimeToPRoot.toFieldLift lift)).toIntLinearMap
  letI : Fintype (PRegularConjClass G p) := Fintype.ofFinite (PRegularConjClass G p)
  have hbasis :
      ∀ i : PRegularConjClass G p, φ (bR i) = bK' i := by
    intro i
    calc
      φ (bR i) = φ [π i]₀ := by
        simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply]
      _ = FDRep.modularCharacterOnPRegularConjClass
            (p := p) (G := G) (A := K') (π i) (PrimeToPRoot.toFieldLift lift) := by
            change
              virtualModularCharacterOnPRegularConjClass
                  (p := p) (k := k) (A := K') (G := G) (PrimeToPRoot.toFieldLift lift) [π i]₀ =
                FDRep.modularCharacterOnPRegularConjClass
                  (p := p) (G := G) (A := K') (π i) (PrimeToPRoot.toFieldLift lift)
            exact
              virtualModularCharacterOnPRegularConjClass_class
                (p := p) (lift := PrimeToPRoot.toFieldLift lift) (E := π i)
      _ = bK' i := by
            symm
            exact
              exercise_18_18_2_9_field_irreducible_modular_characters_basis_apply
                (p := p) (k := k) (K := K')
                lift hlift
                π hπ_pairwise hπ_complete i
  have hrepr :
      ∀ y : R₀[k](G), ∀ i : PRegularConjClass G p,
        bK'.repr (φ y) i = (bR.repr y i : K') := by
    intro y i
    have himage :
        φ y = ∑ j, (bR.repr y j : K') • bK' j := by
      calc
        φ y = φ (∑ j, (bR.repr y j) • bR j) := by
          exact congrArg φ (bR.sum_repr y).symm
        _ = ∑ j, (bR.repr y j) • φ (bR j) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [map_zsmul]
        _ = ∑ j, (bR.repr y j) • bK' j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [hbasis j]
        _ = ∑ j, (bR.repr y j : K') • bK' j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← Int.cast_smul_eq_zsmul K']
    calc
      bK'.repr (φ y) i = bK'.repr (∑ j, (bR.repr y j : K') • bK' j) i := by
        rw [himage]
      _ = (bR.repr y i : K') := by
        simpa using congrFun (bK'.repr_sum_self fun j ↦ (bR.repr y j : K')) i
  have hcoord_repr :
      ∀ y : R₀[k](G), ∀ i : PRegularConjClass G p,
        bR.repr y i = regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y i := by
    intro y i
    have hcoord_sum :
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y =
          ∑ j, (bR.repr y j) •
            (Pi.single j (1 : ℤ) : PRegularConjClass G p → ℤ) := by
      calc
        regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) y =
            regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
              (∑ j, (bR.repr y j) • bR j) := by
                rw [bR.sum_repr]
        _ =
            ∑ j, (bR.repr y j) •
              regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) (bR j) := by
                rw [map_sum]
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [map_zsmul]
        _ =
            ∑ j, (bR.repr y j) •
              (Pi.single j (1 : ℤ) : PRegularConjClass G p → ℤ) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [bR, simple_finiteRep_classes_basis_of_complete_family_apply,
                  hπ_coord j]
    have hvalue := congrFun hcoord_sum i
    simpa [Pi.smul_apply, Pi.single_apply] using hvalue.symm
  calc
    bK'.repr
        (virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K') (G := G) (PrimeToPRoot.toFieldLift lift) x) c
      = (bR.repr x c : K') := hrepr x c
    _ = (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G) x c : K') := by
          exact congrArg (fun n : ℤ ↦ (n : K')) (hcoord_repr x c)

/-- Helper for Exercise 18-18.3-2: the Exercise `18.4` basis coefficient functional is determined
by the `d`-th projective-envelope pairing on all regular class functions, not only on actual
Brauer rows. This isolates the Cartan-side blocker as a projective-projective pairing statement.
-/
theorem fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hlift : Function.Injective lift)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a =
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (φ : PRegularConjClass G p → K) (d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) lift hlift
        π hπ_pairwise hπ_complete
    bK.repr φ d =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
              (if hs : IsPRegular p s then
                φ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
              else 0) := by
  classical
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (k := IsLocalRing.ResidueField A) (K := K) lift hlift
      π hπ_pairwise hπ_complete
  let L : (PRegularConjClass G p → K) →ₗ[K] K :=
    (Fintype.card G : K)⁻¹ •
      ∑ s : G,
        (if hs : IsPRegular p (s⁻¹) then
          regularRestriction (p := p) (A := A) (K := K) (G := G)
            (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
            (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
        else 0) •
          (if hs : IsPRegular p s then
            (LinearMap.proj
              (R := K) (φ := fun _ : PRegularConjClass G p ↦ K)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩))
          else 0)
  have hL_apply (f : PRegularConjClass G p → K) :
      L f =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              regularRestriction (p := p) (A := A) (K := K) (G := G)
                (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) *
              (if hs : IsPRegular p s then
                f (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
              else 0) := by
    simp only [L, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro s hs_mem
    by_cases hs : IsPRegular p s
    · rw [dif_pos hs, dif_pos hs]
      by_cases hs_inv : IsPRegular p (s⁻¹) <;> simp [hs_inv]
    · rw [dif_neg hs, dif_neg hs]
      simp
  have hbasis_pairing :
      ∀ j : PRegularConjClass G p, L (bK j) = bK.repr (bK j) d := by
    intro j
    have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
      intro s _hs
      haveI : HasEnoughRootsOfUnity K (orderOf s) :=
        HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
      exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
    have hdelta :=
      -- Serre's orthogonality relation already computes the projective pairing on the basis
      -- vectors coming from the chosen projective envelopes.
      projectiveEnvelope_regular_pairing_eq_delta
        (p := p) (A := A) (K := K) (G := G) (lift := lift)
        (hred := hred) (hω := hω)
        (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
        (P := P) (hP_envelope := hP_envelope) d j
    have hrepr_self :
        bK.repr (bK j) d = if d = j then (1 : K) else 0 := by
      -- Read the `d`-coordinate of the `j`-th basis vector from `repr_self`.
      rw [bK.repr_self j]
      by_cases hdj : d = j <;> simp [Finsupp.single_apply, hdj]
    calc
      L (bK j)
        =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p) (A := A) (K := K) (G := G)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                (if hs : IsPRegular p s then
                  bK j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
                else 0) := hL_apply (bK j)
      _ =
          (Fintype.card G : K)⁻¹ *
            ∑ s : G,
              (if hs : IsPRegular p (s⁻¹) then
                regularRestriction (p := p) (A := A) (K := K) (G := G)
                  (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                  (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
              else 0) *
                FDRep.modularCharacterZeroExtension (π j) (PrimeToPRoot.toFieldLift lift) s := by
          -- Rewrite the `j`-th basis vector as the `j`-th Brauer character before applying the
          -- established projective-envelope delta computation.
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs_mem
          by_cases hsp : IsPRegular p s
          · have hval :
                bK j (PRegularConjClass.ofSubtype (G := G) p ⟨s, hsp⟩) =
                  FDRep.modularCharacterOnPRegularConjClass
                    (p := p) (π j) (PrimeToPRoot.toFieldLift lift)
                    (PRegularConjClass.ofSubtype (G := G) p ⟨s, hsp⟩) := by
              simp [bK, exercise_18_18_2_9_field_irreducible_modular_characters_basis_apply]
            rw [FDRep.modularCharacterOnPRegularConjClass_ofSubtype] at hval
            refine congrArg₂ (· * ·) rfl ?_
            rw [dif_pos hsp, FDRep.modularCharacterZeroExtension, dif_pos hsp]
            exact hval
          · simp [FDRep.modularCharacterZeroExtension, hsp]
      _ = if d = j then (1 : K) else 0 := hdelta
      _ = bK.repr (bK j) d := by
          symm
          exact hrepr_self
  have hL_eq_repr : L φ = bK.repr φ d := by
    -- Both functionals are `K`-linear, so it is enough to compare them on the Exercise `18.4`
    -- basis vectors and then expand `φ` in that basis.
    calc
      L φ = L (∑ j, (bK.repr φ j) • bK j) := by
        rw [bK.sum_repr]
      _ = ∑ j, (bK.repr φ j) • L (bK j) := by
        simp only [map_sum, map_smul]
      _ = ∑ j, (bK.repr φ j) • bK.repr (bK j) d := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hbasis_pairing j]
      _ = bK.repr (∑ j, (bK.repr φ j) • bK j) d := by
        have hsum : (bK.repr (∑ j, (bK.repr φ j) • bK j)) d
            = ∑ j, (bK.repr φ j) • (bK.repr (bK j)) d := by
          simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
            Finset.sum_apply, Pi.smul_apply]
        exact hsum.symm
      _ = bK.repr φ d := by
        rw [bK.sum_repr]
  calc
    bK.repr φ d = L φ := hL_eq_repr.symm
    _ =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              regularRestriction (p := p) (A := A) (K := K) (G := G)
                (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) *
              (if hs : IsPRegular p s then
                φ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
              else 0) := hL_apply φ

/-- Helper for Exercise 18-18.3-2: in the fixed Exercise `18.4` basis attached to a
coordinate-normalized simple family `π`, the `d`-th coordinate of any Brauer row is recovered by
Serre's projective-envelope pairing with the `d`-th projective envelope. -/
theorem fixed_basis_repr_eq_projective_envelope_regular_pairing
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hlift : Function.Injective lift)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a =
          ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P : PRegularConjClass G p → FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (E : FDRep (IsLocalRing.ResidueField A) G) (d : PRegularConjClass G p) :
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) lift hlift
        π hπ_pairwise hπ_complete
    bK.repr
        (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) E (PrimeToPRoot.toFieldLift lift)) d =
      (Fintype.card G : K)⁻¹ *
        ∑ s : G,
          (if hs : IsPRegular p (s⁻¹) then
            regularRestriction (p := p) (A := A) (K := K) (G := G)
              (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
              (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
          else 0) *
              FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s := by
  classical
  let φ : PRegularConjClass G p → K :=
    FDRep.modularCharacterOnPRegularConjClass
      (p := p) (G := G) (A := K) E (PrimeToPRoot.toFieldLift lift)
  have hfunction :=
    fixed_basis_repr_eq_projective_envelope_regular_pairing_of_function
      (p := p) (G := G) (A := A) (K := K) lift hlift hred
      π hπ_simple hπ_coord P hP_envelope φ d
  calc
    (let hπ_pairwise :=
        pairwiseNonisomorphic_of_regularClassCoordinate_single
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
      let hπ_complete :=
        complete_irreducible_family_of_regularClassCoordinate_single
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
      let bK :=
        exercise_18_18_2_9_field_irreducible_modular_characters_basis
          (p := p) (k := IsLocalRing.ResidueField A) (K := K) lift hlift
          π hπ_pairwise hπ_complete
      bK.repr
        (FDRep.modularCharacterOnPRegularConjClass
          (p := p) (G := G) (A := K) E (PrimeToPRoot.toFieldLift lift)) d)
        =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              regularRestriction (p := p) (A := A) (K := K) (G := G)
                (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) *
              (if hs : IsPRegular p s then
                φ (PRegularConjClass.ofSubtype (G := G) p ⟨s, hs⟩)
              else 0) := by
          simpa [φ] using hfunction
    _ =
        (Fintype.card G : K)⁻¹ *
          ∑ s : G,
            (if hs : IsPRegular p (s⁻¹) then
              regularRestriction (p := p) (A := A) (K := K) (G := G)
                (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P d]ₚ₀)
                (PRegularConjClass.ofSubtype (G := G) p ⟨s⁻¹, hs⟩)
            else 0) *
              FDRep.modularCharacterZeroExtension E (PrimeToPRoot.toFieldLift lift) s := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro s hs_mem
          by_cases hsp : IsPRegular p s
          · refine congrArg₂ (· * ·) rfl ?_
            rw [dif_pos hsp, FDRep.modularCharacterZeroExtension, dif_pos hsp]
            simp [φ, FDRep.modularCharacterOnPRegularConjClass_ofSubtype]
          · simp [FDRep.modularCharacterZeroExtension, hsp]

/-- Helper for Exercise 18-18.3-2: the regular-restriction row of a projective scalar-extension
character is the descended virtual modular character of its Cartan image, assuming only the
primitive roots needed on the `p`-regular locus. -/
theorem regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row_of_regular_roots
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift liftK)
        (cartanHom (IsLocalRing.ResidueField A) G x) := by
  let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hredK : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((liftK x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := by
    intro x
    refine ⟨((primeToPRoot_unitsLift (p := p) (A := A) x : Aˣ) : A), ?_, ?_⟩
    · simp [liftK]
    · exact residue_primeToPRoot_unitLift (p := p) (A := A) x
  ext d
  let s := PRegularConjClass.representative (G := G) (p := p) d
  have hs : PRegularConjClass.ofSubtype (G := G) p s = d := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) d
  -- Evaluate both descended functions on the chosen regular representative of `d`.
  rw [← hs, virtualModularCharacterOnPRegularConjClass_ofSubtype]
  simpa [liftK] using
    regularRestriction_projectiveCharacterScalarExtension_eq_virtualModularCharacterOnPRegular_cartan
      (p := p) (A := A) (K := K) (G := G) (lift := liftK) hredK hω x s

/-- Helper for Exercise 18-18.3-2: Serre's mixed-character orthogonality argument should identify
the Cartan image of each projective envelope in a coordinate-normalized simple family with the
centralizer-`p`-part multiple of the matching simple class. This isolates the remaining pure
Cartan-class frontier from the downstream generator rewrites. -/
theorem regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (x : P₀[IsLocalRing.ResidueField A](G)) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    regularRestriction (p := p) (A := A) (K := K) (G := G)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) =
      virtualModularCharacterOnPRegularConjClass
        (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
        (PrimeToPRoot.toFieldLift liftK)
        (cartanHom (IsLocalRing.ResidueField A) G x) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row_of_regular_roots
      (p := p) (A := A) (K := K) (G := G) hω x

/-- Helper for Exercise 18-18.3-2: after rewriting a projective-character regular restriction
as the descended virtual modular character of its Cartan image, the Exercise `18.4` Brauer-basis
coordinate is the corresponding Cartan coordinate, cast to `K`. This version only assumes the
primitive roots needed on the `p`-regular locus. -/
theorem regularRestriction_projectiveCharacterScalarExtension_basis_repr_eq_cast_cartanCoordinate_of_regular_roots
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : P₀[IsLocalRing.ResidueField A](G))
    (d : PRegularConjClass G p) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK
        (fun _ _ hyz ↦
          primeToPRoot_unitsLift_injective (p := p) (A := A) <|
            IsFractionRing.injective A K (congrArg (fun u : Kˣ ↦ (u : K)) hyz))
        π hπ_pairwise hπ_complete
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)) d =
      (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d : K) := by
  let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hliftK : Function.Injective liftK := by
    intro y z hyz
    apply primeToPRoot_unitsLift_injective (p := p) (A := A)
    apply IsFractionRing.injective A K
    exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK hliftK
      π hπ_pairwise hπ_complete
  have hrow :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x) =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift liftK)
          (cartanHom (IsLocalRing.ResidueField A) G x) := by
    -- First use the `c = d ∘ e` triangle to rewrite the whole row as a Cartan virtual
    -- modular character.
    simpa [liftK] using
      regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row_of_regular_roots
        (p := p) (A := A) (K := K) (G := G) hω x
  calc
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)) d
      =
        bK.repr
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift liftK)
            (cartanHom (IsLocalRing.ResidueField A) G x)) d := by
          rw [hrow]
    _ =
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          (cartanHom (IsLocalRing.ResidueField A) G x) d : K) := by
          -- The Exercise `18.4` Brauer basis reads off the fixed regular-class coordinate.
          simpa [bK, liftK] using
            (virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) (K' := K) liftK hliftK
              π hπ_simple hπ_coord
              (cartanHom (IsLocalRing.ResidueField A) G x) d)
    _ =
        (cartanCoordinateAddHom
          (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d : K) := by
          rfl

/-- Helper for Exercise 18-18.3-2: after rewriting a projective-character regular restriction
as the descended virtual modular character of its Cartan image, the Exercise `18.4` Brauer-basis
coordinate is the corresponding Cartan coordinate, cast to `K`. -/
theorem regularRestriction_projectiveCharacterScalarExtension_basis_repr_eq_cast_cartanCoordinate
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (x : P₀[IsLocalRing.ResidueField A](G))
    (d : PRegularConjClass G p) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK
        (fun _ _ hyz ↦
          primeToPRoot_unitsLift_injective (p := p) (A := A) <|
            IsFractionRing.injective A K (congrArg (fun u : Kˣ ↦ (u : K)) hyz))
        π hπ_pairwise hπ_complete
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) x)) d =
      (cartanCoordinateAddHom
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) x d : K) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    regularRestriction_projectiveCharacterScalarExtension_basis_repr_eq_cast_cartanCoordinate_of_regular_roots
      (p := p) (A := A) (K := K) (G := G) hω π hπ_simple hπ_coord x d

/-- Helper for Exercise 18-18.3-2: once the regular-restriction row is rewritten as the descended
virtual modular character of the Cartan image, the Exercise `18.4` basis coordinate at `d`
recovers the `regularClassCoordinateAddEquiv` coordinate of that Cartan class. This version only
assumes the primitive roots needed on the `p`-regular locus. -/
theorem coordinate_normalized_projective_envelope_cartan_coordinate_readback_of_regular_roots
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P :
      PRegularConjClass G p →
        FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (c d : PRegularConjClass G p) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK
        (fun _ _ hyz ↦
          primeToPRoot_unitsLift_injective (p := p) (A := A) <|
            IsFractionRing.injective A K (congrArg (fun u : Kˣ ↦ (u : K)) hyz))
        π hπ_pairwise hπ_complete
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
      (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀) d : K) := by
  let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hliftK : Function.Injective liftK := by
    intro y z hyz
    apply primeToPRoot_unitsLift_injective (p := p) (A := A)
    apply IsFractionRing.injective A K
    exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  let bK :=
    exercise_18_18_2_9_field_irreducible_modular_characters_basis
      (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK hliftK
      π hπ_pairwise hπ_complete
  have hrow :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
          (PrimeToPRoot.toFieldLift liftK)
          (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀) := by
    -- First rewrite the regular-restriction row as the descended virtual modular character of
    -- the Cartan image; this is the source proof's modular-character comparison.
    simpa [liftK] using
      regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row_of_regular_roots
        (p := p) (A := A) (K := K) (G := G) hω (x := [P c]ₚ₀)
  calc
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d
      =
        bK.repr
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (k := IsLocalRing.ResidueField A) (A := K) (G := G)
            (PrimeToPRoot.toFieldLift liftK)
            (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀)) d := by
          rw [hrow]
    _ =
        (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀) d : K) := by
          -- Once the row is in descended virtual-character form, the Exercise `18.4` basis
          -- reads off exactly the canonical regular-class coordinate.
          simpa [bK, liftK] using
            (virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
              (p := p) (k := IsLocalRing.ResidueField A) (G := G) (K' := K) liftK hliftK
              π hπ_simple hπ_coord
              (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀) d)

/-- Helper for Exercise 18-18.3-2: once the regular-restriction row is rewritten as the descended
virtual modular character of the Cartan image, the Exercise `18.4` basis coordinate at `d`
recovers the `regularClassCoordinateAddEquiv` coordinate of that Cartan class. -/
theorem coordinate_normalized_projective_envelope_cartan_coordinate_readback
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P :
      PRegularConjClass G p →
        FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (c d : PRegularConjClass G p) :
    let liftK : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ :=
      (Units.map (algebraMap A K).toMonoidHom).comp
        (primeToPRoot_unitsLift (p := p) (A := A))
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bK :=
      exercise_18_18_2_9_field_irreducible_modular_characters_basis
        (p := p) (k := IsLocalRing.ResidueField A) (K := K) liftK
        (fun _ _ hyz ↦
          primeToPRoot_unitsLift_injective (p := p) (A := A) <|
            IsFractionRing.injective A K (congrArg (fun u : Kˣ ↦ (u : K)) hyz))
        π hπ_pairwise hπ_complete
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d =
      (regularClassCoordinateAddEquiv
          (p := p) (k := IsLocalRing.ResidueField A) (G := G)
          (cartanHom (IsLocalRing.ResidueField A) G [P c]ₚ₀) d : K) := by
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  exact
    coordinate_normalized_projective_envelope_cartan_coordinate_readback_of_regular_roots
      (p := p) (A := A) (K := K) (G := G) hω π hπ_simple hπ_coord P c d
/-
  let liftK : PrimeToPRoot p k →* Kˣ :=
    (Units.map (algebraMap A K).toMonoidHom).comp
      (primeToPRoot_unitsLift (p := p) (A := A))
  have hliftK : Function.Injective liftK := by
    intro y z hyz
    apply primeToPRoot_unitsLift_injective (p := p) (A := A)
    apply IsFractionRing.injective A K
    exact congrArg (fun u : Kˣ ↦ (u : K)) hyz
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_simple hπ_coord
  let bK :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (k := k) (A := K) (PrimeToPRoot.toFieldLift liftK)
      (by
        intro y z hyz
        apply hliftK
        exact Units.ext hyz)
      π hπ_pairwise hπ_complete
  have hrow :
      regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) =
        virtualModularCharacterOnPRegularConjClass
          (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift liftK)
          (cartanHom k G [P c]ₚ₀) := by
    -- Route correction: first rewrite the whole regular-restriction row as the descended virtual
    -- modular character of the Cartan image, then read its basis coordinates by the canonical
    -- `regularClassCoordinateAddEquiv` comparison.
    simpa [liftK] using
      regularRestriction_projectiveCharacterScalarExtension_eq_cartan_virtual_row
        (p := p) (A := A) (K := K) (G := G) (x := [P c]ₚ₀)
  calc
    bK.repr
        (regularRestriction (p := p) (A := A) (K := K) (G := G)
          (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)) d
      =
        bK.repr
          (virtualModularCharacterOnPRegularConjClass
            (p := p) (k := k) (A := K) (G := G) (PrimeToPRoot.toFieldLift liftK)
            (cartanHom k G [P c]ₚ₀)) d := by
              rw [hrow]
    _ =
        (regularClassCoordinateAddEquiv (p := p) (k := k) (G := G)
          (cartanHom k G [P c]ₚ₀) d : K) := by
            -- Once the row is in descended virtual-character form, the Exercise `18.4` basis
            -- reads off exactly the canonical regular-class coordinate.
            simpa [bK, liftK] using
              (virtualModularCharacter_basis_repr_eq_cast_regularClassCoordinate
                (p := p) (k := k) (G := G) (K' := K) liftK hliftK
                π hπ_simple hπ_coord (cartanHom k G [P c]ₚ₀) d)
-/

/-- Helper for Exercise 18-18.3-2: specialize Serre's projective-envelope regular-restriction
value formula to a coordinate-normalized family indexed directly by `PRegularConjClass G p`.
This keeps the remaining Cartan-class proof on the source-faithful orthogonality route while
removing the bookkeeping around `PairwiseNonisomorphic` and completeness.
MOVE THIS DECLARATION (down through its closing `simpa … d))` line) to AFTER
`complete_irreducible_family_of_regularClassCoordinate_single` (~line 3540): it forward-references
`regularClassCoordinateAddEquiv` (3310), `pairwiseNonisomorphic_of_regularClassCoordinate_single`
(3514) and `complete_irreducible_family_of_regularClassCoordinate_single` (3533). -/
theorem coordinate_normalized_projective_envelope_regularRestriction_value
    {A : Type u} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]
    {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (π : PRegularConjClass G p → FDRep (IsLocalRing.ResidueField A) G)
    (hπ_simple : ∀ c, Simple (π c))
    (hπ_coord :
      ∀ c,
        regularClassCoordinateAddEquiv
            (p := p) (k := IsLocalRing.ResidueField A) (G := G) [π c]₀ =
          (Pi.single c (1 : ℤ) : PRegularConjClass G p → ℤ))
    (P :
      PRegularConjClass G p →
        FiniteProjectiveGroupAlgebraModule (IsLocalRing.ResidueField A) G)
    (hP_envelope :
      ∀ c, ∃ f : (P c).V →ₗ[(IsLocalRing.ResidueField A)[G]] asModule (π c).ρ,
        f.IsProjectiveEnvelope)
    (c d : PRegularConjClass G p) :
    let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
    let hliftA := primeToPRoot_unitsLift_injective (p := p) (A := A)
    let hπ_pairwise :=
      pairwiseNonisomorphic_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
    let hπ_complete :=
      complete_irreducible_family_of_regularClassCoordinate_single
        (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
    let bA :=
      exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
        (p := p) (A := A)
        liftA hliftA
        (residue_primeToPRoot_canonicalLift (p := p) (A := A))
        π hπ_pairwise hπ_complete
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)) := by
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := IsLocalRing.ResidueField A) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A)
      liftA hliftA
      (residue_primeToPRoot_canonicalLift (p := p) (A := A))
      π hπ_pairwise hπ_complete
  have hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s) := by
    intro s _hs
    haveI : HasEnoughRootsOfUnity K (orderOf s) :=
      HasEnoughRootsOfUnity.of_dvd K (Monoid.order_dvd_exponent s)
    exact HasEnoughRootsOfUnity.exists_primitiveRoot K (orderOf s)
  change
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀) d =
      algebraMap A K
        ((ConjClasses.centralizerPPart p d.1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c))
  have hsrc :=
    projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (hω := hω)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c
      (inversePRegularConjClass (p := p) d)
  change
    regularRestriction (p := p)
        (projectiveCharacterScalarExtension (A := A) (K := K) (G := G) [P c]ₚ₀)
        (inversePRegularConjClass (p := p) (inversePRegularConjClass (p := p) d)) =
      algebraMap A K
        ((ConjClasses.centralizerPPart p (inversePRegularConjClass (p := p) d).1 : A) *
          (bA.repr
            (primeToP_regular_indicator
              (p := p) (A := A) (G := G)
              (inversePRegularConjClass (p := p) d)) c)) at hsrc
  rw [inversePRegularConjClass_involutive] at hsrc
  rw [inversePRegularConjClass_val, ConjClasses.centralizerPPart_inv] at hsrc
  exact hsrc
/-
  let liftA := primeToPRoot_canonicalLift (p := p) (A := A)
  let hliftA : Function.Injective liftA :=
    primeToPRoot_unitsLift_injective (p := p) (A := A)
  let hπ_pairwise :=
    pairwiseNonisomorphic_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_coord
  let hπ_complete :=
    complete_irreducible_family_of_regularClassCoordinate_single
      (p := p) (k := k) (G := G) (π := π) hπ_simple hπ_coord
  let bA :=
    exercise_18_18_2_9_irreducible_modular_characters_basis_dvr
      (p := p) (A := A) liftA hliftA π hπ_pairwise hπ_complete
  -- Specialize the source orthogonality formula at the inverse class, then rewrite back using
  -- `inversePRegularConjClass_involutive`.
  simpa [liftA, hliftA, bA, inversePRegularConjClass_involutive,
    ConjClasses.centralizerPPart_inv] using
    (projectiveEnvelope_regularRestriction_value_eq_centralizerPPart_mul_repr_inv
      (p := p) (A := A) (K := K) (G := G)
      (π := π) (hπ_pairwise := hπ_pairwise) (hπ_complete := hπ_complete)
      (P := P) (hP_envelope := hP_envelope) c
      (inversePRegularConjClass (p := p) d))
-/

/-!
Route correction: the following abandoned block tried to prove that, after choosing a
coordinate-normalized simple family, each corresponding projective envelope maps to a single
scaled coordinate vector.  That would diagonalize the Cartan matrix in a projective-envelope/simple
basis, which is stronger than Serre's Exercise 18.5 and is false in general.  Exercise 18.5(b)
computes the cokernel/invariant factors, not individual Cartan columns.
-/
end CartanCokernel

end Representation
