import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_2_1
import LinearRepresentations_Serre_1977.Chap03.Theorem_3_3_2_1
import LinearRepresentations_Serre_1977.Chap06.Corollary_6_6_5_4
import LinearRepresentations_Serre_1977.Chap06.Proposition_6_6_5_5
import LinearRepresentations_Serre_1977.Chap12.Exercise_12_12_2_6.FieldDenominatorPrelude
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

noncomputable section

open scoped BigOperators
open scoped Representation

universe u v w

namespace Representation

open CategoryTheory
open Exercise_12_12_2_6

section FieldPart

variable {K : Type u} [Field K] [CharZero K]
variable {G : Type u} [Group G] [Finite G]

local instance instFintypeGExercise_12_12_2_6_field_basis : Fintype G := Fintype.ofFinite G

/-- Helper for Exercise 12-12.2-6: choose a finite complete pairwise nonisomorphic family of
simple finite-dimensional `K`-representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family_local :
    ∃ (ι : Type u) (_ : Fintype ι) (π : ι → FDRep K G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular K G)
  let e :
      (Representation.directSum fun i ↦ (σ i).toRepresentation).Equiv (leftRegular K G) :=
    directSum_equiv_of_iSupIndep_of_iSup_eq_top (ρ := leftRegular K G) σ hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨f⟩
            exact ⟨f.symm⟩,
          fun {i j k} hij hjk ↦ by
            rcases hij with ⟨f⟩
            rcases hjk with ⟨g⟩
            exact ⟨f.trans g⟩⟩ }
  let ι : Type u := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep K G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    -- Distinct quotient classes cannot label isomorphic simple summands.
    intro q q' hqq' hIso
    rcases hIso with ⟨f⟩
    have hclasses :
        (⟦Quotient.out q⟧ : Quotient r) = ⟦Quotient.out q'⟧ := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep K G) (Rep K G)).mapIso f)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : Quotient r) := (Quotient.out_eq q).symm
      _ = ⟦Quotient.out q'⟧ := hclasses
      _ = q' := Quotient.out_eq q'
  have hσ_complete :
      ∀ (τ : FDRep K G) [Simple τ], ∃ i : κ, Nonempty (τ ≅ FDRep.of ((σ i).toRepresentation)) := by
    intro τ _
    letI : Representation.IsIrreducible τ.ρ := FDRep.isIrreducible_of_simple τ
    have hτ_nontriv : Nontrivial τ := by
      by_contra hτ_sub
      letI : Subsingleton τ := not_nontrivial_iff_subsingleton.mp hτ_sub
      have hzero : (𝟙 τ : τ ⟶ τ) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero τ hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : τ)
    let f : Representation.IntertwiningMap (leftRegular K G) τ.ρ :=
      (Representation.leftRegularMapEquiv τ.ρ).symm v
    have hf_nonzero : f ≠ 0 := by
      intro hf
      apply hv
      have hf' := congrArg (Representation.leftRegularMapEquiv τ.ρ) hf
      simpa [f] using hf'
    let F :
        Representation.IntertwiningMap
          (Representation.directSum fun i ↦ (σ i).toRepresentation) τ.ρ :=
      intertwiningMapCongrLeft_local (K := K) (G := G) e τ.ρ f
    have hF_nonzero : F ≠ 0 := by
      intro hF
      exact hf_nonzero ((intertwiningMapCongrLeft_local (K := K) (G := G) e τ.ρ).injective hF)
    have hcomponent :
        ∃ i, (directSumIntertwiningMapEquivPi_local
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) ≠ 0 := by
      by_contra hnone
      have hnone' := not_exists.mp hnone
      apply hF_nonzero
      apply (directSumIntertwiningMapEquivPi_local
        (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ)).injective
      ext i x
      have hi0 :
          (directSumIntertwiningMapEquivPi_local
            (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) = 0 := by
        simpa using hnone' i
      simp [hi0]
    rcases hcomponent with ⟨i, hi⟩
    have hi_iso : Nonempty (((σ i).toRepresentation).Equiv τ.ρ) := by
      by_contra hnot
      let ρ1 := (σ i).toRepresentation
      let ρ2 := τ.ρ
      let fi : Representation.IntertwiningMap ((σ i).toRepresentation) τ.ρ :=
        directSumIntertwiningMapEquivPi_local
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i
      letI : Representation.IsIrreducible ((σ i).toRepresentation) := by
        exact hσ_irr i
      have hnot' : ¬ Nonempty (Representation.Equiv ((σ i).toRepresentation) τ.ρ) := hnot
      have hnot'' : ¬ Nonempty (ρ1.Equiv ρ2) := by
        simpa [ρ1, ρ2] using hnot'
      -- The nonisomorphic case forces the chosen coordinate intertwiner to vanish.
      have hfi_zero' :
          (show ρ1.IntertwiningMap ρ2 from fi) = 0 := by
        exact
          @Representation.intertwiningMap_eq_zero_of_not_isomorphic
            K inferInstance G inferInstance
            ↥(σ i).toSubmodule inferInstance inferInstance
            ↥τ inferInstance inferInstance
            ρ1 ρ2 inferInstance inferInstance
            (show ρ1.IntertwiningMap ρ2 from fi) hnot''
      have hfi_zero : fi = 0 := by
        simpa [ρ1, ρ2] using hfi_zero'
      exact hi hfi_zero
    rcases hi_iso with ⟨eτ⟩
    -- A nonzero coordinate map between irreducibles is an equivalence, hence an `FDRep` isomorphism.
    refine ⟨i, ?_⟩
    exact ⟨(fdRepIsoOfRho_local (K := K) (G := G) τ).trans eτ.symm.toFDRepIso⟩
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    refine
      { isSimple := ?_
        exists_iso := ?_ }
    · intro q
      letI : Representation.IsIrreducible (π q).ρ := by
        simpa [π] using hσ_irr (Quotient.out q)
      exact FDRep.simple_of_isIrreducible (π q)
    · intro τ _
      obtain ⟨i, hi⟩ := hσ_complete τ
      refine ⟨(⟦i⟧ : Quotient r), ?_⟩
      have hout :
          Nonempty (((σ (Quotient.out (⟦i⟧ : Quotient r))).toRepresentation).Equiv
            ((σ i).toRepresentation)) := by
        exact Quotient.exact (Quotient.out_eq (⟦i⟧ : Quotient r))
      rcases hout with ⟨hout⟩
      rcases hi with ⟨hi⟩
      simpa [π] using ⟨hi.trans hout.toFDRepIso.symm⟩
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 12-12.2-6: transporting through a chosen finite basis gives an equivalent
representation. -/
def finBasisRepresentationEquiv_local
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ρ.Equiv (finBasisRepresentation_local (K := K) (G := G) ρ) :=
  Representation.Equiv.mk (Module.finBasis K V).equivFun fun g => by
    -- The basis transport intertwines the original action with its coordinate model.
    ext x i
    simp [finBasisRepresentation_local, LinearEquiv.conj_apply_apply]

/-- Helper for Exercise 12-12.2-6: lifting only the carrier by `ULift` keeps the same action
while moving the underlying type to a larger universe. -/
def ulift_carrier_representation_local
    {F : Type*} [Field F]
    {G0 : Type*} [Group G0]
    {W : Type*} [AddCommGroup W] [Module F W]
    (ρ : Representation F G0 W) :
    Representation F G0 (ULift W) where
  toFun g :=
    { toFun := fun x ↦ ⟨ρ g x.down⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro a x
        ext
        simp }
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

/-- Helper for Exercise 12-12.2-6: lifting only the carrier by `ULift` does not change the
character. -/
theorem ulift_carrier_representation_character_apply_local
    {F : Type*} [Field F]
    {G0 : Type*} [Group G0]
    {W : Type*} [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F G0 W) (g : G0) :
    (ulift_carrier_representation_local ρ).character g = ρ.character g := by
  -- `ULift.moduleEquiv` conjugates the lifted action back to the original one.
  change
    LinearMap.trace F (ULift W)
      ((ULift.moduleEquiv.symm : W ≃ₗ[F] ULift W).conj (ρ g)) =
        LinearMap.trace F W (ρ g)
  exact LinearMap.trace_conj' (ρ g) (ULift.moduleEquiv.symm : W ≃ₗ[F] ULift W)

/-- Helper for Exercise 12-12.2-6: the normalized pairing is additive on finite integer linear
combinations in its left argument over an arbitrary field. -/
theorem groupFunctionPairing_sum_zsmul_left_overField_local
    {ι : Type*} [Fintype ι]
    (s : Finset ι) (a : ι → ℤ) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      have hzsmul : (a i • χ i : G → K) = (((a i : ℤ) : K) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      -- Rewrite the inserted term into the scalar form expected by the pairing API.
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 12-12.2-6: pairing a character-ring element with an irreducible basis
character isolates the corresponding basis coefficient. -/
theorem basis_coefficient_pairing_eq_local
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G))
    (i : ι) :
    ⟪(x : G → K), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : G → K) := by
    -- Expand the irreducible-basis expression of `x` inside the ambient class-function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R[K](G) ↦ (z : G → K)) (b.sum_repr x)
  have horth :
      Pairwise fun j k ↦
        ⟪(π j).character, (π k).character⟫ = (0 : K) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      K π hπ_complete.isSimple hπ_pairwise
  calc
    ⟪(x : G → K), (π i).character⟫
        = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
            -- Replace `x` by its irreducible-basis expansion before pairing.
            simpa [hx] using
              congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character)
                hx.symm
    _ = ∑ j, ((c j : ℤ) : K) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left_overField_local
              (K := K) (s := Finset.univ) (a := c)
              (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            simp [horth hji]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- Helper for Exercise 12-12.2-6: the self-pairing of an irreducible character over a field of
characteristic zero is nonzero. -/
theorem self_pairing_character_ne_zero_local
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  have hcard_ne : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let n : ℕ := Module.finrank K (Representation.IntertwiningMap V.ρ V.ρ)
  have hn_pos : 0 < n := by
    have hV_nontriv : Nontrivial V := by
      by_contra hV_sub
      letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
      have hzero : (𝟙 V : V ⟶ V) = 0 := by
        ext x
        simp
      exact CategoryTheory.id_nonzero V hzero
    letI : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ) := by
      refine ⟨0, 1, ?_⟩
      intro hone
      obtain ⟨x, hx⟩ := exists_ne (0 : V)
      have hx0 := congrArg (fun f : Representation.IntertwiningMap V.ρ V.ρ ↦ f x) hone
      exact hx (by simpa using hx0.symm)
    simpa [n] using
      (Module.finrank_pos_iff.mpr
        (inferInstance : Nontrivial (Representation.IntertwiningMap V.ρ V.ρ)))
  have hpair :
      ⟪V.character, V.character⟫ =
        (n : K) := by
    -- The standard character-pairing identity computes the endomorphism-space dimension.
    simpa [n] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        K V.ρ V.ρ)
  intro hzero
  have hn_zero : (n : K) = 0 := by
    simpa [hpair] using hzero
  exact Nat.cast_ne_zero.mpr hn_pos.ne' hn_zero

/-- Helper for Exercise 12-12.2-6: once an integer multiple of a scaled irreducible character
lands in `R_K(G)`, coefficient comparison forces the denominator to divide that integer. -/
theorem denominator_dvd_of_zsmul_scaled_character_mem_characterRing_local
    (ρ : Rep K G)
    [ρ.ρ.IsIrreducible]
    (m : ℕ+)
    (d : ℕ)
    (hmem : ((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K) ∈ R[K](G)) :
    (m : ℕ) ∣ d := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  letI : FiniteDimensional K ρ := Representation.IsIrreducible.finiteDimensional_of_finite ρ.ρ
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family_local (K := K) (G := G)
  letI : Fintype ι := inferInstance
  let ρfin : Representation K G (Fin (Module.finrank K ρ) → K) :=
    finBasisRepresentation_local (K := K) (G := G) ρ.ρ
  have hρfin_irr : ρfin.IsIrreducible := by
    -- Moving to coordinates preserves irreducibility because the two representations are
    -- equivalent.
    exact isIrreducible_of_nonempty_equiv
      ⟨finBasisRepresentationEquiv_local (K := K) (G := G) ρ.ρ⟩
  have hρfin_char : ρfin.character = ρ.ρ.character := by
    ext g
    simpa [ρfin] using
      character_finBasisRepresentation_eq_local (K := K) (G := G) ρ.ρ g
  obtain ⟨i, hi⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation
      (π := π) hπ_complete ρfin hρfin_irr
  rcases hi with ⟨e⟩
  let x : R[K](G) := ⟨((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K), hmem⟩
  let c : ℤ :=
    (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i
  have hzsmul :
      ((d : ℤ) • ((((m : ℕ) : K)⁻¹) • ρ.ρ.character) : G → K) =
        ((((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) • ρ.ρ.character) := by
    ext g
    simp [zsmul_eq_mul, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
  have hpair_scaled :
      ⟪(x : G → K), (π i).character⟫ =
        (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
          ⟪(π i).character, (π i).character⟫ := by
    -- The chosen basis vector is isomorphic to `ρ`, so the pairing only records the scalar
    -- coefficient.
    calc
      ⟪(x : G → K), (π i).character⟫
          = ⟪((((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) • ρ.ρ.character),
              (π i).character⟫ := by
                simpa [x, hzsmul]
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) * ⟪ρ.ρ.character, (π i).character⟫ := by
            rw [groupFunctionPairing_smul_left]
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := by
              congr 1
              calc
                ⟪ρ.ρ.character, (π i).character⟫ = ⟪ρfin.character, (π i).character⟫ := by
                  simpa using
                    congrArg
                      (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character)
                      hρfin_char.symm
                _ = ⟪(π i).character, (π i).character⟫ := by
                  simpa [ρfin] using
                    congrArg
                      (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character)
                      (FDRep.char_iso e)
  have hpair_basis :
      ⟪(x : G → K), (π i).character⟫ =
        ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
    -- The irreducible basis expansion identifies the same pairing with the `i`-th basis
    -- coefficient.
    simpa [c] using
      basis_coefficient_pairing_eq_local
        (K := K) (π := π) hπ_pairwise hπ_complete x i
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact self_pairing_character_ne_zero_local (K := K) (V := π i)
  have hcoeff :
      ((c : ℤ) : K) = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
    -- Compare the two formulas for the same pairing and cancel the nonzero self-pairing factor.
    apply mul_right_cancel₀ hself_ne
    calc
      ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫
          = ⟪(x : G → K), (π i).character⟫ := by
              simpa using hpair_basis.symm
      _ = (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) *
            ⟪(π i).character, (π i).character⟫ := hpair_scaled
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr m.2.ne'
  have hmulK :
      ((m : ℕ) : K) * ((c : ℤ) : K) = ((d : ℤ) : K) := by
    -- Multiply by the nonzero denominator to remove the inverse.
    calc
      ((m : ℕ) : K) * ((c : ℤ) : K)
          = ((m : ℕ) : K) * (((d : ℤ) : K) * (((m : ℕ) : K)⁻¹)) := by
              rw [hcoeff]
      _ = ((d : ℤ) : K) := by
            field_simp [hmK_ne]
  have hmulZ : ((m : ℤ) * c : ℤ) = d := by
    exact_mod_cast hmulK
  have hdivZ : ((m : ℤ) : ℤ) ∣ (d : ℤ) := ⟨c, hmulZ.symm⟩
  exact Int.natCast_dvd_natCast.mp (by simpa using hdivZ)

end FieldPart

end Representation
