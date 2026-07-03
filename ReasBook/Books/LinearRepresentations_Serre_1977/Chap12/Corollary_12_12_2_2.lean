import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_4_4
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Representation

universe u

namespace Representation

open CategoryTheory

section

variable (K : Type u) (G : Type u) [Field K] [CharZero K] [Group G]

/- Domain-style sampling for this item:
* `FDRep.schurScaledCharacter` is the source-facing Chapter 12 scaled-character owner.
* `FDRep.IsSchurDenominator` is the source-facing denominator owner for those scaled characters.
* `mem_overlineCharacterRingInExtension_iff` is the canonical coefficient-extension bridge; this
  corollary should reuse it rather than restating a specialized copy.

This definition is `source-facing`: the public primitive data are a simple finite-dimensional
representation `V : FDRep K G` and its Schur denominator. Because `FDRep.IsSchurDenominator`
uses the scalars `((m : ℕ) : K)⁻¹`, the faithful LinearRepresentations_Serre_1977-style denominator notion requires
characteristic zero; quasisplitness says that every such canonical denominator is `1`. -/
/-- The group algebra `K[G]` is quasisplit if every simple finite-dimensional
`K`-representation of `G` has Schur denominator `1`. -/
class IsQuasisplitGroupAlgebra : Prop where
  schurDenominator_eq_one (V : FDRep K G) [Simple V] {m : ℕ+}
      (hm : FDRep.IsSchurDenominator V m) : m = 1

namespace FDRep

/-- In a quasisplit group algebra, every source-facing Schur denominator is `1`. -/
theorem IsSchurDenominator.eq_one
    {K : Type u} {G : Type u} [Field K] [CharZero K] [Group G]
    [IsQuasisplitGroupAlgebra K G]
    (V : FDRep K G) [Simple V] {m : ℕ+} (hm : FDRep.IsSchurDenominator V m) :
    m = 1 :=
  IsQuasisplitGroupAlgebra.schurDenominator_eq_one V hm

end FDRep

end

section

variable (K : Type u) (G : Type u) [Field K] [CharZero K] [Group G] [Finite G]

local instance instFintypeCor121222 : Fintype G := Fintype.ofFinite G

open scoped BigOperators

/-- Helper for Corollary 12-12.2-2: every `FDRep` object is canonically isomorphic to the object
rebuilt from its underlying unbundled representation. -/
private noncomputable def fdRepIsoOfRho (τ : FDRep K G) : τ ≅ FDRep.of τ.ρ :=
  Action.mkIso (Iso.refl _) fun g => by
    ext x
    rfl

/-- Helper for Corollary 12-12.2-2: precomposing with a representation equivalence identifies
intertwining spaces with the same codomain. -/
private noncomputable def intertwiningMapCongrLeft
    {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]
    {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V₁} {σ : Representation K G V₂}
    (e : ρ.Equiv σ) (τ : Representation K G W) :
    Representation.IntertwiningMap σ τ ≃ₗ[K] Representation.IntertwiningMap ρ τ :=
  { toFun := fun f ↦ f.comp e.toIntertwiningMap
    invFun := fun f ↦ f.comp e.symm.toIntertwiningMap
    left_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    right_inv := by
      intro f
      apply Representation.IntertwiningMap.ext
      ext x
      simp
    map_add' := by
      intro f g
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a f
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Corollary 12-12.2-2: intertwining maps from a direct sum are exactly families of
intertwining maps from each summand. -/
private noncomputable def directSumIntertwiningMapEquivPi
    {ι : Type*} {M : ι → Type*} [(i : ι) → AddCommMonoid (M i)] [(i : ι) → Module K (M i)]
    {W : Type*} [AddCommMonoid W] [Module K W]
    (π : ∀ i, Representation K G (M i)) (τ : Representation K G W) :
    Representation.IntertwiningMap (Representation.directSum π) τ ≃ₗ[K]
      ∀ i, Representation.IntertwiningMap (π i) τ :=
  let _ : DecidableEq ι := Classical.decEq ι
  { toFun := fun F i ↦
      ((F.toLinearMap.comp
          (DirectSum.lof K ι M i)).intertwiningMap_of_isIntertwiningMap
        (π i) τ fun g x ↦ by
          simpa [Representation.directSum] using
            congr($(F.isIntertwining' g) (DirectSum.lof K ι M i x)))
    invFun := fun f ↦
      { toLinearMap := DirectSum.toModule K ι W fun i ↦ (f i).toLinearMap
        isIntertwining' := by
          intro g
          apply DirectSum.linearMap_ext
          intro i
          ext x
          simp [Representation.directSum, Representation.IntertwiningMap.isIntertwining] }
    left_inv := by
      intro F
      apply Representation.IntertwiningMap.ext
      apply DirectSum.linearMap_ext
      intro i
      ext x
      change
        (DirectSum.toModule K ι W
          (fun j ↦ F.toLinearMap.comp (DirectSum.lof K ι M j)))
          (DirectSum.lof K ι M i x) =
        F (DirectSum.lof K ι M i x)
      simp
    right_inv := by
      intro f
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      change
        (DirectSum.toModule K ι W fun j ↦ (f j).toLinearMap)
          (DirectSum.lof K ι M i x) =
        (f i) x
      simp
    map_add' := by
      intro F H
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl
    map_smul' := by
      intro a F
      funext i
      apply Representation.IntertwiningMap.ext
      ext x
      rfl }

/-- Helper for Corollary 12-12.2-2: a nonisomorphism hypothesis on two explicit irreducible
representations forces every intertwiner between them to vanish. -/
private theorem intertwiningMap_eq_zero_of_not_isomorphic_explicit
    {V1 : Type*} [AddCommGroup V1] [Module K V1]
    {V2 : Type*} [AddCommGroup V2] [Module K V2]
    (ρ1 : Representation K G V1) [ρ1.IsIrreducible]
    (ρ2 : Representation K G V2) [ρ2.IsIrreducible]
    (f : Representation.IntertwiningMap ρ1 ρ2) (hρ : ¬ Nonempty (ρ1.Equiv ρ2)) :
    f = 0 := by
  -- A nonzero intertwiner between irreducibles would be bijective, hence a representation
  -- equivalence, contradicting the nonisomorphism hypothesis.
  simpa using
    (Representation.IsIrreducible.bijective_or_eq_zero
      (ρ := ρ1) (σ := ρ2) f).resolve_left
      (fun hf ↦ hρ ⟨f.ofBijective hf⟩)

/-- Helper for Corollary 12-12.2-2: in characteristic zero, a finite group admits a complete
pairwise nonisomorphic family of irreducible finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_simple_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep K G),
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
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : Quotient r)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep K G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
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
      intertwiningMapCongrLeft (K := K) (G := G) e τ.ρ f
    have hF_nonzero : F ≠ 0 := by
      intro hF
      exact hf_nonzero ((intertwiningMapCongrLeft (K := K) (G := G) e τ.ρ).injective hF)
    have hcomponent :
        ∃ i, (directSumIntertwiningMapEquivPi
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) ≠ 0 := by
      by_contra hnone
      have hnone' := not_exists.mp hnone
      apply hF_nonzero
      apply (directSumIntertwiningMapEquivPi
        (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ)).injective
      ext i x
      have hi0 :
          (directSumIntertwiningMapEquivPi
            (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i) = 0 := by
        simpa using hnone' i
      simp [hi0]
    rcases hcomponent with ⟨i, hi⟩
    have hi_iso : Nonempty (((σ i).toRepresentation).Equiv τ.ρ) := by
      by_contra hnot
      let ρ1 := (σ i).toRepresentation
      let ρ2 := τ.ρ
      let fi : Representation.IntertwiningMap ((σ i).toRepresentation) τ.ρ :=
        directSumIntertwiningMapEquivPi
          (K := K) (G := G) (π := fun i ↦ (σ i).toRepresentation) (τ := τ.ρ) F i
      letI : Representation.IsIrreducible ((σ i).toRepresentation) := by
        exact hσ_irr i
      have hnot' : ¬ Nonempty (Representation.Equiv ((σ i).toRepresentation) τ.ρ) := hnot
      have hnot'' : ¬ Nonempty (ρ1.Equiv ρ2) := by
        simpa [ρ1, ρ2] using hnot'
      -- Route correction: make the chosen irreducible summand explicit before applying Schur's
      -- lemma, so elaboration keeps the source and target representations fixed.
      have hfi_zero' :
          (show ρ1.IntertwiningMap ρ2 from fi) = 0 := by
        exact
          @intertwiningMap_eq_zero_of_not_isomorphic_explicit
            K G inferInstance inferInstance inferInstance inferInstance
            ↥(σ i).toSubmodule inferInstance inferInstance ↥τ inferInstance inferInstance
            ρ1 inferInstance ρ2 inferInstance
            (show ρ1.IntertwiningMap ρ2 from fi) hnot''
      have hfi_zero : fi = 0 := by
        simpa [ρ1, ρ2] using hfi_zero'
      exact hi hfi_zero
    rcases hi_iso with ⟨eτ⟩
    -- A nonzero coordinate map between irreducibles is an equivalence, hence an `FDRep` isomorphism.
    refine ⟨i, ?_⟩
    exact ⟨(fdRepIsoOfRho (K := K) (G := G) τ).trans eτ.symm.toFDRepIso⟩
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

/-- Helper for Corollary 12-12.2-2: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → K) (ψ : G → K) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : K) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Convert the inserted integer multiple into the scalar form used by the pairing API.
      have hzsmul : (a i • χ i : G → K) = (((a i : ℤ) : K) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Corollary 12-12.2-2: pairing a representation-ring element with one irreducible
basis character isolates the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Finite ι]
    (π : ι → FDRep K G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R[K](G)) (i : ι) :
    ⟪(x : G → K), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i :
        ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
  letI : Fintype ι := Fintype.ofFinite ι
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : Invertible (Nat.card G : K) := invertibleOfNonzero hcard_ne
  let b := irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx :
      ∑ j, c j • (π j).character = (x : G → K) := by
    -- Rewrite the basis expansion from `R[K](G)` into the ambient function space.
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
            -- Replace `x` by its irreducible-basis expansion.
            simpa [hx] using
              congrArg (fun ψ : G → K ↦ groupFunctionPairingOverField K ψ (π i).character)
                hx.symm
    _ = ∑ j, ((c j : ℤ) : K) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left (K := K) (G := G) (s := Finset.univ)
              (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            simp [horth hji]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim

/-- Helper for Corollary 12-12.2-2: the self-pairing of an irreducible character is nonzero. -/
private theorem self_pairing_character_ne_zero
    (V : FDRep K G) [Simple V] :
    ⟪V.character, V.character⟫ ≠ (0 : K) := by
  letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
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
      ⟪V.character, V.character⟫ = (n : K) := by
    simpa [n] using
      (Representation.groupFunctionPairingOverField_character_eq_finrank_intertwiningMap
        K V.ρ V.ρ)
  intro hzero
  have hn_zero : (n : K) = 0 := by
    simpa [hpair] using hzero
  exact Nat.cast_ne_zero.mpr hn_pos.ne' hn_zero

/-- Helper for Corollary 12-12.2-2: if `R_K(G) = \overline{R}_K(G)`, then every existing Schur
denominator witness is forced to be `1`. -/
private theorem schur_denominator_eq_one_of_characterRing_eq_overline
    (hEq : R[K](G) = R̄[K](G))
    (V : FDRep K G) [Simple V] {m : ℕ+} (hm : FDRep.IsSchurDenominator V m) :
    m = 1 := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family (K := K) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨i, hi⟩ := hπ_complete.exists_iso V (show Simple V from inferInstance)
  rcases hi with ⟨e⟩
  have hx_mem : FDRep.schurScaledCharacter V m ∈ R[K](G) := by
    simpa [hEq] using hm.1
  let x : R[K](G) := ⟨FDRep.schurScaledCharacter V m, hx_mem⟩
  let c : ℤ :=
    (irreducible_characters_basis_of_complete_family K π hπ_pairwise hπ_complete).repr x i
  have hpair_scaled :
      ⟪(x : G → K), (π i).character⟫ =
        (((m : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ := by
    -- Transport the simple character of `V` to the chosen basis element `π i`.
    calc
      ⟪(x : G → K), (π i).character⟫
          = ⟪FDRep.schurScaledCharacter V m, (π i).character⟫ := by
              rfl
      _ = ⟪(((m : ℕ) : K)⁻¹ • V.character), (π i).character⟫ := by
            rfl
      _ = (((m : ℕ) : K)⁻¹) * ⟪V.character, (π i).character⟫ := by
            rw [groupFunctionPairing_smul_left]
      _ = (((m : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ := by
            congr 1
            exact congrArg
              (fun χ : G → K ↦ groupFunctionPairingOverField K χ (π i).character)
              (FDRep.char_iso e)
  have hpair_basis :
      ⟪(x : G → K), (π i).character⟫ =
        ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫ := by
    simpa [c] using
      basis_coefficient_pairing_eq (K := K) (G := G) (π := π) hπ_pairwise hπ_complete x i
  have hself_ne : ⟪(π i).character, (π i).character⟫ ≠ (0 : K) := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact self_pairing_character_ne_zero (K := K) (G := G) (π i)
  have hcoeff :
      ((c : ℤ) : K) = (((m : ℕ) : K)⁻¹) := by
    apply mul_right_cancel₀ hself_ne
    calc
      ((c : ℤ) : K) * ⟪(π i).character, (π i).character⟫
          = ⟪(x : G → K), (π i).character⟫ := by
              simpa using hpair_basis.symm
      _ = (((m : ℕ) : K)⁻¹) * ⟪(π i).character, (π i).character⟫ := hpair_scaled
  have hmK_ne : ((m : ℕ) : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr m.2.ne'
  have hmulK : ((m : ℕ) : K) * ((c : ℤ) : K) = 1 := by
    -- Multiply by the nonzero denominator to eliminate the inverse.
    exact
      calc
        ((m : ℕ) : K) * ((c : ℤ) : K)
            = ((m : ℕ) : K) * (((m : ℕ) : K)⁻¹) := by rw [hcoeff]
        _ = 1 := by field_simp [hmK_ne]
  have hmulZ : ((m : ℤ) * c : ℤ) = 1 := by
    exact_mod_cast hmulK
  have hmNat : (m : ℕ) = 1 := by
    have hm_dvd_one_int : ((m : ℤ) : ℤ) ∣ (1 : ℤ) := ⟨c, hmulZ.symm⟩
    have hm_dvd_one_nat : (m : ℕ) ∣ 1 := by
      exact Int.natCast_dvd_natCast.mp (by simpa using hm_dvd_one_int)
    exact Nat.dvd_one.mp hm_dvd_one_nat
  exact Subtype.ext hmNat

/-- Helper for Corollary 12-12.2-2: multiplying a Schur-scaled character by its denominator
recovers the original character. -/
private theorem zsmul_schurScaledCharacter_eq_character
    (V : FDRep K G) (n : ℕ+) :
    ((n : ℤ) • FDRep.schurScaledCharacter V n : G → K) = V.character := by
  -- Expand the scaled character pointwise and cancel the inverse denominator.
  ext g
  simp [FDRep.schurScaledCharacter, zsmul_eq_mul]

/-- Helper for Corollary 12-12.2-2: every simple finite-dimensional representation should admit a
Schur denominator. -/
private theorem exists_schur_denominator_of_simple
    (V : FDRep K G) [Simple V] :
    ∃ m : ℕ+, FDRep.IsSchurDenominator V m := by
  classical
  -- Route correction: finite relative index gives an admissible multiple, but not an upper bound
  -- on all admissible denominators. The right source-faithful route is to choose a `ℤ`-basis of
  -- `R̄[K](G)` and bound every denominator by divisibility of one nonzero coordinate of `χ_V`.
  let S : Submodule ℤ (G → K) := (R̄[K](G)).toSubmodule
  let x : S :=
    ⟨V.character,
      characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K V)⟩
  have hx_ne : x ≠ 0 := by
    intro hx
    have hchar : (V.character : G → K) = 0 := by
      simpa [x] using congrArg (fun z : S ↦ (z : G → K)) hx
    have hpair_zero : ⟪V.character, V.character⟫ = (0 : K) := by
      simp [hchar, Representation.groupFunctionPairingOverField]
    exact self_pairing_character_ne_zero (K := K) (G := G) V hpair_zero
  have hS_fg : S.FG := by
    let ιK : (G → K) →ₗ[ℤ] G → AlgebraicClosure K :=
      ((IsScalarTower.toAlgHom ℤ K (AlgebraicClosure K)).compLeft G).toLinearMap
    have hιK_inj : Function.Injective ιK := by
      intro χ ψ hχψ
      ext g
      have hg : ιK χ g = ιK ψ g := congrFun hχψ g
      change algebraMap K (AlgebraicClosure K) (χ g) =
        algebraMap K (AlgebraicClosure K) (ψ g) at hg
      exact FaithfulSMul.algebraMap_injective K (AlgebraicClosure K) hg
    have hmap :
        S.map ιK = (overlineCharacterRingOverField K G).toSubmodule := by
      ext χ
      constructor
      · rintro ⟨χK, hχK, rfl⟩
        exact ⟨χK, hχK, rfl⟩
      · rintro ⟨χK, hχK, rfl⟩
        exact ⟨χK, hχK, rfl⟩
    have htarget_fg : (overlineCharacterRingOverField K G).toSubmodule.FG := by
      obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
        exists_complete_pairwise_nonisomorphic_simple_family
          (K := AlgebraicClosure K) (G := G)
      letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
      letI : Fintype ι := Fintype.ofFinite ι
      let b :=
        irreducible_characters_basis_of_complete_family
          (AlgebraicClosure K) π hπ_pairwise hπ_complete
      letI : Module.Finite ℤ (R[AlgebraicClosure K](G)) := Module.Finite.of_basis b
      have hR_fg : (R[AlgebraicClosure K](G)).toSubmodule.FG := by
        simpa using (Submodule.FG.of_finite : (R[AlgebraicClosure K](G)).toSubmodule.FG)
      exact
        Submodule.FG.of_le hR_fg
          (fun χ hχ ↦ (mem_overlineCharacterRingOverField_iff (K := K) (G := G) χ).1 hχ |>.1)
    exact Submodule.fg_of_fg_map_injective ιK hιK_inj (by simpa [hmap] using htarget_fg)
  letI : Module.Finite ℤ S := by
    exact Module.Finite.of_fg hS_fg
  letI : Module.IsTorsionFree ℤ (G → K) := by
    infer_instance
  letI : Module.IsTorsionFree ℤ S := Submodule.instIsTorsionFree (p := S)
  obtain ⟨d, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := S)
  have hrepr_ne : b.repr x ≠ 0 := by
    intro h
    apply hx_ne
    apply b.repr.injective
    simpa using h
  have hcoord_exists : ∃ i : Fin d, b.repr x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr_ne
    ext i
    exact h i
  rcases hcoord_exists with ⟨i0, hi0⟩
  let B : ℕ := ∑ j : Fin d, Int.natAbs (b.repr x j)
  have hcoord_le_B : Int.natAbs (b.repr x i0) ≤ B := by
    simpa [B] using
      (Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin d ↦ Int.natAbs (b.repr x j))
        (fun j _ ↦ Nat.zero_le _)
        (by simp : i0 ∈ (Finset.univ : Finset (Fin d))))
  have hB_pos : 0 < B := by
    exact lt_of_lt_of_le (Int.natAbs_pos.mpr hi0) hcoord_le_B
  have hbounded :
      ∀ n : ℕ+, FDRep.schurScaledCharacter V n ∈ R̄[K](G) → (n : ℕ) ≤ B := by
    intro n hn
    let y : S := ⟨FDRep.schurScaledCharacter V n, hn⟩
    have hxy : ((n : ℤ) • y) = x := by
      -- Rewrite inside the lattice using the standalone denominator-cancellation identity.
      ext g
      simp [x, y, zsmul_schurScaledCharacter_eq_character (K := K) (G := G) V n]
    have hdiv : ((n : ℤ) : ℤ) ∣ b.repr x i0 := by
      -- Passing to the chosen coordinate turns the recovery identity into a divisibility fact.
      refine ⟨b.repr y i0, ?_⟩
      have hrepr := congrArg (fun z : S ↦ b.repr z i0) hxy
      simpa [zsmul_eq_mul, mul_comm] using hrepr.symm
    rcases hdiv with ⟨k, hk⟩
    have hk_ne : k ≠ 0 := by
      intro hk0
      apply hi0
      simpa [hk0] using hk
    have hn_le_coord : (n : ℕ) ≤ Int.natAbs (b.repr x i0) := by
      have hk_one : 1 ≤ Int.natAbs k := Nat.succ_le_of_lt (Int.natAbs_pos.mpr hk_ne)
      calc
        (n : ℕ) = (n : ℕ) * 1 := by simp
        _ ≤ (n : ℕ) * Int.natAbs k := by
          exact Nat.mul_le_mul_left _ hk_one
        _ = Int.natAbs ((n : ℤ) * k) := by
          simp [Int.natAbs_mul]
        _ = Int.natAbs (b.repr x i0) := by
          rw [hk]
    exact hn_le_coord.trans hcoord_le_B
  let P : ℕ → Prop := fun n ↦
    ∃ hn : 0 < n, FDRep.schurScaledCharacter V ⟨n, hn⟩ ∈ R̄[K](G)
  have hP_one : P 1 := by
    -- The unscaled character is always admissible because `χ_V ∈ R[K](G) ⊆ R̄[K](G)`.
    refine ⟨zero_lt_one, ?_⟩
    simpa [FDRep.schurScaledCharacter] using
      characterRingOverField_le_overlineCharacterRing K G
        (FDRep.character_mem_characterRingOverField K V)
  let mNat := Nat.findGreatest P B
  have hm_prop : P mNat := by
    exact Nat.findGreatest_spec (Nat.succ_le_of_lt hB_pos) hP_one
  rcases hm_prop with ⟨hm_pos, hm_mem⟩
  refine ⟨⟨mNat, hm_pos⟩, ?_, ?_⟩
  · -- The chosen `findGreatest` value is itself an admissible denominator.
    simpa using hm_mem
  · intro n hn
    have hPn : P (n : ℕ) := by
      exact ⟨n.2, by simpa using hn⟩
    have hn_le_B : (n : ℕ) ≤ B := hbounded n hn
    -- Maximality is now exactly the universal property of `Nat.findGreatest`.
    exact Nat.le_findGreatest hn_le_B hPn

/-- Helper for Corollary 12-12.2-2: quasisplitness implies the intrinsic character ring already
lies in the honest representation ring. -/
private theorem overlineCharacterRing_le_characterRing_of_isQuasisplit
    [IsQuasisplitGroupAlgebra K G] :
    R̄[K](G) ≤ R[K](G) := by
  have hcard_ne : (Nat.card G : K) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  letI : NeZero (Nat.card G : K) := ⟨hcard_ne⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family (K := K) (G := G)
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  choose m hdenom using
    fun i ↦ exists_schur_denominator_of_simple (K := K) (G := G) (π i)
  let b :=
    scaled_irreducible_characters_basis_of_complete_family π hπ_pairwise hπ_complete m hdenom
  intro χ hχ
  let x : R̄[K](G) := ⟨χ, hχ⟩
  let c := b.repr x
  have hx :
      ∑ i, c i • ((b i : R̄[K](G)) : G → K) = χ := by
    -- Expand `x` in the scaled-character basis and forget the subtype wrapper.
    simpa [b, c, x] using
      congrArg (fun z : R̄[K](G) ↦ (z : G → K)) (b.sum_repr x)
  rw [← hx]
  change ∑ i, c i • ((b i : R̄[K](G)) : G → K) ∈ (R[K](G)).toSubmodule
  refine Submodule.sum_mem _ ?_
  intro i _
  have hm_one : m i = 1 := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact FDRep.IsSchurDenominator.eq_one (V := π i) (hdenom i)
  have hb_char :
      ((b i : R̄[K](G)) : G → K) = (π i).character := by
    -- Quasisplitness removes the denominator from the scaled basis vector.
    calc
      ((b i : R̄[K](G)) : G → K) = FDRep.schurScaledCharacter (π i) (m i) := by
        simpa [b] using
          congrArg (fun z : R̄[K](G) ↦ (z : G → K))
            (scaled_irreducible_characters_basis_of_complete_family_apply
              π hπ_pairwise hπ_complete m hdenom i)
      _ = (π i).character := by
            simp [FDRep.schurScaledCharacter, hm_one]
  have hchar_mem : (π i).character ∈ (R[K](G)).toSubmodule := by
    letI : Simple (π i) := hπ_complete.isSimple i
    exact FDRep.character_mem_characterRingOverField K (π i)
  exact Submodule.smul_mem _ _ (by simpa [hb_char] using hchar_mem)

-- Proof sketch: choose a complete pairwise nonisomorphic family of irreducible
-- `K`-representations. Proposition `12-12.2-1` identifies a `ℤ`-basis of the intrinsic owner
-- `\overline{R}_K(G)` with the scaled characters `χᵢ / mᵢ`, while `R_K(G)` is generated by the
-- unscaled characters `χᵢ`. These two lattices coincide exactly when every scaling integer `mᵢ`
-- equals `1`, which is precisely the quasisplit condition on `K[G]`.
/-- Corollary 12-12.2-2: the group algebra `K[G]` is quasisplit if and only if LinearRepresentations_Serre_1977's
representation ring already equals `\overline{R}_K(G)`. -/
theorem
    characterRing_eq_overlineCharacterRing_iff_isQuasisplitGroupAlgebra :
    R[K](G) = R̄[K](G) ↔
      IsQuasisplitGroupAlgebra K G := by
  constructor
  · intro hEq
    -- Equality of the two lattices forces every denominator witness to collapse to `1`.
    refine ⟨?_⟩
    intro V _ m hm
    exact schur_denominator_eq_one_of_characterRing_eq_overline
      (K := K) (G := G) hEq V hm
  · intro hquasi
    -- Route correction: the reverse implication is reduced to the inclusion `R̄[K](G) ≤ R[K](G)`
    -- once the denominator-existence lemma is supplied.
    letI : IsQuasisplitGroupAlgebra K G := hquasi
    exact le_antisymm
      (characterRingOverField_le_overlineCharacterRing K G)
      (overlineCharacterRing_le_characterRing_of_isQuasisplit (K := K) (G := G))

end

end Representation
