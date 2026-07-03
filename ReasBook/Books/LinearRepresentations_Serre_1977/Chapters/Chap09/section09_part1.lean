import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_9_9_1_1 (from Chap09) -/
noncomputable section

namespace Representation

open CategoryTheory

section CharacterRing

variable {G : Type} [Group G]

scoped[Representation] notation:max "R(" G ")" => R[ℂ](G)

open scoped Representation

end CharacterRing

section

variable {G : Type} [Group G] [Finite G]

open scoped Representation
open scoped BigOperators

local instance instFintypeGExercise9911 : Fintype G := Fintype.ofFinite G

variable (φ : G → ℝ)
local notation "φℂ" => Complex.ofReal ∘ φ

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's Chapter 9 positivity criterion for an integral virtual character to be
--   an actual character.
-- * core/canonical: the pairing owner `⟪-, -⟫` and the character-ring owner `R(G)`.
-- * bridge/view: the canonical complex-valued view `φℂ` of the real-valued function `φ`.
--
-- Primitive data: the real-valued function `φ` together with the pairing and sign hypotheses.
-- Derived API: realization of `φℂ` as a character in `FDRep ℂ G`.

/-- Helper for Exercise 9-9.1-1: the real part of a character value is bounded above by the value
at the identity. -/
private lemma character_re_le_character_one (V : FDRep ℂ G) (s : G) :
    Complex.re (V.character s) ≤ (V.character 1).re := by
  -- Compare the real part with the norm, then use the Chapter 6 character bound.
  have hnorm : ‖V.character s‖ ≤ Module.finrank ℂ V :=
    character_norm_le_char_one V.ρ s (isOfFinOrder_of_finite s)
  calc
    Complex.re (V.character s) ≤ ‖V.character s‖ := Complex.re_le_norm _
    _ ≤ Module.finrank ℂ V := hnorm
    _ = (V.character 1).re := by
          rw [FDRep.char_one]
          simp

/-- Helper for Exercise 9-9.1-1: a finite group admits a complete pairwise nonisomorphic family
of irreducible complex finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    -- Distinct quotient classes cannot label isomorphic regular summands.
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
    -- Multiplicity of one irreducible class in the regular representation equals its degree.
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
          Module.finrank ℂ (π q) := by
      letI : Representation.IsIrreducible (π q).ρ := by
        exact FDRep.isIrreducible_of_simple (π q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank ℂ (π q) ^ 2 := by
    -- Every regular summand inside one isomorphism class has the same degree.
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank ℂ (π q) := by
            simp
      _ = Module.finrank ℂ (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover : Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    -- Every irreducible regular summand lies in the quotient class determined by its own label.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    -- Summing the dimensions of the internal decomposition recovers the regular dimension.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing ℂ (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) = Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
            exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                simpa [dimσ] using
                  (Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule))
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    -- The quotient classes partition the regular summands, so the square-degree sum is `|G|`.
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    -- The Chapter 2 square-degree criterion upgrades the quotient family to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 9-9.1-1: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : ℂ) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Convert the inserted integer multiple into the scalar form used by the pairing API.
      have hzsmul : (a i • χ i : G → ℂ) = (((a i : ℤ) : ℂ) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 9-9.1-1: pairing an element of `R(G)` with an irreducible basis character
recovers the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(G)) (i : ι) :
    ⟪(x : G → ℂ), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : G → ℂ) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  have horth : Pairwise fun j k ↦ ⟪(π j).character, (π k).character⟫ = (0 : ℂ) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ j, ⟪(π j).character, (π j).character⟫ = (1 : ℂ) := by
    intro j
    letI : Simple (π j) := hπ_complete.isSimple j
    have hself : Nonempty (π j ≅ π j) := ⟨Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π j) (π j))
  calc
    ⟪(x : G → ℂ), (π i).character⟫ = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
      -- Replace `x` by its irreducible-basis expansion.
      simpa [hx] using
        congrArg (fun ψ : G → ℂ ↦ groupFunctionPairingOverField ℂ ψ (π i).character) hx.symm
    _ = ∑ j, ((c j : ℤ) : ℂ) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left (s := Finset.univ)
              (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : ℂ) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            rw [horth hji, mul_zero]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    _ = (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
          simp [b, c, hdiag]

omit [Finite G] in
/-- Helper for Exercise 9-9.1-1: every finite sum of honest complex characters is again the
character of a finite-dimensional complex representation. -/
private theorem exists_fdRep_with_character_eq_sum
    {ι : Type*} (s : Finset ι) (π : ι → FDRep ℂ G) :
    ∃ τ : FDRep ℂ G, τ.character = s.sum fun i ↦ (π i).character := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨FDRep.of (Representation.trivial ℂ G (Fin 0 → ℂ)), ?_⟩
      -- The trivial action on the zero-dimensional space has zero trace everywhere.
      ext g
      simp [FDRep.character, Representation.trivial]
  | insert i s hi ih =>
      rcases ih with ⟨τ, hτ⟩
      refine ⟨FDRep.of (Representation.prod (π i).ρ τ.ρ), ?_⟩
      -- Add one more summand and use the binary direct-sum character formula.
      calc
        (FDRep.of (Representation.prod (π i).ρ τ.ρ)).character =
            (Representation.prod (π i).ρ τ.ρ).character := rfl
        _ = Representation.character (π i).ρ + Representation.character τ.ρ := by
            exact Representation.char_prod (π i).ρ τ.ρ
        _ = (π i).character + τ.character := rfl
        _ = (π i).character + s.sum (fun j ↦ (π j).character) := by
            rw [hτ]
        _ = (insert i s).sum (fun j ↦ (π j).character) := by
            rw [Finset.sum_insert hi]

omit [Finite G] in
/-- Helper for Exercise 9-9.1-1: a finite nonnegative integral combination of irreducible complex
characters is the character of an honest finite-dimensional complex representation. -/
private theorem exists_fdRep_with_character_eq_repr_sum
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G) (c : ι → ℤ) (hc : ∀ i, 0 ≤ c i) :
    ∃ τ : FDRep ℂ G, τ.character = ∑ i, c i • (π i).character := by
  let n : ι → ℕ := fun i ↦ Int.toNat (c i)
  let π' : (Σ i, Fin (n i)) → FDRep ℂ G := fun j ↦ π j.1
  obtain ⟨τ, hτ⟩ :=
    exists_fdRep_with_character_eq_sum (s := Finset.univ) π'
  refine ⟨τ, ?_⟩
  -- Replicate each irreducible summand `c i` times and collapse the sigma-indexed sum.
  calc
    τ.character = ∑ j : Σ i, Fin (n i), (π' j).character := hτ
    _ = ∑ i, ∑ _ : Fin (n i), (π i).character := by
          simpa [π'] using
            (Fintype.sum_sigma (fun j : Σ i, Fin (n i) ↦ (π' j).character))
    _ = ∑ i, n i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simp [n]
    _ = ∑ i, c i • (π i).character := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [show c i = Int.ofNat (n i) by
            simpa [n] using (Int.toNat_of_nonneg (hc i)).symm]
          simp

-- Proof sketch: expand the pairing as the averaged sum
-- `|G|⁻¹ ∑ s, φ(s⁻¹) χ(s)`, compare each summand with `φ(s⁻¹) χ(1)` using the source hint and the
-- assumption `φ(s) ≤ 0` for `s ≠ 1`, and then use `⟪φℂ, 1⟫ = 0` to rewrite the resulting sum.
/-- A real-valued function on a finite group with zero pairing against the unit character and
nonpositive values away from the identity has nonnegative real pairing with every character. -/
theorem groupFunctionPairing_character_re_nonneg_of_pairing_one_eq_zero_of_nonpos_off_identity
    (hpair : ⟪φℂ, (1 : G → ℂ)⟫ = 0)
    (hneg : ∀ s : G, s ≠ 1 → φ s ≤ 0)
    (V : FDRep ℂ G) :
    0 ≤ (⟪φℂ, V.character⟫).re := by
  have hterm :
      ∀ s : G,
        Complex.re (φℂ s * V.character 1) ≤ Complex.re (φℂ s * V.character s⁻¹) := by
    intro s
    by_cases hs : s = 1
    · -- At the identity both comparison terms are equal.
      subst hs
      simp
    · -- Away from the identity, `φ(s) ≤ 0` reverses the real-part inequality for the character.
      have hφ : φ s ≤ 0 := hneg s hs
      have hre : Complex.re (V.character s⁻¹) ≤ (V.character 1).re :=
        character_re_le_character_one V s⁻¹
      have hmul : φ s * (V.character 1).re ≤ φ s * (V.character s⁻¹).re := by
        nlinarith
      simpa [Complex.re_ofReal_mul] using hmul
  have hsum :
      ∑ s : G, Complex.re (φℂ s * V.character 1) ≤
        ∑ s : G, Complex.re (φℂ s * V.character s⁻¹) := by
    -- Sum the pointwise comparison from the source hint.
    exact Finset.sum_le_sum fun s _ ↦ hterm s
  have hconst_sum_zero :
      (Nat.card G : ℝ)⁻¹ * ∑ s : G, Complex.re (φℂ s * V.character 1) = 0 := by
    have hconst_fun : (fun _ : G ↦ V.character 1) = (V.character 1) • (1 : G → ℂ) := by
      ext x
      simp
    have hconstpair : ⟪φℂ, fun _ : G ↦ V.character 1⟫ = 0 := by
      -- Pull the constant character value `χ(1)` out of the pairing and use `⟪φ, 1⟫ = 0`.
      calc
        ⟪φℂ, fun _ : G ↦ V.character 1⟫ = ⟪φℂ, (V.character 1) • (1 : G → ℂ)⟫ := by
          rw [hconst_fun]
        _ = V.character 1 * ⟪φℂ, (1 : G → ℂ)⟫ :=
              Representation.groupFunctionPairing_smul_right (V.character 1) φℂ (1 : G → ℂ)
        _ = 0 := by
              rw [hpair, mul_zero]
    rw [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply] at hconstpair
    have hconst_real := congrArg Complex.re hconstpair
    simpa [map_sum, Complex.re_ofReal_mul] using hconst_real
  have hsum_nonneg :
      0 ≤ (Nat.card G : ℝ)⁻¹ * ∑ s : G, Complex.re (φℂ s * V.character s⁻¹) := by
    have hcard_nonneg : 0 ≤ (Nat.card G : ℝ)⁻¹ := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_left hsum hcard_nonneg
    calc
      0 = (Nat.card G : ℝ)⁻¹ * ∑ s : G, Complex.re (φℂ s * V.character 1) :=
        hconst_sum_zero.symm
      _ ≤ (Nat.card G : ℝ)⁻¹ * ∑ s : G, Complex.re (φℂ s * V.character s⁻¹) := hscaled
  -- Rewrite the pairing back into the averaged sum form.
  simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply,
    map_sum, Complex.re_ofReal_mul] using hsum_nonneg

-- Proof sketch: write the given function as an integral linear combination of irreducible
-- characters using `hR`. Pairing with each irreducible character has nonnegative real part by the
-- previous theorem, and the pairing with the unit character is zero. As in LinearRepresentations_Serre_1977's argument, this
-- forces all coefficients to be nonnegative, so the function is an actual character.
/-- Exercise 9-9.1-1: if a real-valued function on a finite group has zero pairing with the unit
character, is nonpositive away from the identity, and belongs to LinearRepresentations_Serre_1977's character ring `R(G)`,
then it is the character of a finite-dimensional complex representation. -/
theorem exists_fdRep_character_eq_of_mem_characterRing_of_pairing_one_eq_zero_of_nonpos_off_identity
    (hpair : ⟪φℂ, (1 : G → ℂ)⟫ = 0)
    (hneg : ∀ s : G, s ≠ 1 → φ s ≤ 0)
    (hR : φℂ ∈ R(G)) :
    ∃ V : FDRep ℂ G, V.character = φℂ := by
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let x : R(G) := ⟨φℂ, hR⟩
  let c := b.repr x
  have hc_nonneg : ∀ i, 0 ≤ c i := by
    intro i
    -- Pairing with the `i`th irreducible basis character reads off the coefficient `c i`.
    have hcoeff :
        ⟪φℂ, (π i).character⟫ = ((c i : ℤ) : ℂ) := by
      simpa [b, c, x] using basis_coefficient_pairing_eq (π := π) hπ_pairwise hπ_complete x i
    have hpair_nonneg : 0 ≤ (⟪φℂ, (π i).character⟫).re :=
      groupFunctionPairing_character_re_nonneg_of_pairing_one_eq_zero_of_nonpos_off_identity
        φ hpair hneg (π i)
    have hreal : 0 ≤ (c i : ℝ) := by
      simpa [hcoeff] using hpair_nonneg
    exact_mod_cast hreal
  obtain ⟨V, hV⟩ := exists_fdRep_with_character_eq_repr_sum (π := π) c hc_nonneg
  have hx :
      ∑ i, c i • (π i).character = (x : G → ℂ) := by
    -- Collapse the irreducible-basis expansion of `x` back to the given class function.
    simpa [b, c, x, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  refine ⟨V, ?_⟩
  calc
    V.character = ∑ i, c i • (π i).character := hV
    _ = x := hx
    _ = φℂ := rfl

end

end Representation

/-! ### Exercise_9_9_1_2 (from Chap09) -/
open CategoryTheory
open scoped Representation
open scoped BigOperators

noncomputable section

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

local instance : Fintype G := Fintype.ofFinite G

-- Source/core/bridge triage:
-- * source-facing: LinearRepresentations_Serre_1977's irreducibility criterion for a virtual complex character `χ ∈ R(G)`.
-- * core/canonical: the bundled owner `FDRep ℂ G` together with the Chapter 2 owner theorem
--   `self_character_pairing_eq_one_iff_isIrreducible`.
-- * bridge/view: the canonical coercion from `R(G)` to complex-valued functions on `G`, and
--   Exercise
--   `9-9.1-1`, which upgrades the numerical hypotheses on `χ` to an actual finite-dimensional
--   character.
--
-- Primitive data: `χ : R(G)` and the numerical conditions on its self-pairing and value at the
-- identity.
-- Derived API: existence of a simple object of `FDRep ℂ G` whose character is `χ`.

-- Proof sketch: for the forward implication, an irreducible character belongs to `R(G)`
-- by definition, its self-pairing is `1` by Theorem `2-2.3-5`, and its value at `1` is the
-- nonnegative degree of the representation via `Representation.char_one`. For the reverse
-- implication, use
-- the fact that `χ` already lives in `R(G)` together with the nonnegativity of `χ 1`
-- and Exercise `9-9.1-1` to realize `χ` as an actual finite-dimensional character, then apply
-- the finite-dimensional irreducibility criterion to that `FDRep` object.
/-- Helper for Exercise 9-9.1-2: a finite group admits a complete pairwise nonisomorphic family
of irreducible complex finite-dimensional representations. -/
private theorem exists_complete_pairwise_nonisomorphic_irreducible_family :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  letI : NeZero (Nat.card G : ℂ) := ⟨by
    exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun j ↦ (σ j).toSubmodule) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hσ_indep hσ_top
  let r : Setoid κ :=
    { r := fun i j ↦ Nonempty ((σ i).toRepresentation.Equiv (σ j).toRepresentation)
      iseqv :=
        ⟨fun i ↦ ⟨Representation.Equiv.refl _⟩,
          fun {i j} hij ↦ by
            rcases hij with ⟨e⟩
            exact ⟨e.symm⟩,
          fun {i j l} hij hjl ↦ by
            rcases hij with ⟨eij⟩
            rcases hjl with ⟨ejl⟩
            exact ⟨eij.trans ejl⟩⟩ }
  let ι : Type := Quotient r
  letI : Finite ι := by
    refine Finite.of_surjective (fun i : κ ↦ (⟦i⟧ : ι)) ?_
    intro q
    exact ⟨Quotient.out q, Quotient.out_eq q⟩
  letI : Fintype ι := Fintype.ofFinite ι
  let π : ι → FDRep ℂ G := fun q ↦ FDRep.of ((σ (Quotient.out q)).toRepresentation)
  have hπ_pairwise : PairwiseNonisomorphic π := by
    intro q q' hqq' hIso
    rcases hIso with ⟨e⟩
    have hclasses : (⟦Quotient.out q⟧ : ι) = (⟦Quotient.out q'⟧ : ι) := by
      apply Quotient.sound
      exact ⟨Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e)⟩
    apply hqq'
    calc
      q = (⟦Quotient.out q⟧ : ι) := (Quotient.out_eq q).symm
      _ = (⟦Quotient.out q'⟧ : ι) := hclasses
      _ = q' := Quotient.out_eq q'
  have hπ_simple (q : ι) : Simple (π q) := by
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    -- Distinct quotient classes cannot label isomorphic regular summands.
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
    -- Multiplicity of one irreducible class in the regular representation equals its degree.
    have hmult :
        Nat.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } =
          Module.finrank ℂ (π q) := by
      letI : Representation.IsIrreducible (π q).ρ := by
        exact FDRep.isIrreducible_of_simple (π q)
      simpa using
        leftRegular_irreducible_multiplicity_eq_finrank σ hinternal hσ_irr (π q).ρ
          inferInstance
    have hcard :
        Fintype.card { j // Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) } = (S q).card := by
      rw [show S q = Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ) by
        rfl]
      rw [Fintype.card_of_subtype
        (Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ))]
      intro j
      simp
    exact hcard.symm.trans <| by
      simpa [Nat.card_eq_fintype_card] using hmult
  have hS_sum (q : ι) : Finset.sum (S q) dimσ = Module.finrank ℂ (π q) ^ 2 := by
    -- Every regular summand inside one isomorphism class has the same degree.
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank ℂ (π q) := by
            simp
      _ = Module.finrank ℂ (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover : Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
    -- Every irreducible regular summand lies in the quotient class determined by its own label.
    apply Finset.ext
    intro j
    constructor
    · intro _
      simp
    · intro hj
      have hj_mem : j ∈ S (⟦j⟧ : ι) := by
        refine Finset.mem_filter.mpr ?_
        constructor
        · simp
        · rcases Quotient.exact (Quotient.out_eq (⟦j⟧ : ι)) with ⟨e⟩
          exact ⟨e.symm⟩
      exact Finset.mem_biUnion.mpr ⟨(⟦j⟧ : ι), Finset.mem_univ _, hj_mem⟩
  have htotal_eq_card : Finset.sum (Finset.univ : Finset κ) dimσ = Nat.card G := by
    -- Summing the dimensions of the internal decomposition recovers the regular dimension.
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing ℂ (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) = Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
            exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                simpa [dimσ] using
                  (Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule))
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
    -- The quotient classes partition the regular summands, so the square-degree sum is `|G|`.
    calc
      ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = ∑ q : ι, Finset.sum (S q) dimσ := by
        refine Finset.sum_congr rfl fun q _ ↦ (hS_sum q).symm
      _ = Finset.sum (Finset.univ.biUnion S) dimσ := by
            symm
            exact Finset.sum_biUnion fun q _ q' _ hqq' ↦ hS_disjoint hqq'
      _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
            rw [hcover]
      _ = Nat.card G := htotal_eq_card
  have hπ_complete : IsCompleteIrreducibleFamily π := by
    -- The Chapter 2 square-degree criterion upgrades the quotient family to completeness.
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 9-9.1-2: the normalized pairing is additive over finite integer linear
combinations in its left argument. -/
private theorem groupFunctionPairing_sum_zsmul_left
    {ι : Type*} (s : Finset ι) (a : ι → ℤ) (χ : ι → G → ℂ) (ψ : G → ℂ) :
    ⟪∑ j ∈ s, a j • χ j, ψ⟫ = ∑ j ∈ s, ((a j : ℤ) : ℂ) * ⟪χ j, ψ⟫ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty linear combination pairs to zero.
      simp [Representation.groupFunctionPairingOverField]
  | insert i s hi ih =>
      -- Rewrite the integer multiple as complex scalar multiplication before applying linearity.
      have hzsmul : (a i • χ i : G → ℂ) = (((a i : ℤ) : ℂ) • χ i) := by
        ext g
        simp [zsmul_eq_mul, smul_eq_mul]
      rw [Finset.sum_insert hi, groupFunctionPairing_add_left, hzsmul,
        groupFunctionPairing_smul_left, ih, Finset.sum_insert hi]

/-- Helper for Exercise 9-9.1-2: pairing an element of `R(G)` with an irreducible basis character
recovers the corresponding basis coefficient. -/
private theorem basis_coefficient_pairing_eq
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(G)) (i : ι) :
    ⟪(x : G → ℂ), (π i).character⟫ =
      (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast Nat.card_pos.ne')
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : G → ℂ) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  have horth : Pairwise fun j k ↦ ⟪(π j).character, (π k).character⟫ = (0 : ℂ) :=
    irreducible_characters_pairwise_orthogonal_of_pairwise_nonisomorphic
      ℂ π hπ_complete.isSimple hπ_pairwise
  have hdiag : ∀ j, ⟪(π j).character, (π j).character⟫ = (1 : ℂ) := by
    intro j
    letI : Simple (π j) := hπ_complete.isSimple j
    have hself : Nonempty (π j ≅ π j) := ⟨Iso.refl _⟩
    simpa [Representation.groupFunctionPairing_eq_card_inv_sum_apply_mul_inv_apply, hself] using
      (FDRep.char_orthonormal (π j) (π j))
  calc
    ⟪(x : G → ℂ), (π i).character⟫ = ⟪∑ j, c j • (π j).character, (π i).character⟫ := by
      -- Replace `x` by its irreducible-basis expansion.
      rw [hx]
    _ = ∑ j, ((c j : ℤ) : ℂ) * ⟪(π j).character, (π i).character⟫ := by
          -- Expand the pairing termwise across the finite sum.
          simpa [c] using
            groupFunctionPairing_sum_zsmul_left (s := Finset.univ)
              (a := c) (χ := fun j ↦ (π j).character) (ψ := (π i).character)
    _ = ((c i : ℤ) : ℂ) * ⟪(π i).character, (π i).character⟫ := by
          -- Orthogonality kills every off-diagonal basis term.
          refine Finset.sum_eq_single i ?_ ?_
          · intro j _ hji
            rw [horth hji, mul_zero]
          · intro hi
            exact (hi (Finset.mem_univ i)).elim
    _ = (((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i :
        ℤ) : ℂ) := by
          simp [b, c, hdiag]

/-- Helper for Exercise 9-9.1-2: self-pairing `1` forces the irreducible-basis coefficients of an
element of `R(G)` to have square sum `1`. -/
private lemma repr_square_sum_eq_one_of_self_pairing_eq_one
    {ι : Type*} [Fintype ι]
    (π : ι → FDRep ℂ G)
    (hπ_pairwise : PairwiseNonisomorphic π)
    (hπ_complete : IsCompleteIrreducibleFamily π)
    (x : R(G))
    (hpair : ⟪(x : G → ℂ), x⟫ = (1 : ℂ)) :
    ∑ i, ((irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete).repr x i)^2
      = 1 := by
  let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
  let c := b.repr x
  have hx : ∑ j, c j • (π j).character = (x : G → ℂ) := by
    -- Rewrite the basis expansion of `x` into the ambient function space.
    simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
      FDRep.irreducibleCharacter_apply] using
      congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr x)
  have hcomplex :
      (((∑ i, (c i)^2 : ℤ) : ℂ)) = ⟪(x : G → ℂ), x⟫ := by
    calc
      (((∑ i, (c i)^2 : ℤ) : ℂ))
          = ∑ i, ((c i : ℤ) : ℂ) * (((c i : ℤ) : ℂ)) := by
              -- Convert the integer square sum into the ambient complex sum.
              simp [pow_two]
      _ = ∑ i, ((c i : ℤ) : ℂ) * ⟪(π i).character, (x : G → ℂ)⟫ := by
            -- Each coefficient is recovered by pairing with the corresponding basis character.
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [groupFunctionPairing_comm, basis_coefficient_pairing_eq (π := π) hπ_pairwise
              hπ_complete x i]
      _ = ⟪∑ i, c i • (π i).character, (x : G → ℂ)⟫ := by
            -- Reassemble the coefficient sum into a single pairing.
            symm
            simpa [c] using
              groupFunctionPairing_sum_zsmul_left (s := Finset.univ)
                (a := c) (χ := fun i ↦ (π i).character) (ψ := (x : G → ℂ))
      _ = ⟪(x : G → ℂ), x⟫ := by
            rw [hx]
  have hcomplex_one : (((∑ i, (c i)^2 : ℤ) : ℂ)) = (1 : ℂ) := by
    rw [hcomplex, hpair]
  exact_mod_cast hcomplex_one

/-- Helper for Exercise 9-9.1-2: an integral square sum equal to `1` has exactly one nonzero
coefficient, and that coefficient is `1` or `-1`. -/
private lemma integer_coefficients_eq_singleton_of_sq_sum_eq_one
    {ι : Type*} [Fintype ι] (c : ι → ℤ) (h : ∑ i, (c i)^2 = 1) :
    ∃ i, (c i = 1 ∨ c i = -1) ∧ ∀ j, j ≠ i → c j = 0 := by
  classical
  have hnotallzero : ¬ ∀ i, c i = 0 := by
    intro hzero
    have hsum_zero : ∑ i, (c i)^2 = 0 := by
      simp [hzero]
    linarith
  obtain ⟨i, hi_nonzero⟩ : ∃ i, c i ≠ 0 := by
    simpa [not_forall] using hnotallzero
  have hi_sq_le : (c i)^2 ≤ 1 := by
    calc
      (c i)^2 ≤ ∑ j, (c j)^2 := by
        simpa using
          (Finset.single_le_sum (fun j _ ↦ sq_nonneg (c j)) (Finset.mem_univ i) :
            (c i)^2 ≤ ∑ j, (c j)^2)
      _ = 1 := h
  have hi_sq_eq : (c i)^2 = 1 := by
    exact Int.sq_eq_one_of_sq_le_three (le_trans hi_sq_le (by norm_num)) hi_nonzero
  have hi_sign : c i = 1 ∨ c i = -1 := by
    exact sq_eq_one_iff.mp hi_sq_eq
  refine ⟨i, hi_sign, ?_⟩
  intro j hji
  have hsum_erase :
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = 1 := by
    calc
      Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) + (c i)^2 = ∑ k, (c k)^2 := by
        simpa using (Finset.sum_erase_add (s := Finset.univ) (f := fun k ↦ (c k)^2)
          (Finset.mem_univ i))
      _ = 1 := h
  have herase_zero : Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) = 0 := by
    linarith
  have hj_sq_le :
      (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2) := by
    have hj_mem : j ∈ Finset.univ.erase i := by
      simp [hji]
    simpa using
      (Finset.single_le_sum (fun k _ ↦ sq_nonneg (c k)) hj_mem :
        (c j)^2 ≤ Finset.sum (Finset.univ.erase i) (fun k ↦ (c k)^2))
  have hj_sq_eq_zero : (c j)^2 = 0 := by
    have hj_sq_nonneg : 0 ≤ (c j)^2 := sq_nonneg (c j)
    linarith
  exact sq_eq_zero_iff.mp hj_sq_eq_zero

/-- Helper for Exercise 9-9.1-2: a simple finite-dimensional complex representation has positive
degree. -/
private theorem simple_fdRep_finrank_pos (V : FDRep ℂ G) [Simple V] :
    0 < Module.finrank ℂ V := by
  have hV_nontriv : Nontrivial V := by
    by_contra hV_sub
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV_sub
    have hzero : (𝟙 V : V ⟶ V) = 0 := by
      ext x
      exact Subsingleton.elim _ _
    exact CategoryTheory.id_nonzero V hzero
  exact Module.finrank_pos

/-- Exercise 9-9.1-2: for a virtual complex character `χ ∈ R(G)`, LinearRepresentations_Serre_1977's irreducibility
criterion is equivalent to the conjunction that the self-pairing of `χ` is `1` and the value of
`χ` at the identity has nonnegative real part. The finite-dimensional irreducible realization is
expressed canonically as a simple object of `FDRep ℂ G`. -/
theorem exists_irreducible_fdRep_character_eq_iff
    (χ : R(G)) :
    (∃ V : FDRep ℂ G, Simple V ∧ V.character = χ) ↔
      ⟪(χ : G → ℂ), χ⟫ = (1 : ℂ) ∧ 0 ≤ ((χ : G → ℂ) 1).re := by
  constructor
  · rintro ⟨V, hV_simple, hV_char⟩
    constructor
    · -- Promote simplicity to irreducibility and apply the Chapter 2 criterion.
      letI : Simple V := hV_simple
      letI : Representation.IsIrreducible V.ρ := FDRep.isIrreducible_of_simple V
      calc
        ⟪(χ : G → ℂ), χ⟫ = ⟪V.character, V.character⟫ := by
          rw [← hV_char]
        _ = (1 : ℂ) := by
          exact (self_character_pairing_eq_one_iff_isIrreducible V.ρ).2 inferInstance
    · -- Evaluate the character at the identity to read off the nonnegative degree.
      have hdegree_nonneg : 0 ≤ (Module.finrank ℂ V : ℝ) := by
        positivity
      have hV_one_nonneg : 0 ≤ (V.character 1).re := by
        simpa using hdegree_nonneg
      rw [← hV_char]
      exact hV_one_nonneg
  · intro hχ
    rcases hχ with ⟨hpair, hχ_one_nonneg⟩
    letI : NeZero (Nat.card G : ℂ) := ⟨by
      exact_mod_cast Nat.card_pos.ne'⟩
    -- Route correction: use the canonical irreducible-character basis of `R(G)` to show that `χ`
    -- is a signed irreducible character, then use the value at `1` to rule out the negative sign.
    obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
      exists_complete_pairwise_nonisomorphic_irreducible_family (G := G)
    let b := irreducible_characters_basis_of_complete_family ℂ π hπ_pairwise hπ_complete
    let c := b.repr χ
    have hsq : ∑ i, (c i)^2 = 1 :=
      repr_square_sum_eq_one_of_self_pairing_eq_one (π := π) hπ_pairwise hπ_complete χ hpair
    obtain ⟨i, hi_sign, hzero⟩ :=
      integer_coefficients_eq_singleton_of_sq_sum_eq_one c hsq
    have hχ_expansion : ∑ j, c j • (π j).character = (χ : G → ℂ) := by
      -- Rewrite the basis expansion of `χ` into the ambient function space.
      simpa [b, c, irreducible_characters_basis_of_complete_family_apply,
        FDRep.irreducibleCharacter_apply] using
        congrArg (fun z : R(G) ↦ (z : G → ℂ)) (b.sum_repr χ)
    have hsum_single : ∑ j, c j • (π j).character = c i • (π i).character := by
      -- All basis coefficients except one vanish.
      refine Finset.sum_eq_single i ?_ ?_
      · intro j _ hji
        simp [hzero j hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    have hχ_single : (χ : G → ℂ) = c i • (π i).character := by
      calc
        (χ : G → ℂ) = ∑ j, c j • (π j).character := by
          simpa using hχ_expansion.symm
        _ = c i • (π i).character := hsum_single
    rcases hi_sign with hi_pos | hi_neg
    · -- The positive sign gives `χ` itself as an irreducible character.
      refine ⟨π i, hπ_complete.isSimple i, ?_⟩
      calc
        (π i).character = (1 : ℤ) • (π i).character := by simp
        _ = (χ : G → ℂ) := by simpa [hi_pos] using hχ_single.symm
    · -- The negative sign would force `χ(1)` to be strictly negative, contradicting the hypothesis.
      letI : Simple (π i) := hπ_complete.isSimple i
      have hπ_pos : 0 < Module.finrank ℂ (π i) :=
        simple_fdRep_finrank_pos (V := π i)
      have hχ_neg : (χ : G → ℂ) = (-1 : ℤ) • (π i).character := by
        simpa [hi_neg] using hχ_single
      have hχ_one :
          ((χ : G → ℂ) 1).re = -(Module.finrank ℂ (π i) : ℝ) := by
        have hzsmul :
            (((-1 : ℤ) • (π i).character : G → ℂ)) = ((-1 : ℂ) • (π i).character) := by
          ext g
          simp [smul_eq_mul]
        calc
          ((χ : G → ℂ) 1).re = ((((-1 : ℤ) • (π i).character : G → ℂ) 1)).re := by
            rw [hχ_neg]
          _ = ((((-1 : ℂ) • (π i).character : G → ℂ) 1)).re := by
            rw [hzsmul]
          _ = -(Module.finrank ℂ (π i) : ℝ) := by
            simp [FDRep.char_one]
      have hπ_pos_real : 0 < (Module.finrank ℂ (π i) : ℝ) := by
        exact_mod_cast hπ_pos
      have hχ_one_neg : ((χ : G → ℂ) 1).re < 0 := by
        rw [hχ_one]
        linarith
      exact (not_lt_of_ge hχ_one_nonneg hχ_one_neg).elim

end

end Representation

/-! ### Exercise_9_9_1_3 (from Chap09) -/
open scoped Representation

noncomputable section

universe u v

namespace Representation

open PowerSeries

section

variable {k : Type} [Field k]
variable {G : Type u} [Monoid G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Exercise 9-9.1-3: evaluating the symmetric-power character series at `s` gives the inverse
of the basis-free polynomial `((ρ s).charpoly.reverse : k[T]) = det(1 - ρ(s) T)`. -/
theorem symmetricPowerCharacterSeries_eval_eq_det_inv
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) σ_T(ρ) =
      (((ρ s).charpoly.reverse : Polynomial k) : PowerSeries k)⁻¹ :=
  -- Route correction: the remaining source-faithful work lives in the imported
  -- `SymmetricExteriorProduct` support file, not in this public wrapper; the new split-model
  -- transport plus quotient-trace transport there now reduce the live gap to the restriction-side
  -- trace of the first filtration piece.
  symmetricPowerCharacterSeries_eval_eq_det_inv_aux (ρ := ρ) s

/-- Evaluating the exterior-power character series at `s` gives the determinant
`det(1 + ρ(s) T)`, encoded basis-freely as `(-ρ s).charpoly.reverse`. -/
theorem exteriorPowerCharacterSeries_eval_eq_det
    (ρ : Representation k G V) (s : G) :
    PowerSeries.map (Pi.evalRingHom _ s) λ_T(ρ) =
      (((-ρ s).charpoly.reverse : Polynomial k) : PowerSeries k) :=
  exteriorPowerCharacterSeries_eval_eq_det_aux (ρ := ρ) s

end

section

variable {k : Type} [Field k] [Algebra ℚ k]
variable {G : Type u} [Group G]
variable {V : Type v}
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The symmetric-power generating series is the exponential of the Adams-operation series. -/
theorem symmetricPowerCharacterSeries_eq_exp_subst (ρ : Representation k G V) :
    σ_T(ρ) =
      (exp (G → k)).subst (psiGeneratingSeries ρ.character) :=
  symmetricPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ)

/-- The exterior-power generating series is the exponential of the alternating Adams-operation
series. -/
theorem exteriorPowerCharacterSeries_eq_exp_subst (ρ : Representation k G V) :
    λ_T(ρ) =
      (exp (G → k)).subst (alternatingPsiGeneratingSeries ρ.character) :=
  exteriorPowerCharacterSeries_eq_exp_subst_aux (ρ := ρ)

/-- The symmetric-power characters satisfy the Newton-style recursion
`n χ_σ^n = ∑_{k=1}^n Ψ^k(χ) χ_σ^{n-k}`. -/
theorem nthSymmetricPowerCharacter_recurrence (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthSymmetricPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        Ψ^m(ρ.character) * (ρ.nthSymmetricPower ((n : ℕ) - m)).character :=
  by
    -- Differentiate the symmetric exponential identity and read off the coefficient of degree
    -- `n - 1`.
    have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
      -- The positive summation range is the successor image of `range n`.
      simpa using pnat_Icc_one_eq_map_range n
    ext s
    rw [hmap, Finset.sum_map]
    simp only [Pi.mul_apply, Finset.sum_apply]
    have hcoeff :=
      congrArg (PowerSeries.coeff n.natPred) (derivative_symmetricPowerCharacterSeries ρ)
    rw [PowerSeries.coeff_derivative, coeff_symmetricPowerCharacterSeries, PowerSeries.coeff_mul]
      at hcoeff
    simp only [coeff_derivative_psiGeneratingSeries] at hcoeff
    have hs := congrFun hcoeff s
    have hnat : (n : ℕ) = n.natPred + 1 := by
      exact (PNat.natPred_add_one n).symm
    have hcast' : ((n.natPred : k) + 1) = (n : k) := by
      rw [← Nat.cast_one]
      rw [← Nat.cast_add]
      rw [PNat.natPred_add_one]
    have hsCoeff :
        (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s =
          ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
            Ψ^x.succPNat(ρ.character) s := by
      calc
        (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s
            = ((n.natPred : k) + 1) * (ρ.nthSymmetricPower (n.natPred + 1)).character s := by
              rw [hcast']
        _ = ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
              Ψ^x.succPNat(ρ.character) s := by
            simpa [Finset.Nat.antidiagonal_eq_map', mul_comm] using hs
    calc
      (n : k) * (ρ.nthSymmetricPower n).character s
          = (n : k) * (ρ.nthSymmetricPower (n.natPred + 1)).character s := by
            rw [hnat]
      _ = ∑ x ∈ Finset.range ↑n, (ρ.nthSymmetricPower (n.natPred - x)).character s *
            Ψ^x.succPNat(ρ.character) s := by
          exact hsCoeff
      _ = ∑ x ∈ Finset.range ↑n, Ψ^x.succPNat(ρ.character) s *
            (ρ.nthSymmetricPower (↑n - (x + 1))).character s := by
          -- Reindex by the predecessor `x` and put the Adams term first to match the statement.
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
            omega
          rw [hsub, mul_comm]

/-- The exterior-power characters satisfy the alternating Newton-style recursion
`n χ_λ^n = ∑_{k=1}^n (-1)^(k-1) Ψ^k(χ) χ_λ^{n-k}`. -/
theorem nthExteriorPowerCharacter_recurrence (ρ : Representation k G V) (n : ℕ+) :
    (n : k) • (ρ.nthExteriorPower n).character =
      Finset.sum (Finset.Icc 1 n) fun m ↦
        (((-1 : k) ^ ((m : ℕ) - 1)) • Ψ^m(ρ.character)) *
          (ρ.nthExteriorPower ((n : ℕ) - m)).character :=
  by
    -- Reindex the differentiated alternating exponential identity by positive integers.
    have hmap : Finset.Icc 1 n = (Finset.range n).map ⟨Nat.succPNat, Nat.succPNat_injective⟩ := by
      simpa using pnat_Icc_one_eq_map_range n
    ext s
    rw [hmap, Finset.sum_map]
    simp only [Pi.mul_apply, Finset.sum_apply]
    have hcoeff :=
      congrArg (PowerSeries.coeff n.natPred) (derivative_exteriorPowerCharacterSeries ρ)
    rw [PowerSeries.coeff_derivative, coeff_exteriorPowerCharacterSeries, PowerSeries.coeff_mul]
      at hcoeff
    simp only [coeff_derivative_alternatingPsiGeneratingSeries,
      coeff_exteriorPowerCharacterSeries] at hcoeff
    have hs := congrFun hcoeff s
    have hnat : (n : ℕ) = n.natPred + 1 := by
      exact (PNat.natPred_add_one n).symm
    have hcast' : ((n.natPred : k) + 1) = (n : k) := by
      rw [← Nat.cast_one]
      rw [← Nat.cast_add]
      rw [PNat.natPred_add_one]
    have hsCoeff :
        (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s =
          ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
            (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
      calc
        (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s
            = ((n.natPred : k) + 1) * (ρ.nthExteriorPower (n.natPred + 1)).character s := by
              rw [hcast']
        _ = ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
              (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
            simpa [Finset.Nat.antidiagonal_eq_map', mul_assoc, mul_left_comm, mul_comm] using hs
    calc
      (n : k) * (ρ.nthExteriorPower n).character s
          = (n : k) * (ρ.nthExteriorPower (n.natPred + 1)).character s := by
            rw [hnat]
      _ = ∑ x ∈ Finset.range ↑n, (ρ.nthExteriorPower (n.natPred - x)).character s *
            (((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) s := by
          exact hsCoeff
      _ = ∑ x ∈ Finset.range ↑n, ((((-1 : k) ^ x) • Ψ^x.succPNat(ρ.character)) *
            (ρ.nthExteriorPower (↑n - (x + 1))).character) s := by
          -- Reindex from predecessors to positive indices and move the signed Adams factor first.
          refine Finset.sum_congr rfl ?_
          intro x hx
          have hsub : n.natPred - x = (n : ℕ) - (x + 1) := by
            omega
          simp only [Pi.mul_apply]
          rw [hsub]
          ac_rfl

end

end Representation
