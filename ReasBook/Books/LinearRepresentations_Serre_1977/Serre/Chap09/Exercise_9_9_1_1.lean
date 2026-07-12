import Mathlib
import LinearRepresentations_Serre_1977.Chap11.Theorem_11_11_2_1.TensorCharacterBridge
import LinearRepresentations_Serre_1977.RepresentationTheory.GroupFunctionPairing
import LinearRepresentations_Serre_1977.Chap02.Proposition_2_2_1_2
import LinearRepresentations_Serre_1977.Chap02.Remark_2_2_4_4
import LinearRepresentations_Serre_1977.Chap06.Exercise_6_6_5_7
import LinearRepresentations_Serre_1977.Chap12.Proposition_12_12_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace Representation

open CategoryTheory

section CharacterRing

variable {G : Type} [Group G]


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
-- * source-facing: Serre's Chapter 9 positivity criterion for an integral virtual character to be
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
-- previous theorem, and the pairing with the unit character is zero. As in Serre's argument, this
-- forces all coefficients to be nonnegative, so the function is an actual character.
/-- Exercise 9-9.1-1: if a real-valued function on a finite group has zero pairing with the unit
character, is nonpositive away from the identity, and belongs to Serre's character ring `R(G)`,
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
