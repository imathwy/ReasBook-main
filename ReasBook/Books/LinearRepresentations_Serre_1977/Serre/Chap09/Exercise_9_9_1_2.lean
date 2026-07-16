import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap09.Exercise_9_9_1_1
import LinearRepresentations_Serre_1977.Serre.FiniteToFintype

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped Representation
open scoped BigOperators

noncomputable section

namespace Representation

section

variable {G : Type} [Group G] [Finite G]

-- Source/core/bridge triage:
-- * source-facing: Serre's irreducibility criterion for a virtual complex character `χ ∈ R(G)`.
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

/-- Exercise 9-9.1-2: for a virtual complex character `χ ∈ R(G)`, Serre's irreducibility
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
