import Mathlib
import Serre.Chap01.Definition_1_1_4_1
import Serre.Chap03.Theorem_3_3_1_1
import Serre.Chap06.Corollary_6_6_5_3
import Serre.Chap06.Exercise_6_6_5_6
import Serre.Chap06.Exercise_6_6_5_8
import Serre.Chap06.Proposition_6_6_5_1
import Serre.Chap08.Definition_8_8_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open CategoryTheory
open Representation
open Module.End Polynomial
open scoped BigOperators MonoidAlgebra

variable {G : Type} [Group G]

noncomputable local instance [Finite G] : Fintype G := Fintype.ofFinite G

local notation "A4" => alternatingGroup (Fin 4)

variable {q : ℕ} [Fact q.Prime]

-- Proof sketch: apply the class equation. If every nontrivial conjugacy class had cardinality
-- divisible by `q`, then `Nat.card G - 1` would be divisible by `q`; this contradicts
-- `q ∣ Nat.card G`.
/-- Exercise 8-8.3-10 (1): source part (i). If the center of `G` is trivial and `q` divides the
order of `G`, then some nonidentity element has conjugacy class cardinality not divisible by `q`. -/
theorem exists_nontrivial_element_conjClass_card_not_dvd_of_center_eq_bot
    [Finite G] (hq : q ∣ Nat.card G)
    (hcenter : Subgroup.center G = ⊥) :
    ∃ s : G, s ≠ 1 ∧ ¬ q ∣ Nat.card (ConjClasses.mk s).carrier := by
  classical
  cases nonempty_fintype G
  by_contra h
  push Not at h
  -- Every noncentral conjugacy class then contributes a multiple of `q` to the class equation.
  have hsum :
      q ∣ ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card := by
    refine Finset.dvd_sum ?_
    intro x hx
    obtain ⟨s, rfl⟩ := Quotient.exists_rep x
    have hs_ne_one : s ≠ 1 := by
      intro hs
      have hmk1 :
          (ConjClasses.mk (1 : G)) ∉ ConjClasses.noncenter G := by
        simpa using (ConjClasses.mk_bijOn G).mapsTo (show (1 : G) ∈ Subgroup.center G by simp)
      exact hmk1 (by simpa [hs] using hx)
    simpa [Nat.card_eq_fintype_card, Set.toFinset_card] using h s hs_ne_one
  have hcard :
      Fintype.card (Subgroup.center G) +
        ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card =
      Fintype.card G := Group.card_center_add_sum_card_noncenter_eq_card G
  have hq_fintype : q ∣ Fintype.card G := by
    simpa [Nat.card_eq_fintype_card] using hq
  have hq_center : q ∣ Fintype.card (Subgroup.center G) := by
    have hcenter_eq :
        Fintype.card (Subgroup.center G) =
          Fintype.card G -
            ∑ x ∈ (ConjClasses.noncenter G).toFinset, x.carrier.toFinset.card := by
      omega
    simpa [hcenter_eq] using Nat.dvd_sub hq_fintype hsum
  have hq_one : q ∣ 1 := by
    simpa [hcenter] using hq_center
  exact (show Nat.Prime q from Fact.out).not_dvd_one hq_one

variable {p a b : ℕ} [Fact p.Prime]

/-- Helper for Exercise 8-8.3-10: a divisor of `p ^ a * q ^ b` is again of the form
`p ^ i * q ^ j`. -/
lemma card_eq_prime_pow_mul_prime_pow_of_dvd_prime_pow_mul_prime_pow
    {n : ℕ} (hn : n ∣ p ^ a * q ^ b) :
    ∃ i j, n = p ^ i * q ^ j := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  by_cases hpq : p = q
  · subst hpq
    have hn' : n ∣ p ^ (a + b) := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hn
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hn'
    exact ⟨i, 0, by simpa [pow_zero, hi]⟩
  · have hprod0 : p ^ a * q ^ b ≠ 0 := by
      exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
    have hn0 : n ≠ 0 := by
      intro hz
      rw [hz, zero_dvd_iff] at hn
      exact hprod0 hn
    have hfac : n.factorization ≤ (p ^ a * q ^ b).factorization :=
      (Nat.factorization_le_iff_dvd hn0 hprod0).2 hn
    have hsupp : ↑n.factorization.support ⊆ ({p, q} : Set ℕ) := by
      intro r hr
      by_cases hrp : r = p
      · simp [hrp]
      by_cases hrq : r = q
      · simp [hrq]
      have hmul :=
        Nat.factorization_mul (a := p ^ a) (b := q ^ b)
          (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
      have hprod : (p ^ a * q ^ b).factorization r = 0 := by
        have h :=
          congrArg (fun f : ℕ →₀ ℕ => f r) hmul
        have hpr : p ≠ r := by
          intro hpr'
          exact hrp hpr'.symm
        have hqr : q ≠ r := by
          intro hqr'
          exact hrq hqr'.symm
        simp only [hp.factorization_pow, hq.factorization_pow, Finsupp.add_apply,
          Finsupp.single_apply, hpr, hqr, if_false, add_zero] at h
        exact h
      have h0 : n.factorization r = 0 := by
        have hle0 : n.factorization r ≤ 0 := by
          simpa [hprod] using hfac r
        exact Nat.eq_zero_of_le_zero hle0
      exact False.elim ((Finsupp.mem_support_iff.mp hr) h0)
    refine ⟨n.factorization p, n.factorization q, ?_⟩
    have hfac_eq :
        n.factorization =
          Finsupp.single p (n.factorization p) +
            Finsupp.single q (n.factorization q) := by
      ext r
      by_cases hrp : r = p
      · subst r
        simp [hpq]
      by_cases hrq : r = q
      · subst r
        simp [hpq]
      have h0 : n.factorization r = 0 := by
        by_contra h0
        have hrmem : r ∈ ({p, q} : Set ℕ) := hsupp (Finsupp.mem_support_iff.mpr h0)
        simp [hrp, hrq] at hrmem
      simp [h0, hrp, hrq]
    calc
      n = n.factorization.prod (fun x k ↦ x ^ k) := by
        symm
        exact Nat.prod_factorization_pow_eq_self hn0
      _ = p ^ n.factorization p * q ^ n.factorization q := by
        rw [hfac_eq]
        simp [Finsupp.prod_add_index, pow_add, hpq]

/-- Helper for Exercise 8-8.3-10: if a divisor of `p ^ a * q ^ b` is not divisible by `q`, then
it is a pure power of `p`. -/
lemma eq_prime_pow_of_not_dvd_of_dvd_prime_pow_mul_prime_pow
    {n : ℕ} (hn : n ∣ p ^ a * q ^ b) (hqn : ¬ q ∣ n) :
    ∃ i, n = p ^ i := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  by_cases hpq : p = q
  · subst hpq
    have hn' : n ∣ p ^ (a + b) := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hn
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).mp hn'
    exact ⟨i, hi⟩
  · obtain ⟨i, j, hij⟩ :=
      card_eq_prime_pow_mul_prime_pow_of_dvd_prime_pow_mul_prime_pow
        (p := p) (q := q) (a := a) (b := b) hn
    by_cases hj0 : j = 0
    · exact ⟨i, by simpa [hij, hj0, pow_zero] using hij⟩
    · have hqpow : q ∣ q ^ j := dvd_pow_self q hj0
      have hqdvd : q ∣ n := by
        rw [hij]
        exact dvd_mul_of_dvd_right hqpow (p ^ i)
      exact False.elim (hqn hqdvd)

/-- Helper for Exercise 8-8.3-10: under the Maschke hypotheses, a finite group admits a complete
pairwise nonisomorphic family of simple finite-dimensional complex representations. -/
theorem exists_complete_pairwise_nonisomorphic_simple_family
    [Finite G] [NeZero (Nat.card G : ℂ)] :
    ∃ (ι : Type) (_ : Fintype ι) (π : ι → FDRep ℂ G),
      PairwiseNonisomorphic π ∧ IsCompleteIrreducibleFamily π := by
  classical
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨κ, _, σ, hσ_indep, hσ_top, hσ_irr⟩ :=
    exists_isInternal_irreducible_subrepresentations (ρ := leftRegular ℂ G)
  let hinternal : DirectSum.IsInternal (fun i ↦ (σ i).toSubmodule) :=
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
    -- Distinct quotient classes cannot represent isomorphic irreducibles.
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
    -- Each representative remains irreducible, hence simple in `FDRep`.
    letI : Representation.IsIrreducible (π q).ρ := by
      simpa [π] using hσ_irr (Quotient.out q)
    exact FDRep.simple_of_isIrreducible (π q)
  let S : ι → Finset κ :=
    fun q ↦ Finset.univ.filter fun j ↦ Nonempty ((σ j).toRepresentation.Equiv (π q).ρ)
  let dimσ : κ → Nat := fun j ↦ Module.finrank ℂ (σ j).toSubmodule
  have hS_disjoint : Pairwise fun q q' ↦ Disjoint (S q) (S q') := by
    intro q q' hqq'
    refine Finset.disjoint_left.mpr fun j hj hj' ↦ ?_
    rcases (Finset.mem_filter.mp hj).2 with ⟨eqj⟩
    rcases (Finset.mem_filter.mp hj').2 with ⟨eqj'⟩
    exact hπ_pairwise hqq' <| ⟨(eqj.symm.trans eqj').toFDRepIso⟩
  have hS_card (q : ι) : (S q).card = Module.finrank ℂ (π q) := by
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
    calc
      Finset.sum (S q) dimσ = Finset.sum (S q) (fun _j ↦ Module.finrank ℂ (π q)) := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        rcases (Finset.mem_filter.mp hj).2 with ⟨e⟩
        exact e.toLinearEquiv.finrank_eq
      _ = (S q).card * Module.finrank ℂ (π q) := by
            simp
      _ = Module.finrank ℂ (π q) ^ 2 := by
            rw [hS_card, pow_two]
  have hcover :
      Finset.univ.biUnion S = (Finset.univ : Finset κ) := by
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
    letI := DirectSum.IsInternal.chooseDecomposition (fun j ↦ (σ j).toSubmodule) hinternal
    letI : ∀ j : κ, Module.Free ℂ (σ j).toSubmodule := fun j ↦
      Module.Free.of_divisionRing ℂ (σ j).toSubmodule
    let e := (DirectSum.decomposeLinearEquiv (fun j ↦ (σ j).toSubmodule)).symm
    calc
      Finset.sum (Finset.univ : Finset κ) dimσ = Module.finrank ℂ (G →₀ ℂ) := by
        symm
        calc
          Module.finrank ℂ (G →₀ ℂ) =
              Module.finrank ℂ (DirectSum κ fun j ↦ (σ j).toSubmodule) := by
                exact e.finrank_eq.symm
          _ = Finset.sum (Finset.univ : Finset κ) dimσ := by
                dsimp [dimσ]
                exact Module.finrank_directSum (R := ℂ) (M := fun j ↦ (σ j).toSubmodule)
      _ = Nat.card G := by
            rw [Nat.card_eq_fintype_card]
            exact Module.finrank_finsupp_self ℂ
  have hπ_sum : ∑ q : ι, Module.finrank ℂ (π q) ^ 2 = Nat.card G := by
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
    exact isCompleteIrreducibleFamily_of_sum_sq_degree_eq_card π hπ_simple hπ_pairwise hπ_sum
  exact ⟨ι, inferInstance, π, hπ_pairwise, hπ_complete⟩

/-- Helper for Exercise 8-8.3-10: a simple trivial finite-dimensional complex representation is
isomorphic to the trivial representation. -/
lemma nonempty_equiv_trivial_of_simple_of_isTrivial
    (W : FDRep ℂ G) [Simple W] [Representation.IsTrivial W.ρ] :
    Nonempty (Representation.Equiv W.ρ (Representation.trivial ℂ G ℂ)) := by
  -- Every linear endomorphism of a trivial representation is automatically intertwining.
  let X : Rep ℂ G := (forget₂ (FDRep ℂ G) (Rep ℂ G)).obj W
  let eInter : Representation.IntertwiningMap W.ρ W.ρ ≃ₗ[ℂ] (W →ₗ[ℂ] W) :=
    LinearEquiv.ofBijective
      (Representation.IntertwiningMap.toLinearMapl (ρ := W.ρ) (σ := W.ρ))
      ⟨Representation.IntertwiningMap.toLinearMap_injective _ _,
        fun f ↦ by
          refine ⟨LinearMap.intertwiningMap_of_isIntertwiningMap
            (ρ := W.ρ) (σ := W.ρ) (f := f) ?_, rfl⟩
          intro g x
          simp⟩
  let eEnd : (W ⟶ W) ≃ₗ[ℂ] (W →ₗ[ℂ] W) :=
    ((FDRep.forget₂HomLinearEquiv W W).symm).trans ((Rep.homLinearEquiv X X).trans eInter)
  have hEnd : Module.finrank ℂ (W →ₗ[ℂ] W) = 1 := by
    -- Schur's lemma forces the endomorphism space of a simple object to be one-dimensional.
    rw [← LinearEquiv.finrank_eq eEnd]
    simpa using CategoryTheory.finrank_endomorphism_simple_eq_one ℂ W
  have hdim : Module.finrank ℂ W = 1 := by
    -- The space of linear endomorphisms has dimension `dim(W)^2`.
    have hsq : Module.finrank ℂ W * Module.finrank ℂ W = 1 := by
      simpa [Module.finrank_linearMap] using hEnd
    exact Nat.eq_one_of_mul_eq_one_left hsq
  rcases Module.nonempty_linearEquiv_of_finrank_eq_one hdim with ⟨e⟩
  refine ⟨Representation.Equiv.mk e.symm ?_⟩
  -- Once `W` has dimension `1`, the trivial action follows from the `IsTrivial` hypothesis.
  intro g
  ext z
  simp

/-- Helper for Exercise 8-8.3-10: integrality of `(m : k) / n` over `ℤ` forces the divisibility
`n ∣ m`. -/
lemma nat_dvd_of_isIntegral_natCast_div_local
    {k : Type*} [Field k] [CharZero k] {m n : ℕ} (hn : n ≠ 0)
    (h : IsIntegral ℤ ((m : k) / n)) :
    n ∣ m := by
  let r : ℚ := m / n
  have hr : IsIntegral ℤ r := by
    have hrk : IsIntegral ℤ (r : k) := by
      simpa [r] using h
    exact IsIntegral.ratCast_iff.mp hrk
  obtain ⟨z, hz : r = z⟩ := hr.exists_int_iff_exists_rat |>.mp ⟨r, rfl⟩
  have hden : r.den = 1 := by
    rw [hz]
    simp
  exact (Rat.den_div_natCast_eq_one_iff m n hn).mp <| by
    simpa [r] using hden

/-- Helper for Exercise 8-8.3-10: after dividing by `p`, each degree-weighted character summand
remains integral if the character value vanishes or the degree is divisible by `p`. -/
lemma isIntegral_degree_character_div_prime_of_eq_zero_or_prime_dvd
    [Finite G] (W : FDRep ℂ G) (s : G) {p : ℕ} (hp : Nat.Prime p)
    (h : W.character s = 0 ∨ p ∣ Module.finrank ℂ W) :
    IsIntegral ℤ (((Module.finrank ℂ W : ℂ) * W.character s) / p) := by
  rcases h with hzero | hdiv
  · -- A vanishing character value makes the normalized summand equal to zero.
    simpa [hzero] using (isIntegral_zero : IsIntegral ℤ (0 : ℂ))
  · rcases hdiv with ⟨m, hm⟩
    have hp0 : (p : ℂ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    have hmC : (Module.finrank ℂ W : ℂ) = (p : ℂ) * m := by
      exact_mod_cast hm
    have hrewrite :
        (((Module.finrank ℂ W : ℂ) * W.character s) / p) = (m : ℂ) * W.character s := by
      -- Pull the factor `p` out of the degree and cancel it against the denominator.
      calc
        (((Module.finrank ℂ W : ℂ) * W.character s) / p)
            = ((((p : ℂ) * m) * W.character s) / p) := by
                rw [hmC]
        _ = (m : ℂ) * W.character s := by
              field_simp [hp0]
    rw [hrewrite]
    exact IsIntegral.mul isIntegral_algebraMap (Representation.char_isIntegral W.ρ s)

/-- Helper for Exercise 8-8.3-10: a prime-power conjugacy class forces a nontrivial irreducible
constituent whose character does not vanish there and whose degree avoids that prime. -/
theorem exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow
    [Finite G] (s : G) (hs : s ≠ 1) {p n : ℕ} (hp : Nat.Prime p)
    (hcard : Nat.card (ConjClasses.mk s).carrier = p ^ n) :
    ∃ W : FDRep ℂ G,
      Simple W ∧
        ¬ Representation.IsTrivial W.ρ ∧
        W.character s ≠ 0 ∧
        ¬ p ∣ Module.finrank ℂ W := by
  classical
  let _hcard : Nat.card (ConjClasses.mk s).carrier = p ^ n := hcard
  letI : Fintype G := Fintype.ofFinite G
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  letI : NeZero (Nat.card G : ℂ) := ⟨hcard_ne⟩
  -- Choose a complete irreducible family and single out the trivial constituent.
  obtain ⟨ι, _, π, hπ_pairwise, hπ_complete⟩ :=
    exists_complete_pairwise_nonisomorphic_simple_family (G := G)
  letI : IsCompleteIrreducibleFamily π := hπ_complete
  letI : Finite ι := IsCompleteIrreducibleFamily.finite_index π hπ_complete hπ_pairwise
  letI : Fintype ι := Fintype.ofFinite ι
  haveI : (Representation.trivial ℂ G ℂ).IsIrreducible := by
    simpa using
      isIrreducible_of_finrank_eq_one (ρ := Representation.trivial ℂ G ℂ)
        (by simp : Module.finrank ℂ ℂ = 1)
  obtain ⟨i0, hi0⟩ :=
    IsCompleteIrreducibleFamily.exists_iso_of_representation π hπ_complete
      (Representation.trivial ℂ G ℂ) inferInstance
  rcases hi0 with ⟨e0⟩
  have htriv_char : (π i0).character s = 1 := by
    -- Transport the trivial character across the chosen isomorphism.
    have hchar0 : (Representation.trivial ℂ G ℂ).character = (π i0).character := by
      simpa using
        Representation.char_iso
          (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e0))
    have hvalue := congrArg (fun χ : G → ℂ ↦ χ s) hchar0
    simpa [Representation.character, Representation.trivial] using hvalue.symm
  have htriv_dim : Module.finrank ℂ (π i0) = 1 := by
    -- Evaluating the transported trivial character at `1` recovers the degree.
    have hchar0 : (Representation.trivial ℂ G ℂ).character = (π i0).character := by
      simpa using
        Representation.char_iso
          (Representation.equivOfIso ((forget₂ (FDRep ℂ G) (Rep ℂ G)).mapIso e0))
    have hvalue := congrArg (fun χ : G → ℂ ↦ χ 1) hchar0
    simpa [Representation.char_one, Representation.character, Representation.trivial] using
      hvalue.symm
  have hi0_term : (Module.finrank ℂ (π i0) : ℂ) * (π i0).character s = 1 := by
    simp [htriv_dim, htriv_char]
  by_contra hexists
  have hbad :
      ∀ W : FDRep ℂ G, Simple W → ¬ Representation.IsTrivial W.ρ → W.character s ≠ 0 →
        p ∣ Module.finrank ℂ W := by
    intro W hWsimple hWnontriv hχ
    by_cases hdiv : p ∣ Module.finrank ℂ W
    · exact hdiv
    · exact False.elim <| hexists ⟨W, hWsimple, hWnontriv, hχ, hdiv⟩
  have hterm_case :
      ∀ i : ι, i ≠ i0 → (π i).character s = 0 ∨ p ∣ Module.finrank ℂ (π i) := by
    intro i hne
    have hnontriv : ¬ Representation.IsTrivial (π i).ρ := by
      intro htriv
      letI : Representation.IsTrivial (π i).ρ := htriv
      have hi : Nonempty (π i ≅ FDRep.of (Representation.trivial ℂ G ℂ)) := by
        letI : Simple (π i) := hπ_complete.isSimple i
        rcases nonempty_equiv_trivial_of_simple_of_isTrivial (W := π i) with ⟨e⟩
        exact ⟨e.toFDRepIso⟩
      rcases hi with ⟨ei⟩
      exact hπ_pairwise hne ⟨ei.trans e0⟩
    by_cases hχ : (π i).character s = 0
    · exact Or.inl hχ
    · exact Or.inr <| hbad (π i) (hπ_complete.isSimple i) hnontriv hχ
  have hsum_zero :=
    sum_degree_mul_character_eq_zero_of_ne_one_of_complete_irreducible_family
      (π := π) hπ_complete hπ_pairwise s hs
  let a : ι → ℂ := fun i ↦ (Module.finrank ℂ (π i) : ℂ) * (π i).character s
  have hsum : ∑ i : ι, a i = 0 := by
    simpa [a] using hsum_zero
  have hsplit :
      Finset.sum (Finset.univ.erase i0) a + a i0 = 0 := by
    rw [Finset.sum_erase_add (s := Finset.univ) (f := a) (Finset.mem_univ i0)]
    exact hsum
  have hrest_aux :
      Finset.sum (Finset.univ.erase i0) a + 1 = 0 := by
    -- Removing the trivial constituent leaves the textbook identity over the nontrivial terms.
    simpa [a, hi0_term] using hsplit
  have hrest :
      Finset.sum (Finset.univ.erase i0) a = -1 := by
    have h := congrArg (fun z : ℂ ↦ z - 1) hrest_aux
    simpa [sub_eq_add_neg, add_assoc] using h
  have hrest_div :
      IsIntegral ℤ
        (Finset.sum (Finset.univ.erase i0) fun i ↦ a i / p) := by
    -- Every remaining summand becomes integral after dividing by `p`.
    refine IsIntegral.sum _ fun i hi ↦ ?_
    exact isIntegral_degree_character_div_prime_of_eq_zero_or_prime_dvd (π i) s hp <|
      hterm_case i (by simpa using hi)
  have hone_div : IsIntegral ℤ ((1 : ℂ) / p) := by
    have hp0 : (p : ℂ) ≠ 0 := by
      exact_mod_cast hp.ne_zero
    have hsum_div :
        Finset.sum (Finset.univ.erase i0) (fun i ↦ a i / p) =
          (Finset.sum (Finset.univ.erase i0) a) / p := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]
    have hrewrite :
        ((1 : ℂ) / p) = -Finset.sum (Finset.univ.erase i0) (fun i ↦ a i / p) := by
      -- Dividing the decomposed character identity by `p` isolates `1 / p`.
      rw [hsum_div, hrest]
      field_simp [hp0]
    rw [hrewrite]
    exact hrest_div.neg
  have hp_dvd_one : p ∣ 1 :=
    nat_dvd_of_isIntegral_natCast_div_local (k := ℂ) (m := 1) (n := p) hp.ne_zero <| by
      simpa using hone_div
  exact hp.not_dvd_one hp_dvd_one

/-- Helper for Exercise 8-8.3-10: a finite-order complex endomorphism is semisimple. -/
lemma representation_isSemisimple_of_isOfFinOrder_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) :
    Module.End.IsSemisimple (ρ s) := by
  -- The endomorphism is annihilated by `X ^ orderOf s - 1`.
  have hpow : (ρ s) ^ orderOf s = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hsep : ((X ^ orderOf s - (1 : ℂ[X]))).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact_mod_cast hs.orderOf_pos.ne'
  have haeval : Polynomial.aeval (ρ s) (X ^ orderOf s - (1 : ℂ[X])) = 0 := by
    simp [hpow]
  exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree haeval

/-- Helper for Exercise 8-8.3-10: a semisimple complex endomorphism with a unique eigenvalue is
a scalar endomorphism. -/
lemma eq_smul_id_of_isSemisimple_of_unique_eigenvalue_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : f.IsSemisimple)
    {z : ℂ} (hz : ∀ μ : ℂ, Module.End.HasEigenvalue f μ → μ = z) :
    f = z • 1 := by
  -- Shift by `z`; then it suffices to show the shifted operator has only eigenvalue `0`.
  have hshift : (f - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    (Module.End.isSemisimple_sub_algebraMap_iff (f := f) (μ := z)).2 hf
  have hzero : f - algebraMap ℂ (Module.End ℂ V) z = 0 := by
    refine (Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue hshift).2 ?_
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    -- An eigenvector for `f - z` with eigenvalue `μ` is an eigenvector for `f` with eigenvalue
    -- `μ + z`.
    have hv_mem : v ∈ f.eigenspace (μ + z) := by
      rw [mem_eigenspace_iff]
      calc
        f v =
            ((f - algebraMap ℂ (Module.End ℂ V) z) +
              algebraMap ℂ (Module.End ℂ V) z) v := by
              simp
        _ = ((f - algebraMap ℂ (Module.End ℂ V) z) v) +
              ((algebraMap ℂ (Module.End ℂ V) z) v) := by
              simp
        _ = μ • v + z • v := by simp [hv.apply_eq_smul]
        _ = (μ + z) • v := by simp [add_smul]
    have hf_eig : HasEigenvalue f (μ + z) := by
      rw [Module.End.hasEigenvalue_iff]
      exact (Submodule.ne_bot_iff _).2 ⟨v, hv_mem, hv.2⟩
    have hz' : μ + z = z := hz (μ + z) hf_eig
    exact add_right_cancel (show μ + z = 0 + z by simpa using hz')
  simpa [sub_eq_zero] using hzero

/-- Helper for Exercise 8-8.3-10: the conjugacy-class sum argument yields an algebraic integer
for the normalized class-size-weighted character value. -/
theorem isIntegral_conjClass_card_div_finrank_mul_character_local
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G) :
    IsIntegral ℤ
      (((Nat.card (ConjClasses.mk s).carrier : ℂ) / Module.finrank ℂ V) * ρ.character s) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let u : Subalgebra.center ℂ (ℂ[G]) := conjugacyClassSumInCenter ℂ (ConjClasses.mk s)
  let T : Finset G := Finset.univ.filter fun t ↦ t ∈ (ConjClasses.mk s).carrier
  have hcoeff : ∀ t : G, IsIntegral ℤ ((u : ℂ[G]) t) := fun t ↦ by
    by_cases ht : ConjClasses.mk t = ConjClasses.mk s
    · simpa [u, conjugacyClassSum_apply, ConjClasses.indicator,
        ConjClasses.mem_carrier_iff_mk_eq, ht] using isIntegral_one
    · simpa [u, conjugacyClassSum_apply, ConjClasses.indicator,
        ConjClasses.mem_carrier_iff_mk_eq, ht] using isIntegral_zero
  have h := isIntegral_finrank_inv_sum_coeff_mul_character ρ u hcoeff
  have hsum_filter :
      ∑ t : G, (u : ℂ[G]) t * ρ.character t = T.sum (fun t ↦ ρ.character t) := by
    rw [show T = Finset.univ.filter (fun t ↦ t ∈ (ConjClasses.mk s).carrier) by rfl,
      Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro t _
    by_cases ht : t ∈ (ConjClasses.mk s).carrier
    · simp [u, conjugacyClassSum_apply, ConjClasses.indicator, ht]
    · simp [u, conjugacyClassSum_apply, ConjClasses.indicator, ht]
  have hsum_subtype :
      T.sum (fun t ↦ ρ.character t) = ∑ t : (ConjClasses.mk s).carrier, ρ.character t := by
    change
      (Finset.univ.filter (fun t : G ↦ t ∈ (ConjClasses.mk s).carrier)).sum
          (fun t ↦ ρ.character t) =
        ∑ t : (ConjClasses.mk s).carrier, ρ.character t
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp
  have hsum_const :
      (∑ t : (ConjClasses.mk s).carrier, ρ.character t) =
        ∑ _ : (ConjClasses.mk s).carrier, ρ.character s := by
    refine Finset.sum_congr rfl ?_
    intro t _
    rcases ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp t.2) with
      ⟨u, hu⟩
    have hconj_eq : (u : G) * t * (u : G)⁻¹ = s := by
      calc
        (u : G) * t * (u : G)⁻¹ = (s * (u : G)) * (u : G)⁻¹ := by rw [hu.eq]
        _ = s := by simp [mul_assoc]
    exact (ρ.char_conj t u).symm.trans <| congrArg (fun g ↦ ρ.character g) hconj_eq
  have hsum_card :
      (∑ _ : (ConjClasses.mk s).carrier, ρ.character s) =
        Nat.card (ConjClasses.mk s).carrier * ρ.character s := by
    simp [Nat.card_eq_fintype_card]
  rw [hsum_filter, hsum_subtype, hsum_const, hsum_card] at h
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Helper for Exercise 8-8.3-10: coprimality upgrades the class-sum integrality to integrality
of the normalized character average. -/
lemma average_character_isIntegral_of_coprime_conjClass_card_local
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)
    (hcoprime : Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V)) :
    IsIntegral ℤ (((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s) := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  let c : ℕ := Nat.card (ConjClasses.mk s).carrier
  let n : ℕ := Module.finrank ℂ V
  have hcoprime_cn : Nat.Coprime c n := by
    simpa [c, n] using hcoprime
  have hclass :
      IsIntegral ℤ (((c : ℂ) / n) * ρ.character s) := by
    simpa [c, n] using isIntegral_conjClass_card_div_finrank_mul_character_local ρ s
  have hchar : IsIntegral ℤ (ρ.character s) := char_isIntegral ρ s
  have hfinrank_ne : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have hbez : (1 : ℤ) = c * Nat.gcdA c n + n * Nat.gcdB c n := by
    simpa [hcoprime_cn.gcd_eq_one] using Nat.gcd_eq_gcd_ab c n
  have hbezC : (1 : ℂ) = (c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n := by
    exact_mod_cast hbez
  have hdecomp :
      ((n : ℂ)⁻¹) * ρ.character s =
        (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
          (Nat.gcdB c n : ℂ) * ρ.character s := by
    calc
      ((n : ℂ)⁻¹) * ρ.character s
          = (((1 : ℂ) * (n : ℂ)⁻¹) : ℂ) * ρ.character s := by simp
      _ = ((((c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n) * (n : ℂ)⁻¹) : ℂ) *
            ρ.character s := by rw [hbezC]
      _ = (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
            (Nat.gcdB c n : ℂ) * ρ.character s := by
          field_simp [hfinrank_ne]
  rw [hdecomp]
  exact
    IsIntegral.add
      (IsIntegral.mul isIntegral_algebraMap hclass)
      (IsIntegral.mul isIntegral_algebraMap hchar)

/-- Helper for Exercise 8-8.3-10: each characteristic root of `ρ s` has finite order. -/
lemma charpoly_root_coe_isOfFinOrder_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (s : G) (hs : IsOfFinOrder s) (μ : (ρ s).charpoly.roots) :
    IsOfFinOrder (μ : ℂ) := by
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf s, hs.orderOf_pos, ?_⟩
  exact ρ.charpoly_root_pow_orderOf_eq_one s (μ := (μ : ℂ)) Multiset.coe_mem

/-- Helper for Exercise 8-8.3-10: the average of the characteristic roots of `ρ s` equals the
normalized character value. -/
lemma roots_expect_eq_inv_finrank_mul_character_local
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (s : G) :
    (𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ)) =
      ((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s := by
  have hcard : Fintype.card ((ρ s).charpoly.roots : Type) = (ρ s).charpoly.roots.card := by
    exact Multiset.card_coe ((ρ s).charpoly.roots)
  rw [Fintype.expect_eq_sum_div_card, ← Multiset.sum_eq_sum_coe ((ρ s).charpoly.roots), hcard,
    Representation.character,
    trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    ← Polynomial.Splits.natDegree_eq_card_roots (f := (ρ s).charpoly) (IsAlgClosed.splits _),
    LinearMap.charpoly_natDegree]
  simp [div_eq_mul_inv, mul_comm]

/-- Helper for Exercise 8-8.3-10: when the normalized character average is a nonzero algebraic
integer, all characteristic roots of `ρ s` equal that average. -/
lemma charpoly_roots_eq_average_of_coprime_conjClass_card_local
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)
    (hcoprime : Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V))
    (hχ : ρ.character s ≠ 0) :
    ∀ μ : (ρ s).charpoly.roots,
      (μ : ℂ) = ((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
  have hfinrank_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have h_int :
      IsIntegral ℤ (𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ)) := by
    rw [roots_expect_eq_inv_finrank_mul_character_local ρ s]
    exact average_character_isIntegral_of_coprime_conjClass_card_local ρ s hcoprime
  have h_expect_ne : (𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ)) ≠ 0 := by
    rw [roots_expect_eq_inv_finrank_mul_character_local ρ s]
    exact mul_ne_zero (inv_ne_zero hfinrank_ne) hχ
  intro μ
  have hall :=
    Finset.all_eq_expect_of_ne_zero
      (s := (Finset.univ : Finset (ρ s).charpoly.roots))
      (ζ := fun ν : (ρ s).charpoly.roots ↦ (ν : ℂ))
      (hζ := fun ν _ ↦ charpoly_root_coe_isOfFinOrder_local ρ s hs ν)
      h_int h_expect_ne
  simpa [roots_expect_eq_inv_finrank_mul_character_local ρ s] using hall μ (Finset.mem_univ μ)

/-- Helper for Exercise 8-8.3-10: coprimality of the class size and the degree forces `ρ s` to
act by a scalar whenever `ρ.character s ≠ 0`. -/
theorem exists_smul_id_of_coprime_conjClass_card_of_character_ne_zero_local
    [Finite G] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)
    (hcoprime : Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V))
    (hχ : ρ.character s ≠ 0) :
    ∃ z : ℂ, ρ s = z • 1 := by
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  let z : ℂ := ((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s
  have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
  have hconst :
      ∀ μ : (ρ s).charpoly.roots, (μ : ℂ) = z :=
    charpoly_roots_eq_average_of_coprime_conjClass_card_local ρ s hcoprime hχ
  have hunique : ∀ μ : ℂ, HasEigenvalue (ρ s) μ → μ = z := by
    intro μ hμ
    have hroot : μ ∈ (ρ s).charpoly.roots := by
      refine (Polynomial.mem_roots (ρ s).charpoly_monic.ne_zero).2 ?_
      exact (hasEigenvalue_iff_isRoot_charpoly (ρ s) μ).1 hμ
    have hcount : 0 < ((ρ s).charpoly.roots.count μ) :=
      Multiset.count_pos.2 hroot
    let ν : (ρ s).charpoly.roots := ⟨μ, ⟨0, hcount⟩⟩
    simpa [z, ν] using hconst ν
  exact ⟨z,
    eq_smul_id_of_isSemisimple_of_unique_eigenvalue_local
      (representation_isSemisimple_of_isOfFinOrder_local ρ s hs) hunique⟩

/-- Helper for Exercise 8-8.3-10: a finite non-simple group has a nontrivial proper normal
subgroup. -/
lemma exists_nontrivial_proper_normal_subgroup_of_not_isSimpleGroup
    {H : Type} [Group H] [Finite H] [Nontrivial H]
    (hsimple : ¬ IsSimpleGroup H) :
    ∃ N : Subgroup H, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  by_contra hno
  apply hsimple
  -- Every normal subgroup is forced to be either trivial or total.
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, ?_⟩
  intro N hN
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · by_cases hNtop : N = ⊤
    · exact Or.inr hNtop
    · exact False.elim <| hno ⟨N, hN, hNbot, hNtop⟩

-- Proof sketch: if `G` were simple, then it would be nontrivial by the owner class
-- `IsSimpleGroup`. Apply the previous theorem with a prime divisor of `Nat.card G` to obtain
-- `s ≠ 1` whose conjugacy class cardinality is not divisible by that prime. Since
-- `Nat.card (ConjClasses.mk s).carrier ∣ Nat.card G`, that conjugacy class cardinality is a prime
-- power. The corresponding centralizer therefore has prime-power index; then invoke Exercise
-- `6.10` to obtain a proper nontrivial normal subgroup, so `G` is not simple.
/-- Exercise 8-8.3-10 (2): source part (i). A finite group of order `p^a q^b` with trivial center
is not simple; equivalently, it has a nontrivial proper normal subgroup. -/
theorem not_isSimpleGroup_of_center_eq_bot
    (hcard : Nat.card G = p ^ a * q ^ b) (hcenter : Subgroup.center G = ⊥)
    : ¬ IsSimpleGroup G := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  letI : Finite G := Nat.finite_of_card_ne_zero hcard_ne_zero
  letI : Fintype G := Fintype.ofFinite G
  intro hsimple
  letI : IsSimpleGroup G := hsimple
  by_cases hpq : p = q
  · -- Route correction: when the two primes coincide, the group has prime-power order, so the
    -- standard `p`-group center argument already contradicts the trivial-center hypothesis.
    subst hpq
    have hprimepow : Nat.card G = p ^ (a + b) := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hcard
    have hpg : IsPGroup p G := IsPGroup.of_card hprimepow
    letI : Nontrivial G := (isSimpleGroup_iff G).mp hsimple |>.1
    have hcenter_nontriv : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hpg
    have hcenter_subsingleton : Subsingleton (Subgroup.center G) := by
      simpa [hcenter] using (inferInstance : Subsingleton (⊥ : Subgroup G))
    exact not_nontrivial_iff_subsingleton.mpr hcenter_subsingleton hcenter_nontriv
  by_cases hqdiv : q ∣ Nat.card G
  · -- Route correction: reuse the earlier-safe Chapter 6 scalar-action theorem instead of
    -- rebuilding the local character-theory package in this file.
    obtain ⟨s, hs_ne_one, hs_qnodvd⟩ :=
      exists_nontrivial_element_conjClass_card_not_dvd_of_center_eq_bot
        (q := q) hqdiv hcenter
    have hs_card_dvd : Nat.card (ConjClasses.mk s).carrier ∣ Nat.card G := by
      letI : Fintype (ConjClasses.mk s).carrier := Fintype.ofFinite (ConjClasses.mk s).carrier
      letI : Fintype (MulAction.stabilizer (ConjAct G) s) :=
        Fintype.ofFinite (MulAction.stabilizer (ConjAct G) s)
      have hstabilizer_dvd : Nat.card (MulAction.stabilizer (ConjAct G) s) ∣ Nat.card G := by
        simpa using
          (Subgroup.card_subgroup_dvd_card (MulAction.stabilizer (ConjAct G) s))
      refine ⟨Nat.card (MulAction.stabilizer (ConjAct G) s), ?_⟩
      have hcarrier :
          Nat.card (ConjClasses.mk s).carrier =
            Nat.card G / Nat.card (MulAction.stabilizer (ConjAct G) s) := by
        simpa [Nat.card_eq_fintype_card] using (ConjClasses.card_carrier (G := G) s)
      rw [hcarrier]
      exact (Nat.div_mul_cancel hstabilizer_dvd).symm
    obtain ⟨n, hs_card⟩ :=
      eq_prime_pow_of_not_dvd_of_dvd_prime_pow_mul_prime_pow
        (p := p) (q := q) (a := a) (b := b) (hcard ▸ hs_card_dvd) hs_qnodvd
    obtain ⟨W, hWsimple, hWnontriv, hWchar, hWdegree⟩ :=
      exists_irreducible_rep_with_character_ne_zero_of_conjClass_card_eq_prime_pow
        (G := G) (s := s) hs_ne_one hp hs_card
    letI : Simple W := hWsimple
    letI : Representation.IsIrreducible W.ρ := FDRep.isIrreducible_of_simple W
    have hcoprime :
        Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ W) := by
      rw [hs_card]
      exact (hp.coprime_pow_of_not_dvd hWdegree).symm
    obtain ⟨z, hzscalar⟩ :=
      exists_smul_id_of_coprime_conjClass_card_of_character_ne_zero_local
        (ρ := W.ρ) (s := s) hcoprime hWchar
    have hker_bot : W.ρ.ker = ⊥ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top (H := W.ρ.ker) inferInstance with hker | hker
      · exact hker
      · have htriv : Representation.IsTrivial W.ρ := by
          refine ⟨?_⟩
          intro g
          have hg : g ∈ W.ρ.ker := by simpa [hker]
          simpa [MonoidHom.mem_ker] using hg
        exact False.elim <| hWnontriv htriv
    have hinj : Function.Injective W.ρ := (MonoidHom.ker_eq_bot_iff W.ρ).mp hker_bot
    have hs_center : s ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hconj_image : W.ρ (g * s * g⁻¹) = W.ρ s := by
        ext v
        calc
          W.ρ (g * s * g⁻¹) v = W.ρ g (W.ρ s (W.ρ g⁻¹ v)) := by
            simp [mul_assoc]
          _ = W.ρ g (z • W.ρ g⁻¹ v) := by
            rw [hzscalar]
            simp
          _ = z • W.ρ g (W.ρ g⁻¹ v) := by
            simp
          _ = z • v := by
            simp
          _ = W.ρ s v := by
            rw [hzscalar]
            simp
      have hconj_eq : g * s * g⁻¹ = s := hinj hconj_image
      have hmul_eq := congrArg (fun x : G ↦ x * g) hconj_eq
      simpa [mul_assoc] using hmul_eq
    have hs_eq_one : s = 1 := by
      simpa [hcenter] using hs_center
    exact hs_ne_one hs_eq_one
  · -- Route correction: when `q` does not divide the order, the whole group has prime-power
    -- order, so the source proof collapses to the standard nontrivial `p`-group center argument.
    obtain ⟨n, hprimepow⟩ :=
      eq_prime_pow_of_not_dvd_of_dvd_prime_pow_mul_prime_pow
        (p := p) (q := q) (a := a) (b := b) (hcard ▸ dvd_rfl) hqdiv
    have hpg : IsPGroup p G := IsPGroup.of_card hprimepow
    by_cases hGnontriv : Nontrivial G
    · letI : Nontrivial G := hGnontriv
      have hcenter_nontriv : Nontrivial (Subgroup.center G) := IsPGroup.center_nontrivial hpg
      have hcenter_subsingleton : Subsingleton (Subgroup.center G) := by
        simpa [hcenter] using (inferInstance : Subsingleton (⊥ : Subgroup G))
      exact not_nontrivial_iff_subsingleton.mpr hcenter_subsingleton hcenter_nontriv
    · exact hGnontriv ((isSimpleGroup_iff G).mp hsimple).1

/-- Helper for Exercise 8-8.3-10: any finite group whose order divides `p ^ a * q ^ b` is
solvable. -/
lemma solvable_of_card_dvd_prime_pow_mul_prime_pow
    {H : Type} [Group H] [Finite H]
    (hdiv : Nat.card H ∣ p ^ a * q ^ b) : IsSolvable H := by
  classical
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  by_cases hpq : p = q
  · -- When the two primes coincide, every divisor is already a pure `p`-power.
    subst hpq
    have hpow_dvd : Nat.card H ∣ p ^ (a + b) := by
      simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hdiv
    obtain ⟨n, -, hpow⟩ := (Nat.dvd_prime_pow hp).mp hpow_dvd
    letI : Fact p.Prime := ⟨hp⟩
    have hpg : IsPGroup p H := IsPGroup.of_card hpow
    have hnil : Group.IsNilpotent H := hpg.isNilpotent
    letI : Group.IsNilpotent H := hnil
    infer_instance
  · by_cases hqdiv : q ∣ Nat.card H
    · by_cases hpdiv : p ∣ Nat.card H
      · by_cases hcenter : Subgroup.center H = ⊥
        · have hH_nontriv : Nontrivial H := by
            rw [← Finite.one_lt_card_iff_nontrivial]
            have hcard_ne_one : Nat.card H ≠ 1 := by
              intro hone
              exact hq.not_dvd_one (hone ▸ hqdiv)
            have hcard_pos : 0 < Nat.card H := Nat.card_pos
            omega
          letI : Nontrivial H := hH_nontriv
          obtain ⟨i, j, hHpq⟩ :=
            card_eq_prime_pow_mul_prime_pow_of_dvd_prime_pow_mul_prime_pow
              (p := p) (q := q) (a := a) (b := b) hdiv
          have hnot_simple : ¬ IsSimpleGroup H :=
            not_isSimpleGroup_of_center_eq_bot
              (G := H) (p := p) (q := q) (a := i) (b := j) hHpq hcenter
          obtain ⟨N, hNnormal, hNnebot, hNnetop⟩ :=
            exists_nontrivial_proper_normal_subgroup_of_not_isSimpleGroup
              (H := H) hnot_simple
          letI : N.Normal := hNnormal
          have hN_solvable : IsSolvable N :=
            solvable_of_card_dvd_prime_pow_mul_prime_pow
              (H := N) (dvd_trans N.card_subgroup_dvd_card hdiv)
          have hquot_solvable : IsSolvable (H ⧸ N) :=
            solvable_of_card_dvd_prime_pow_mul_prime_pow
              (H := H ⧸ N) (dvd_trans N.card_quotient_dvd_card hdiv)
          have hker_le_range :
              (QuotientGroup.mk' N).ker ≤ N.subtype.range := by
            simpa [QuotientGroup.ker_mk', Subgroup.range_subtype]
          -- Combine solvability of the normal subgroup and the quotient.
          exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) hker_le_range
        · letI : CommGroup (Subgroup.center H) :=
            Group.commGroupOfCenterEqTop (Subgroup.center_eq_top (G := Subgroup.center H))
          letI : IsSolvable (Subgroup.center H) := inferInstance
          have hquot_solvable : IsSolvable (H ⧸ Subgroup.center H) :=
            solvable_of_card_dvd_prime_pow_mul_prime_pow
              (H := H ⧸ Subgroup.center H)
              (dvd_trans (Subgroup.card_quotient_dvd_card (Subgroup.center H)) hdiv)
          have hker_le_range :
              (QuotientGroup.mk' (Subgroup.center H)).ker ≤
                (Subgroup.center H).subtype.range := by
            simpa [QuotientGroup.ker_mk', Subgroup.range_subtype]
          -- The center is commutative, so solvability lifts from the quotient.
          exact
            solvable_of_ker_le_range
              (Subgroup.center H).subtype
              (QuotientGroup.mk' (Subgroup.center H))
              hker_le_range
      · obtain ⟨j, hqpow⟩ :=
          eq_prime_pow_of_not_dvd_of_dvd_prime_pow_mul_prime_pow
            (p := q) (q := p) (a := b) (b := a)
            (by simpa [mul_comm, mul_left_comm, mul_assoc] using hdiv) hpdiv
        letI : Fact q.Prime := ⟨hq⟩
        have hqg : IsPGroup q H := IsPGroup.of_card hqpow
        have hnil : Group.IsNilpotent H := hqg.isNilpotent
        letI : Group.IsNilpotent H := hnil
        infer_instance
    · obtain ⟨i, hppow⟩ :=
        eq_prime_pow_of_not_dvd_of_dvd_prime_pow_mul_prime_pow
          (p := p) (q := q) (a := a) (b := b) hdiv hqdiv
      letI : Fact p.Prime := ⟨hp⟩
      have hpg : IsPGroup p H := IsPGroup.of_card hppow
      have hnil : Group.IsNilpotent H := hpg.isNilpotent
      letI : Group.IsNilpotent H := hnil
      infer_instance
termination_by Nat.card H
decreasing_by
  · rw [← N.index_mul_card]
    exact
      lt_mul_of_one_lt_left Nat.card_pos
        (N.one_lt_index_of_ne_top hNnetop)
  · rw [← N.index_eq_card, ← N.index_mul_card]
    exact
      lt_mul_of_one_lt_right
        (Nat.pos_of_ne_zero N.index_ne_zero_of_finite)
        (N.one_lt_card_iff_ne_bot.mpr hNnebot)
  · rw [← (Subgroup.center H).index_eq_card, ← (Subgroup.center H).index_mul_card]
    exact
      lt_mul_of_one_lt_right
        (Nat.pos_of_ne_zero (Subgroup.center H).index_ne_zero_of_finite)
        ((Subgroup.center H).one_lt_card_iff_ne_bot.mpr hcenter)

-- Proof sketch: induct on `Nat.card G`. If the center is nontrivial, pass to `G ⧸ center G`; if
-- the center is trivial, use the previous theorem in the nontrivial case to find a proper
-- nontrivial normal subgroup and combine solvability of the subgroup and quotient by the induction
-- hypothesis. The prime-power boundary cases are handled separately as finite `p`-groups.
/-- Exercise 8-8.3-10 (3): source part (ii). Burnside's theorem for groups of order `p^a q^b`. -/
theorem burnside_solvable_of_card_eq_prime_pow_mul_prime_pow
    (hcard : Nat.card G = p ^ a * q ^ b) : IsSolvable G := by
  have hp : Nat.Prime p := Fact.out
  have hq : Nat.Prime q := Fact.out
  have hcard_ne_zero : Nat.card G ≠ 0 := by
    rw [hcard]
    exact mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  letI : Finite G := Nat.finite_of_card_ne_zero hcard_ne_zero
  -- Reduce the exact-order hypothesis to the divisor form handled by the induction theorem.
  exact
    solvable_of_card_dvd_prime_pow_mul_prime_pow
      (p := p) (q := q) (a := a) (b := b) (hcard ▸ dvd_rfl)

-- Source/core/bridge triage: this is `bridge/view`. The core owner is the exact mathlib theorem
-- `alternatingGroup.card_of_card_eq_four`; the source-facing statement just rewrites the resulting
-- cardinality `12` as `2^2 * 3`.
/-- Exercise 8-8.3-10 (4): source part (iii). The alternating group `A₄` has order `2^2 * 3`. -/
theorem alternatingGroup_fin4_card_eq_two_pow_two_mul_three :
    Nat.card A4 = 2 ^ 2 * 3 := by
  rw [alternatingGroup.card_of_card_eq_four (by simp)]
  norm_num

/-- Helper for Exercise 8-8.3-10: a nontrivial supersolvable group has a nontrivial normal cyclic
subgroup, obtained from the first nontrivial term in a supersolvable series. -/
lemma exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable
    {Q : Type u} [Group Q] [IsSupersolvable Q] [Nontrivial Q] :
    ∃ B : Subgroup Q, B.Normal ∧ B ≠ ⊥ ∧ IsCyclic B := by
  classical
  let hsup : IsSupersolvable Q := inferInstance
  rcases hsup.supersolvable with ⟨n, f, _, hnormal, hcyclic, h0, hn⟩
  -- Choose the earliest nontrivial term in the supersolvable series.
  have hex : ∃ m, m ≤ n ∧ f m ≠ ⊥ := by
    refine ⟨n, le_rfl, ?_⟩
    simp [hn]
  let m := Nat.find hex
  have hm_le_n : m ≤ n := (Nat.find_spec hex).1
  have hm_ne_bot : f m ≠ ⊥ := (Nat.find_spec hex).2
  have hm_min : ∀ k, k < m → f k = ⊥ := by
    intro k hk
    by_contra hk_ne_bot
    have hk_witness : k ≤ n ∧ f k ≠ ⊥ :=
      ⟨Nat.le_trans (Nat.le_of_lt hk) hm_le_n, hk_ne_bot⟩
    exact Nat.find_min hex hk hk_witness
  have hm_ne_zero : m ≠ 0 := by
    intro hm0
    apply hm_ne_bot
    simp [m, hm0, h0]
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_ne_zero
  have hk1_le_n : k + 1 ≤ n := by
    simpa [m, hk_eq] using hm_le_n
  have hk_lt : k < n := Nat.lt_of_succ_le hk1_le_n
  have hk_bot : f k = ⊥ := hm_min k (by simp [m, hk_eq])
  -- The first nontrivial term is normal, and its predecessor quotient is cyclic.
  have hk1_normal : (f (k + 1)).Normal := by
    by_cases hk1_lt_n : k + 1 < n
    · exact hnormal (k + 1) hk1_lt_n
    · have hk1_eq_n : k + 1 = n := le_antisymm hk1_le_n (Nat.le_of_not_gt hk1_lt_n)
      rw [hk1_eq_n, hn]
      infer_instance
  refine ⟨f (k + 1), hk1_normal, ?_, ?_⟩
  · simpa [m, hk_eq] using hm_ne_bot
  · letI : (f k).Normal := hnormal k hk_lt
    letI : ((f k).subgroupOf (f (k + 1))).Normal := (hnormal k hk_lt).subgroupOf (f (k + 1))
    let e : f (k + 1) ⧸ (f k).subgroupOf (f (k + 1)) ≃*
        f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1))) :=
      QuotientGroup.quotientMulEquivOfEq (by simp [hk_bot])
    -- Replace the trivial predecessor by `⊥`, then identify the resulting quotient with the group.
    have hcyc_quot : IsCyclic (f (k + 1) ⧸ (⊥ : Subgroup (f (k + 1)))) :=
      e.isCyclic.mp (hcyclic k hk_lt)
    exact (QuotientGroup.quotientBot (G := f (k + 1))).isCyclic.mp hcyc_quot

/-- Helper for Exercise 8-8.3-10: a normal subgroup of order `2` lies in the center. -/
lemma normal_cyclic_subgroup_card_two_le_center
    {Q : Type u} [Group Q] (H : Subgroup Q)
    (hHnormal : H.Normal) (hHcard : Nat.card H = 2) :
    H ≤ Subgroup.center Q := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hx1 : x = 1
  · simp [hx1]
  -- In a group of order `2`, the nonidentity element is unique.
  have hunique : ∃! y : H, y ≠ 1 := by
    simpa using (Nat.card_eq_two_iff' (1 : H)).mp hHcard
  have hx_unique : (⟨x, hx⟩ : H) ≠ 1 := by
    simpa using hx1
  have hconj_mem : g * x * g⁻¹ ∈ H := hHnormal.conj_mem x hx g
  have hconj_ne_one : (⟨g * x * g⁻¹, hconj_mem⟩ : H) ≠ 1 := by
    intro h
    apply hx1
    have hval : g * x * g⁻¹ = 1 := by
      simpa using congrArg Subtype.val h
    have := congrArg (fun z : Q ↦ g⁻¹ * z * g) hval
    simpa [mul_assoc] using this
  -- Conjugation preserves `H`, so it must fix that unique nonidentity element.
  have hconj_eq : g * x * g⁻¹ = x := by
    exact congrArg Subtype.val (ExistsUnique.unique hunique hconj_ne_one hx_unique)
  have := congrArg (fun z : Q ↦ z * g) hconj_eq
  simpa [mul_assoc] using this

/-- Helper for Exercise 8-8.3-10: `A₄` has no nontrivial normal cyclic subgroup. -/
lemma alternatingGroup_fin4_no_nontrivial_normal_cyclic_subgroup :
    ¬ ∃ H : Subgroup A4, H.Normal ∧ H ≠ ⊥ ∧ IsCyclic H := by
  classical
  rintro ⟨H, hHnormal, hHbot, hHcyc⟩
  have hA4card : Nat.card A4 = 12 := by
    simpa using alternatingGroup.card_of_card_eq_four (α := Fin 4) (by simp)
  have hcenter_bot : Subgroup.center A4 = ⊥ :=
    alternatingGroup.center_eq_bot (α := Fin 4) (by simp)
  by_cases hHcard2 : Nat.card H = 2
  · -- The order-`2` case collapses to the trivial center of `A₄`.
    have hHcenter : H ≤ Subgroup.center A4 :=
      normal_cyclic_subgroup_card_two_le_center H hHnormal hHcard2
    have hHle_bot : H ≤ ⊥ := by
      simpa [hcenter_bot] using hHcenter
    exact hHbot (le_antisymm hHle_bot bot_le)
  · letI : H.Normal := hHnormal
    letI : IsCyclic H := hHcyc
    have hHcard_ne_one : Nat.card H ≠ 1 := by
      intro h1
      exact hHbot (Subgroup.card_eq_one.mp h1)
    have hquot_mul : 12 = Nat.card (A4 ⧸ H) * Nat.card H := by
      simpa [hA4card] using
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := A4) H)
    have hquot_dvd : Nat.card (A4 ⧸ H) ∣ 12 := by
      simpa [hA4card] using (Subgroup.card_quotient_dvd_card (α := A4) H)
    have hquot_pos : 0 < Nat.card (A4 ⧸ H) := Nat.card_pos
    have hquot_le_twelve : Nat.card (A4 ⧸ H) ≤ 12 := Nat.le_of_dvd (by decide) hquot_dvd
    -- Route correction: instead of enumerating subgroups of `A₄`, force the quotient to be
    -- commutative and then compare with the Klein four commutator subgroup.
    have hquot_comm : IsMulCommutative (A4 ⧸ H) := by
      interval_cases hq : Nat.card (A4 ⧸ H)
      · have hsub : Subsingleton (A4 ⧸ H) := (Nat.card_eq_one_iff_unique.mp hq).1
        letI : Subsingleton (A4 ⧸ H) := hsub
        infer_instance
      · exact (isCyclic_of_prime_card hq).isMulCommutative
      · exact (isCyclic_of_prime_card hq).isMulCommutative
      · letI : CommGroup (A4 ⧸ H) :=
          IsPGroup.commGroupOfCardEqPrimeSq (G := A4 ⧸ H) (p := 2) hq
        infer_instance
      · norm_num at hquot_dvd
      · have : Nat.card H = 2 := by
          omega
        exact False.elim (hHcard2 this)
      · norm_num at hquot_dvd
      · norm_num at hquot_dvd
      · norm_num at hquot_dvd
      · norm_num at hquot_dvd
      · norm_num at hquot_dvd
      · have : Nat.card H = 1 := by
          omega
        exact False.elim (hHcard_ne_one this)
    have hcomm_le : commutator A4 ≤ H :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := H)).mp hquot_comm
    -- The commutator subgroup of `A₄` is the Klein four group, which is not cyclic.
    have hklein_le : alternatingGroup.kleinFour (Fin 4) ≤ H := by
      rw [alternatingGroup.kleinFour_eq_commutator (α := Fin 4) (by simp)]
      exact hcomm_le
    have hklein_cyclic : IsCyclic (alternatingGroup.kleinFour (Fin 4)) :=
      Subgroup.isCyclic_of_le hklein_le
    letI : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
      alternatingGroup.kleinFour_isKleinFour (α := Fin 4) (by simp)
    exact IsKleinFour.not_isCyclic hklein_cyclic

-- Proof sketch: use the canonical normal Klein four subgroup
-- `alternatingGroup.kleinFour (Fin 4)` from Exercise `8-8.2-3`; every nontrivial proper normal
-- subgroup is that owner, whose quotient is cyclic of order `3`, but no refinement yields a
-- normal series with all cyclic factors.
/-- Exercise 8-8.3-10 (5): source part (iii). The alternating group `A₄` is not supersolvable. -/
theorem alternatingGroup_fin4_not_supersolvable :
    ¬ IsSupersolvable A4 := by
  intro hsup
  letI : IsSupersolvable A4 := hsup
  have hA4nontriv : Nontrivial A4 := by
    rw [← Finite.one_lt_card_iff_nontrivial, alternatingGroup.card_of_card_eq_four (by simp)]
    norm_num
  letI : Nontrivial A4 := hA4nontriv
  -- A supersolvable `A₄` would supply a nontrivial normal cyclic subgroup, which we have just
  -- ruled out by the conjugation-action argument.
  obtain ⟨H, hHnormal, hHbot, hHcyc⟩ :=
    exists_nontrivial_normal_cyclic_subgroup_of_nontrivial_supersolvable (Q := A4)
  exact
    alternatingGroup_fin4_no_nontrivial_normal_cyclic_subgroup
      ⟨H, hHnormal, hHbot, hHcyc⟩

-- Source/core/bridge triage: this is `bridge/view`. The core owner is `Nat.card_perm`; the
-- source-facing statement specializes it to `Fin 5` and rewrites `5!` as `2^3 * 3 * 5`.
/-- Exercise 8-8.3-10 (6): source part (iv). The symmetric group `S₅` has order `2^3 * 3 * 5`. -/
theorem symmetricGroup_fin5_card_eq_two_pow_three_mul_three_mul_five :
    Nat.card (Equiv.Perm (Fin 5)) = 2 ^ 3 * 3 * 5 := by
  rw [Nat.card_perm]
  norm_num

/- Exercise 8-8.3-10 (7): source part (iv). The symmetric group `Equiv.Perm (Fin 5)` is not
solvable; this is the standard mathlib theorem `Equiv.Perm.fin_5_not_solvable`. -/
recall Equiv.Perm.fin_5_not_solvable

end
