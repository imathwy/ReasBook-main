import Mathlib
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_6_6_5_8 (from Chap06) -/
open scoped BigOperators

noncomputable section

-- Proof sketch: every conjugate of `a` is again the average of roots of unity, so each conjugate
-- has complex absolute value at most `1` by the triangle inequality. The norm of `a` over `ℚ`,
-- being the product of these conjugates, is therefore an integer of absolute value at most `1`.
-- Hence the norm is `0`, forcing `a = 0`, or it is a unit; in the latter case equality must hold
-- in the triangle inequality for each conjugate, which implies that all the roots of unity are
-- equal and coincide with their average.
variable {ι : Type*}

namespace Finset

/-- Helper for Exercise 6-6.5-8: the average of finitely many complex roots of unity lies in the
closed unit disk. -/
lemma expect_norm_le_one_of_isOfFinOrder
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, IsOfFinOrder (ζ i)) :
    ‖𝔼 i ∈ s, ζ i‖ ≤ 1 := by
  -- Rewrite the expectation as a sum divided by the cardinality.
  have hsum :
      ‖∑ i ∈ s, ζ i‖ ≤ (s.card : ℝ) := by
    -- The triangle inequality is sharp enough because every summand has norm `1`.
    calc
      ‖∑ i ∈ s, ζ i‖ ≤ ∑ i ∈ s, ‖ζ i‖ := norm_sum_le _ _
      _ = (s.card : ℝ) := by
        have hone : ∑ i ∈ s, ‖ζ i‖ = ∑ i ∈ s, (1 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using (hζ i hi).norm_eq_one
        simpa using hone
  have hdiv :
      ‖∑ i ∈ s, ζ i‖ / (s.card : ℝ) ≤ (s.card : ℝ) / (s.card : ℝ) :=
    div_le_div_of_nonneg_right hsum (Nat.cast_nonneg s.card)
  calc
    ‖𝔼 i ∈ s, ζ i‖ = ‖∑ i ∈ s, ζ i‖ / (s.card : ℝ) := by
      rw [Finset.expect_eq_sum_div_card]
      simp
    _ ≤ (s.card : ℝ) / (s.card : ℝ) := hdiv
    _ ≤ 1 := by
      by_cases hs : s.card = 0
      · simp [hs]
      · simp [hs]

/-- Helper for Exercise 6-6.5-8: a nonzero algebraic-integer average of roots of unity is itself a
root of unity, hence has complex norm `1`. -/
lemma expect_norm_eq_one_of_ne_zero_of_isIntegral_of_isOfFinOrder
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, IsOfFinOrder (ζ i))
    (h_int : IsIntegral ℤ (𝔼 i ∈ s, ζ i)) (h0 : (𝔼 i ∈ s, ζ i) ≠ 0) :
    ‖𝔼 i ∈ s, ζ i‖ = 1 := by
  classical
  let K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (ζ '' (↑s : Set ι))
  letI : Finite (ζ '' (↑s : Set ι)) :=
    (Set.Finite.image (f := ζ) s.finite_toSet).to_subtype
  letI : FiniteDimensional ℚ K :=
    IntermediateField.finiteDimensional_adjoin (K := ℚ) (S := ζ '' (↑s : Set ι)) fun x hx => by
      rcases hx with ⟨i, hi, rfl⟩
      rcases isOfFinOrder_iff_pow_eq_one.mp (hζ i hi) with ⟨n, hn, hpow⟩
      exact IsIntegral.of_pow hn (hpow ▸ isIntegral_one)
  letI : NumberField K := NumberField.of_module_finite ℚ K
  let ζK : {i // i ∈ s} → K := fun i ↦
    ⟨ζ i, IntermediateField.subset_adjoin ℚ (ζ '' (↑s : Set ι)) ⟨i, i.2, rfl⟩⟩
  let aK : K := 𝔼 i : {i // i ∈ s}, ζK i
  have h_expect :
      ((aK : K) : ℂ) = 𝔼 i ∈ s, ζ i := by
    -- Compare the subtype-index average in `K` with the original average in `ℂ`.
    have hsum_attach : (∑ i : {i // i ∈ s}, ζ i) = ∑ i ∈ s, ζ i := by
      simpa using (Finset.sum_attach (s := s) (f := ζ))
    calc
      (((aK : K) : ℂ)) =
          (∑ i : {i // i ∈ s}, (((ζK i : K) : K) : ℂ)) / Fintype.card {i // i ∈ s} := by
        simp [aK, Fintype.expect_eq_sum_div_card]
      _ = (∑ i ∈ s, ζ i) / Fintype.card {i // i ∈ s} := by
        rw [hsum_attach]
      _ = 𝔼 i ∈ s, ζ i := by
        rw [Finset.expect_eq_sum_div_card, Fintype.card_coe]
  have h_intK : IsIntegral ℤ aK := by
    -- Transport algebraic integrality back through the embedding `K ↪ ℂ`.
    apply (isIntegral_algebraMap_iff (algebraMap K ℂ).injective).mp
    simpa [h_expect] using h_int
  have h0K : aK ≠ 0 := by
    intro haK
    have hzero : (((aK : K) : ℂ)) = 0 := by
      simpa using congrArg (fun x : K ↦ ((x : K) : ℂ)) haK
    exact h0 (by simpa [h_expect] using hzero)
  have hζK : ∀ i : {i // i ∈ s}, IsOfFinOrder (ζK i) := by
    intro i
    rcases isOfFinOrder_iff_pow_eq_one.mp (hζ i i.2) with ⟨n, hn, hpow⟩
    refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
    apply (algebraMap K ℂ).injective
    simpa [ζK] using hpow
  have hbound : ∀ φ : K →+* ℂ, ‖φ aK‖ ≤ 1 := by
    intro φ
    have hφ :
        φ aK = 𝔼 i ∈ (Finset.univ : Finset {i // i ∈ s}), φ (ζK i) := by
      rw [Finset.expect_eq_sum_div_card]
      simp [aK, Fintype.expect_eq_sum_div_card, Fintype.card_coe]
    have hφζ : ∀ i ∈ (Finset.univ : Finset {i // i ∈ s}), IsOfFinOrder (φ (ζK i)) := by
      intro i hi
      exact φ.toMonoidHom.isOfFinOrder (hζK i)
    -- Each complex embedding again averages roots of unity, so the same unit-disk bound applies.
    simpa [hφ] using
      expect_norm_le_one_of_isOfFinOrder (Finset.univ : Finset {i // i ∈ s})
        (fun i ↦ φ (ζK i)) hφζ
  obtain ⟨n, hn, hpow⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one (K := K) (A := ℂ) h0K h_intK hbound
  have hpow_complex : (((aK : K) : ℂ) ^ n) = 1 := by
    simpa using congrArg (fun x : K ↦ ((x : K) : ℂ)) hpow
  have hnormK : ‖((aK : K) : ℂ)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow_complex (Nat.ne_of_gt hn)
  simpa [h_expect] using hnormK

/-- Helper for Exercise 6-6.5-8: if a sum of unit complex numbers has maximal possible norm, then
all summands are equal. -/
lemma exists_common_value_of_norm_sum_eq_card
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, ‖ζ i‖ = 1)
    (hsum : ‖∑ i ∈ s, ζ i‖ = s.card) :
    ∃ z : ℂ, ∀ i ∈ s, ζ i = z := by
  classical
  revert hζ hsum
  induction s using Finset.induction_on with
  | empty =>
      intro hζ hsum
      refine ⟨1, ?_⟩
      simp
  | @insert a s ha ih =>
      intro hζ hsum
      have hζa : ‖ζ a‖ = 1 := hζ a (by simp)
      have hζs : ∀ i ∈ s, ‖ζ i‖ = 1 := fun i hi ↦ hζ i (by simp [hi])
      have hsum_rest_le : ‖∑ i ∈ s, ζ i‖ ≤ (s.card : ℝ) := by
        calc
          ‖∑ i ∈ s, ζ i‖ ≤ ∑ i ∈ s, ‖ζ i‖ := norm_sum_le _ _
          _ = (s.card : ℝ) := by
            have hone : ∑ i ∈ s, ‖ζ i‖ = ∑ i ∈ s, (1 : ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa using hζs i hi
            simpa using hone
      have hinsert :
          ‖ζ a + ∑ i ∈ s, ζ i‖ = 1 + (s.card : ℝ) := by
        simpa [Finset.sum_insert, ha, Nat.cast_add, add_comm, hζa] using hsum
      have hsum_rest :
          ‖∑ i ∈ s, ζ i‖ = (s.card : ℝ) := by
        have haux :
            1 + (s.card : ℝ) ≤ 1 + ‖∑ i ∈ s, ζ i‖ := by
          calc
            1 + (s.card : ℝ) = ‖ζ a + ∑ i ∈ s, ζ i‖ := hinsert.symm
            _ ≤ ‖ζ a‖ + ‖∑ i ∈ s, ζ i‖ := norm_add_le _ _
            _ = 1 + ‖∑ i ∈ s, ζ i‖ := by simp [hζa]
        linarith
      have hnorm_add :
          ‖ζ a + ∑ i ∈ s, ζ i‖ = ‖ζ a‖ + ‖∑ i ∈ s, ζ i‖ := by
        apply le_antisymm (norm_add_le _ _)
        rw [hinsert, hζa, hsum_rest]
      by_cases hs0 : s.card = 0
      · have hs : s = ∅ := Finset.card_eq_zero.mp hs0
        refine ⟨ζ a, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · rfl
        · simp [hs] at hi
      obtain ⟨z, hz⟩ := ih hζs hsum_rest
      have hcollinear :
          (s.card : ℝ) • ζ a = ∑ i ∈ s, ζ i := by
        have hray := (norm_add_eq_iff_real).mp hnorm_add
        simpa [hζa, hsum_rest] using hray
      have hsum_rest_eq :
          ∑ i ∈ s, ζ i = (s.card : ℂ) * z := by
        calc
          ∑ i ∈ s, ζ i = ∑ i ∈ s, z := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hz i hi
          _ = (s.card : ℂ) * z := by
            simp [nsmul_eq_mul]
      have hza : ζ a = z := by
        have hsC : (s.card : ℂ) ≠ 0 := by
          exact_mod_cast hs0
        have hmul :
            (s.card : ℂ) * ζ a = (s.card : ℂ) * z := by
          simpa [Algebra.smul_def, hsum_rest_eq] using hcollinear
        have := congrArg (fun w : ℂ ↦ (s.card : ℂ)⁻¹ * w) hmul
        simpa [hsC] using this
      refine ⟨z, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact hza
      · exact hz i hi

/-- Helper for Exercise 6-6.5-8: if the average of roots of unity has norm `1`, then every summand
is equal to that average. -/
lemma all_eq_expect_of_norm_expect_eq_one_of_isOfFinOrder
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, IsOfFinOrder (ζ i))
    (hnorm : ‖𝔼 i ∈ s, ζ i‖ = 1) :
    ∀ i ∈ s, ζ i = 𝔼 i ∈ s, ζ i := by
  classical
  have hs : s.Nonempty := by
    by_contra hs
    have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs'] at hnorm
  have hs0 : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hsum_div :
      ‖∑ i ∈ s, ζ i‖ / (s.card : ℝ) = 1 := by
    -- Rewrite the average norm in sum-over-cardinality form.
    calc
      ‖∑ i ∈ s, ζ i‖ / (s.card : ℝ) = ‖𝔼 i ∈ s, ζ i‖ := by
        rw [Finset.expect_eq_sum_div_card]
        simp
      _ = 1 := hnorm
  have hsum :
      ‖∑ i ∈ s, ζ i‖ = s.card := by
    exact (div_eq_one_iff_eq hs0).mp hsum_div
  have hnorm_terms : ∀ i ∈ s, ‖ζ i‖ = 1 := fun i hi ↦ (hζ i hi).norm_eq_one
  obtain ⟨z, hz⟩ := exists_common_value_of_norm_sum_eq_card s ζ hnorm_terms hsum
  have h_expect_eq : 𝔼 i ∈ s, ζ i = z := by
    -- Averaging a constant family recovers that common value.
    calc
      𝔼 i ∈ s, ζ i = 𝔼 i ∈ s, z := by
        refine Finset.expect_congr rfl ?_
        intro i hi
        exact hz i hi
      _ = z := Finset.expect_const hs z
  intro i hi
  rw [hz i hi, h_expect_eq.symm]

-- Source/core/bridge triage:
-- * source-facing: `expect_eq_zero_or_all_eq_of_isIntegral_of_isOfFinOrder`.
-- * core/canonical owner: `Finset.expect`.
-- * bridge/view: the source phrase “arithmetic mean of roots of unity” is expressed through the
--   canonical `expect` notation and the owner predicate `IsOfFinOrder`.
-- Primitive data: the finite family `ζ` indexed by `s` together with the root-of-unity hypothesis
-- `hζ`.
-- Derived API: `all_eq_expect_of_ne_zero` isolates the nonzero branch that downstream arguments
-- typically use.
/-- Exercise 6-6.5-8: if `a` is the arithmetic mean of finitely many complex roots of unity and is
an algebraic integer, then either that mean is `0`, or every root in the family is equal to it. -/
theorem expect_eq_zero_or_all_eq_of_isIntegral_of_isOfFinOrder
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, IsOfFinOrder (ζ i))
    (h_int : IsIntegral ℤ (𝔼 i ∈ s, ζ i)) :
    (𝔼 i ∈ s, ζ i) = 0 ∨ ∀ i ∈ s, ζ i = 𝔼 i ∈ s, ζ i := by
  by_cases h0 : (𝔼 i ∈ s, ζ i) = 0
  · exact Or.inl h0
  · -- In the nonzero branch, Kronecker's theorem forces the average to have norm `1`.
    refine Or.inr <|
      all_eq_expect_of_norm_expect_eq_one_of_isOfFinOrder s ζ hζ
        (expect_norm_eq_one_of_ne_zero_of_isIntegral_of_isOfFinOrder s ζ hζ h_int h0)

/-- Derived form of Exercise 6-6.5-8: if the arithmetic mean of finitely many complex roots of
unity is a nonzero algebraic integer, then every root in the family equals that mean. -/
theorem all_eq_expect_of_ne_zero
    (s : Finset ι) (ζ : ι → ℂ) (hζ : ∀ i ∈ s, IsOfFinOrder (ζ i))
    (h_int : IsIntegral ℤ (𝔼 i ∈ s, ζ i)) (h_expect : (𝔼 i ∈ s, ζ i) ≠ 0) :
    ∀ i ∈ s, ζ i = 𝔼 i ∈ s, ζ i := by
  rcases expect_eq_zero_or_all_eq_of_isIntegral_of_isOfFinOrder s ζ hζ h_int with
    h_zero | h_all
  · exact (h_expect h_zero).elim
  · exact h_all

end Finset

end

/-! ### Exercise_6_6_5_9 (from Chap06) -/
universe u v

namespace Representation

open scoped BigOperators MonoidAlgebra
open Module.End Polynomial

noncomputable section

section IrreducibleFiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)

-- Source/core/bridge triage:
-- * source-facing: the two exercise statements below.
-- * core/canonical owners for part (1): `conjugacyClassSumInCenter` and
--   `isIntegral_finrank_inv_sum_coeff_mul_character`.
-- * core/canonical owners for part (2): `Finset.all_eq_expect_of_ne_zero` and
--   `character_norm_eq_char_one_iff_exists_smul_id`.
-- Primitive data: the irreducible representation `ρ`, the group element `s`, and the arithmetic
-- hypotheses on the conjugacy-class cardinality and the character value.
-- Derived API: the algebraic-integrality scalar from the central class sum, and the resulting
-- scalar-action conclusion for `ρ s`.
--
-- Proof sketch: apply `isIntegral_finrank_inv_sum_coeff_mul_character` to the canonical central
-- class sum `conjugacyClassSumInCenter (ConjClasses.mk s)`. Its coefficients are `0` or `1`, so
-- the normalized character sum is exactly the class cardinality times `ρ.character s` divided by
-- `Module.finrank ℂ V`.
/-- Exercise 6-6.5-9 (1): for an irreducible finite-dimensional complex representation, the
character value at `s` multiplied by the size of the conjugacy class of `s` and divided by the
degree is an algebraic integer. -/
theorem isIntegral_conjClass_card_div_finrank_mul_character
    : by
        letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
        exact
          IsIntegral ℤ
            (((Nat.card (ConjClasses.mk s).carrier : ℂ) / Module.finrank ℂ V) *
              ρ.character s) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
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

/-- Helper for Exercise 6-6.5-9: coprimality upgrades the class-sum integrality from part (1) to
integrality of the normalized character average `(1 / dim V) * χ(s)`. -/
lemma average_character_isIntegral_of_coprime_conjClass_card
    (hcoprime : by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V)) :
    by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact IsIntegral ℤ (((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s) := by
  classical
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
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
    simpa [c, n] using isIntegral_conjClass_card_div_finrank_mul_character ρ s
  have hchar : IsIntegral ℤ (ρ.character s) := char_isIntegral ρ s
  have hfinrank_ne : (n : ℂ) ≠ 0 := by
    exact_mod_cast ((Module.finrank_pos : 0 < Module.finrank ℂ V)).ne'
  have hbez : (1 : ℤ) = c * Nat.gcdA c n + n * Nat.gcdB c n := by
    simpa [hcoprime_cn.gcd_eq_one] using Nat.gcd_eq_gcd_ab c n
  have hbezC : (1 : ℂ) = (c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n := by
    exact_mod_cast hbez
  have hdecomp :
      ((n : ℂ)⁻¹) * ρ.character s =
        (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
          (Nat.gcdB c n : ℂ) * ρ.character s := by
    -- Expand the Bézout identity after multiplying by `n⁻¹ * χ(s)`.
    calc
      ((n : ℂ)⁻¹) * ρ.character s
          = (((1 : ℂ) * (n : ℂ)⁻¹) : ℂ) * ρ.character s := by simp
      _ = ((((c : ℂ) * Nat.gcdA c n + (n : ℂ) * Nat.gcdB c n) * (n : ℂ)⁻¹) : ℂ) *
            ρ.character s := by rw [hbezC]
      _ = (Nat.gcdA c n : ℂ) * (((c : ℂ) / n) * ρ.character s) +
            (Nat.gcdB c n : ℂ) * ρ.character s := by
          field_simp [hfinrank_ne]
  -- Each Bézout summand is integral, so their sum is integral as well.
  rw [hdecomp]
  exact
    IsIntegral.add
      (IsIntegral.mul isIntegral_algebraMap hclass)
      (IsIntegral.mul isIntegral_algebraMap hchar)

end IrreducibleFiniteGroup

section IrreducibleFiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) [ρ.IsIrreducible] (s : G)

-- Proof sketch: by part (1), coprimality of the class size and the degree implies that
-- `(Module.finrank ℂ V : ℂ)⁻¹ * ρ.character s` is an algebraic integer. Apply Exercise 6.8 to the
-- characteristic roots of `ρ s`, indexed with multiplicity by the coerced multiset
-- `(ρ s).charpoly.roots`; the nonzero-average hypothesis comes from `hχ`. This shows that the
-- normalized character average has norm `1`, so the Chapter 6 owner
-- `character_norm_eq_char_one_iff_exists_smul_id` closes the scalar-action conclusion.
/-- Exercise 6-6.5-9 (2): if the size of the conjugacy class of `s` is relatively prime to the
degree of an irreducible finite-dimensional complex representation and `χ(s) ≠ 0`, then `ρ s` is
a homothety. -/
theorem exists_smul_id_of_coprime_conjClass_card_of_character_ne_zero
    (hcoprime : by
      letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
      exact Nat.Coprime (Nat.card (ConjClasses.mk s).carrier) (Module.finrank ℂ V))
    (hχ : ρ.character s ≠ 0) :
    ∃ z : ℂ, ρ s = z • 1 := by
  letI : FiniteDimensional ℂ V := IsIrreducible.finiteDimensional_of_finite ρ
  letI : Module ℂ[G] V := ρ.instModuleMonoidAlgebraAsModule
  letI : IsSimpleModule ℂ[G] V :=
    (irreducible_iff_isSimpleModule_asModule ρ).mp inferInstance
  letI : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] V
  have hs : IsOfFinOrder s := isOfFinOrder_of_finite s
  let z : ℂ := 𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ)
  have hfinrank_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    exact_mod_cast ((Module.finrank_pos : 0 < Module.finrank ℂ V)).ne'
  have hz_eq : z = ((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s := by
    have hcard : Fintype.card ((ρ s).charpoly.roots : Type) = (ρ s).charpoly.roots.card := by
      simp
    rw [show z = 𝔼 μ : (ρ s).charpoly.roots, (μ : ℂ) by rfl, Fintype.expect_eq_sum_div_card,
      ← Multiset.sum_eq_sum_coe ((ρ s).charpoly.roots), hcard, Representation.character,
      trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
      ← (IsAlgClosed.splits ((ρ s).charpoly)).natDegree_eq_card_roots,
      LinearMap.charpoly_natDegree]
    simp [div_eq_mul_inv, mul_comm]
  have hz_int : IsIntegral ℤ z := by
    rw [hz_eq]
    exact average_character_isIntegral_of_coprime_conjClass_card ρ s hcoprime
  have hz_ne : z ≠ 0 := by
    rw [hz_eq]
    exact mul_ne_zero (inv_ne_zero hfinrank_ne) hχ
  have hz_norm : ‖z‖ = 1 := by
    exact
      Finset.expect_norm_eq_one_of_ne_zero_of_isIntegral_of_isOfFinOrder
        (Finset.univ : Finset (ρ s).charpoly.roots)
        (fun μ : (ρ s).charpoly.roots ↦ (μ : ℂ))
        (fun μ _ ↦ by
          refine isOfFinOrder_iff_pow_eq_one.2 ⟨orderOf s, hs.orderOf_pos, ?_⟩
          have hμ : (μ : ℂ) ∈ (ρ s).charpoly.roots := by
            simpa using (μ.2 : 0 < ((ρ s).charpoly.roots.count μ))
          simpa using ρ.charpoly_root_pow_orderOf_eq_one s hμ)
        hz_int hz_ne
  have hchar_eq : ρ.character s = (Module.finrank ℂ V : ℂ) * z := by
    calc
      ρ.character s =
          (Module.finrank ℂ V : ℂ) * (((Module.finrank ℂ V : ℂ)⁻¹) * ρ.character s) := by
            field_simp [hfinrank_ne]
      _ = (Module.finrank ℂ V : ℂ) * z := by rw [← hz_eq]
  have hnorm : ‖ρ.character s‖ = Module.finrank ℂ V := by
    rw [hchar_eq]
    simp [hz_norm]
  exact (character_norm_eq_char_one_iff_exists_smul_id ρ s hs).1 hnorm

end IrreducibleFiniteGroup

end

end Representation

/-! ### Proposition_6_6_5_1 (from Chap06) -/
universe u v w

namespace Representation

section

open Module.End

variable {G : Type u} [Group G]
variable {k : Type w} [Field k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

-- Source/core/bridge triage:
-- * source-facing: `char_isIntegral`.
-- * core/canonical owner: `Representation.character`.
-- * bridge/generalization: `char_isIntegral_of_isOfFinOrder`.
--
-- Proof sketch: if `s` has finite order, then the linear automorphism `ρ s` does as well, so
-- every eigenvalue of `ρ s` is a root of unity and hence integral over `ℤ`. The character value
-- `ρ.character s`, being the trace of `ρ s`, is the sum of those eigenvalues, so it is integral
-- over `ℤ`.

/-- Helper for Proposition 6-6.5-1: every root of the characteristic polynomial of `ρ s` is an
algebraic integer when `s` has finite order. -/
lemma isIntegral_of_charpoly_root_of_isOfFinOrder
    (ρ : Representation k G V) {s : G} (hs : IsOfFinOrder s) {μ : k}
    (hμ : μ ∈ (ρ s).charpoly.roots) :
    IsIntegral ℤ μ := by
  -- The finite-order hypothesis forces each characteristic root to be a root of unity.
  have hpow : μ ^ orderOf s = 1 := ρ.charpoly_root_pow_orderOf_eq_one s hμ
  -- A root of unity is integral over `ℤ`.
  exact IsIntegral.of_pow hs.orderOf_pos <| hpow ▸ isIntegral_one

variable [IsAlgClosed k]

/-- If `s` has finite order, then the character value `ρ.character s` is an algebraic integer. -/
theorem char_isIntegral_of_isOfFinOrder
    (ρ : Representation k G V) {s : G} (hs : IsOfFinOrder s) :
    IsIntegral ℤ (ρ.character s) := by
  -- Rewrite the character as a trace, then as the sum of the characteristic roots.
  rw [Representation.character, trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  -- Each root is integral, so their sum is integral as well.
  refine IsIntegral.multiset_sum fun μ hμ ↦ ?_
  exact isIntegral_of_charpoly_root_of_isOfFinOrder ρ hs hμ

end

section

variable {G : Type u} [Group G]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [Finite G]

/-- Proposition 6-6.5-1: for a finite group representation, the character value at any group
element is an algebraic integer. -/
theorem char_isIntegral (ρ : Representation ℂ G V) (s : G) :
    IsIntegral ℤ (ρ.character s) := by
  -- In a finite group every element has finite order, so the general lemma applies.
  simpa using char_isIntegral_of_isOfFinOrder ρ (isOfFinOrder_of_finite s)

end

end Representation

/-! ### Proposition_6_6_5_2 (from Chap06) -/
open scoped MonoidAlgebra

universe u v

section

variable {A : Type u} [CommRing A]
variable {M : Type v} [Monoid M] [Finite M]

namespace MonoidAlgebra

-- Source/core/bridge triage:
-- * source-facing: Proposition 6-6.5-2 below, specialized to the complex group algebra `ℂ[G]`.
-- * core/canonical owner: `MonoidAlgebra.isIntegral_of_coeff_isIntegral`, which necessarily lives
--   in the commutative coefficient-ring layer because the finite-generation step runs through
--   `Algebra.adjoin ℤ coeffs`.
-- * primitive data: the finite monoid algebra ambient `A[M]`, an element `x : A[M]`, and the
--   coefficientwise integrality hypothesis `hx`.
-- * bridge/view: the center-subtype transport
--   `MonoidAlgebra.isIntegral_center_of_coeff_isIntegral`.
-- * derived API: Proposition 6-6.5-2 as the complex center specialization, and the downstream
--   center-valued corollaries.
/-- In a finite monoid algebra, coefficientwise integrality over `ℤ` implies integrality of the
whole element over `ℤ`. -/
theorem isIntegral_of_coeff_isIntegral (x : A[M]) (hx : ∀ m : M, IsIntegral ℤ (x m)) :
    IsIntegral ℤ x := by
  classical
  let coeffs : Set A := Set.range x
  let S : Subring A := Subring.closure coeffs
  have hS : Module.Finite ℤ S := by
    have hcoeffs : Module.Finite ℤ (Algebra.adjoin ℤ coeffs) :=
      Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range x) fun a ha ↦ by
        rcases ha with ⟨m, rfl⟩
        exact hx m
    let _ : Module.Finite ℤ (Algebra.adjoin ℤ coeffs) := hcoeffs
    exact Module.Finite.equiv (Subring.closureEquivAdjoinInt coeffs).toLinearEquiv.symm
  haveI : Module.Finite ℤ S := hS
  let xS : S[M] := by
    refine ⟨x.support, fun m ↦ ⟨x m, Subring.subset_closure ⟨m, rfl⟩⟩, ?_⟩
    intro m
    simp
  letI : Module.Finite ℤ S[M] := MonoidAlgebra.moduleFinite
  have hxS : IsIntegral ℤ xS := IsIntegral.of_finite ℤ xS
  have hmap : mapRingHom M S.subtype xS = x := by
    ext m
    simp [xS, mapRingHom_apply]
  exact hmap ▸ map_isIntegral_int (mapRingHom M S.subtype) hxS

/-- The center-valued form of `isIntegral_of_coeff_isIntegral`: a central monoid-algebra element
whose coefficients are integral over `ℤ` is itself integral over `ℤ`. -/
theorem isIntegral_center_of_coeff_isIntegral
    (u : Subalgebra.center A (A[M])) (hu : ∀ m : M, IsIntegral ℤ ((u : A[M]) m)) :
    IsIntegral ℤ u := by
  refine
    (isIntegral_algHom_iff
      ((Subalgebra.center A (A[M])).val.restrictScalars ℤ)
      Subtype.val_injective).1 ?_
  exact isIntegral_of_coeff_isIntegral (u : A[M]) hu

end MonoidAlgebra

variable {G : Type v} [Group G] [Finite G]

/-- Proposition 6-6.5-2: a central element of the complex group algebra `ℂ[G]` whose
coefficients are algebraic integers is itself integral over `ℤ`. -/
theorem isIntegral_complexGroupRingCenter_of_coeff_isIntegral
    (u : Subalgebra.center ℂ (ℂ[G])) (hu : ∀ s : G, IsIntegral ℤ ((u : ℂ[G]) s)) :
    IsIntegral ℤ u :=
  MonoidAlgebra.isIntegral_center_of_coeff_isIntegral u hu

end
