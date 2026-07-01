import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
