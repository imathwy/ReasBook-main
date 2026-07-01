import Mathlib

open scoped Topology Pointwise

universe u v

variable (K : Type u) [Field K]

/- The formal power series ring `K[[X]]` carries its canonical `K`-vector-space
structure. -/
#check Module K (PowerSeries K)

/- The textbook space `\mathscr{C}^0(ℝ, ℝ)` is mathlib's type `C(ℝ, ℝ)` of continuous
real-valued functions. -/
#check C(ℝ, ℝ)

/- The continuous real-valued functions on `ℝ` carry their canonical `ℝ`-vector-space
structure. -/
#check Module ℝ C(ℝ, ℝ)

noncomputable abbrev realExpMap : C(ℝ, ℝ) := ⟨Real.exp, Real.continuous_exp⟩

noncomputable abbrev realCosMap : C(ℝ, ℝ) := ⟨Real.cos, Real.continuous_cos⟩

/-- Helper for Exercise 1.4.16: the `n`-th iterated derivative of
`x ↦ exp (a x)` at `0` is `a^n`. -/
lemma exp_scaled_iteratedDeriv_at_zero (a : ℝ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => Real.exp (a * x)) 0 = a ^ n := by
  -- The exponential is an eigenfunction of differentiation.
  rw [iteratedDeriv_exp_const_mul]
  simp

/-- Helper for Exercise 1.4.16: the plain exponential family
`x ↦ exp (a x)` is linearly independent over `ℝ`. -/
lemma real_exp_functions_linearIndependent :
    LinearIndependent ℝ (fun a : ℝ ↦ fun x : ℝ => Real.exp (a * x)) := by
  -- Reduce linear independence to vanishing of every finite linear relation.
  rw [linearIndependent_iff']
  intro s g hg a ha
  let e : s ≃ Fin s.card := s.equivFin
  let coeff : Fin s.card → ℝ := fun i ↦ g ((e.symm i : s) : ℝ)
  let params : Fin s.card → ℝ := fun i ↦ ((e.symm i : s) : ℝ)
  have hsum : (∑ i ∈ s, fun x : ℝ => g i * Real.exp (i * x)) = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using hg
  have hsmooth : ∀ i ∈ s, ContDiffAt ℝ ⊤ (fun x : ℝ => g i * Real.exp (i * x)) 0 := by
    intro i hi
    exact
      (contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))).contDiffAt
  have hderiv : ∀ n : Fin s.card, (∑ x ∈ s, g x * x ^ (n : ℕ)) = 0 := by
    intro n
    -- Evaluate the `n`-th derivative at `0` to obtain a Vandermonde relation.
    have hfun := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f 0) hsum
    change
      iteratedDeriv n (∑ i ∈ s, fun x : ℝ => g i * Real.exp (i * x)) 0 =
        iteratedDeriv n 0 0 at hfun
    rw [iteratedDeriv_sum (fun i hi ↦ (hsmooth i hi).of_le le_top)] at hfun
    simp [iteratedDeriv_const_mul_field, exp_scaled_iteratedDeriv_at_zero] at hfun
    simpa using hfun
  have hcoeff : ∀ n : Fin s.card, ∑ i : Fin s.card, coeff i * params i ^ (n : ℕ) = 0 := by
    intro n
    exact
      (Equiv.sum_comp e.symm
          (fun x : s ↦ g (x : ℝ) * (x : ℝ) ^ (n : ℕ)) ▸
        ((Finset.sum_attach (s := s) (f := fun x : ℝ ↦ g x * x ^ (n : ℕ))).trans (hderiv n)))
  have hzero : coeff = 0 := by
    -- The Vandermonde matrix for distinct parameters is nonsingular.
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    · exact Subtype.coe_injective.comp e.symm.injective
    · simpa [coeff, params] using hcoeff
  have := congrFun hzero (e ⟨a, ha⟩)
  simpa [coeff] using this

-- Proof sketch: show that a finite linear relation among exponentials yields a linear ODE
-- whose distinct exponent parameters force all coefficients to vanish.
/-- Exercise 1.4.16 (1): the exponential family `x ↦ e^(a x)` is linearly independent
over `ℝ`. -/
theorem realExpFamily_linearIndependent :
    LinearIndependent ℝ (fun a ↦
      realExpMap.comp (ContinuousMap.const ℝ a * ContinuousMap.id ℝ)) := by
  -- Reduce the continuous-map statement to the pointwise function statement.
  refine
    LinearIndependent.of_comp
      (ContinuousMap.coeFnLinearMap (R := ℝ) (α := ℝ) (M := ℝ)) ?_
  simpa [realExpMap, ContinuousMap.comp_apply, ContinuousMap.mul_apply]
    using real_exp_functions_linearIndependent

/-- Helper for Exercise 1.4.16: the even iterated derivative of
`x ↦ cos (a x)` at `0` is the expected signed power. -/
lemma cos_scaled_even_iteratedDeriv_at_zero (a : Set.Ioi (0 : ℝ)) (n : ℕ) :
    iteratedDeriv (2 * n) (fun x : ℝ => Real.cos ((a : ℝ) * x)) 0 =
      (a : ℝ) ^ (2 * n) * (-1) ^ n := by
  -- Repeated differentiation of cosine is periodic with period four.
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos]
  rw [Real.iteratedDeriv_even_cos]
  simp

/-- Helper for Exercise 1.4.16: the plain cosine family
`x ↦ cos (a x)` with positive frequencies is linearly independent over `ℝ`. -/
lemma real_cos_functions_linearIndependent :
    LinearIndependent ℝ (fun a : Set.Ioi (0 : ℝ) ↦ fun x : ℝ => Real.cos ((a : ℝ) * x)) := by
  -- Again reduce to finite relations and extract a Vandermonde system.
  rw [linearIndependent_iff']
  intro s g hg a ha
  let e : s ≃ Fin s.card := s.equivFin
  let coeff : Fin s.card → ℝ := fun i ↦ g ((e.symm i : s) : Set.Ioi (0 : ℝ))
  let paramsSq : Fin s.card → ℝ :=
    fun i ↦ (((e.symm i : s) : Set.Ioi (0 : ℝ)) : ℝ) ^ 2
  have hsum : (∑ i ∈ s, fun x : ℝ => g i * Real.cos ((i : ℝ) * x)) = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using hg
  have hsmooth :
      ∀ i ∈ s, ContDiffAt ℝ ⊤ (fun x : ℝ => g i * Real.cos ((i : ℝ) * x)) 0 := by
    intro i hi
    exact
      (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).contDiffAt
  have hderiv : ∀ n : Fin s.card, (∑ x ∈ s, g x * (((x : ℝ) ^ 2) ^ (n : ℕ))) = 0 := by
    intro n
    -- Even derivatives kill the cosine oscillation and leave powers of `a²`.
    have hfun := congrArg (fun f : ℝ → ℝ => iteratedDeriv (2 * n) f 0) hsum
    change
      iteratedDeriv (2 * n) (∑ i ∈ s, fun x : ℝ => g i * Real.cos ((i : ℝ) * x)) 0 =
        iteratedDeriv (2 * n) 0 0 at hfun
    rw [iteratedDeriv_sum (fun i hi ↦ (hsmooth i hi).of_le le_top)] at hfun
    have hsigned :
        (∑ x ∈ s, g x * ((((x : ℝ) ^ 2) ^ (n : ℕ)) * (-1) ^ (n : ℕ))) = 0 := by
      simpa [iteratedDeriv_const_mul_field, cos_scaled_even_iteratedDeriv_at_zero, pow_mul]
        using hfun
    have hmul :
        (-1 : ℝ) ^ (n : ℕ) * (∑ x ∈ s, g x * (((x : ℝ) ^ 2) ^ (n : ℕ))) = 0 := by
      simpa [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm] using hsigned
    have hnonzero : (-1 : ℝ) ^ (n : ℕ) ≠ 0 := by
      exact pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.mp hmul).resolve_left hnonzero
  have hcoeff :
      ∀ n : Fin s.card, ∑ i : Fin s.card, coeff i * paramsSq i ^ (n : ℕ) = 0 := by
    intro n
    have hattach :
        ∑ x ∈ s.attach, g (x : Set.Ioi (0 : ℝ)) * (((x : ℝ) ^ 2) ^ (n : ℕ)) =
          ∑ x ∈ s, g x * (((x : ℝ) ^ 2) ^ (n : ℕ)) :=
      Finset.sum_attach (s := s) (f := fun x : Set.Ioi (0 : ℝ) ↦ g x * (((x : ℝ) ^ 2) ^ (n : ℕ)))
    exact
      (Equiv.sum_comp e.symm
          (fun x : s ↦
            g (x : Set.Ioi (0 : ℝ)) * ((((x : Set.Ioi (0 : ℝ)) : ℝ) ^ 2) ^ (n : ℕ))) ▸
        (hattach.trans (hderiv n)))
  have hzero : coeff = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    · intro i j hij
      have hsquare :
          (((e.symm i : s) : Set.Ioi (0 : ℝ)) : ℝ) ^ 2 =
            (((e.symm j : s) : Set.Ioi (0 : ℝ)) : ℝ) ^ 2 := hij
      apply e.symm.injective
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hEq | hNeg
      · apply Subtype.ext
        exact Subtype.ext hEq
      · exfalso
        have hiPos :
            0 < ((((e.symm i : s) : Set.Ioi (0 : ℝ)) : ℝ)) :=
          ((e.symm i : s) : Set.Ioi (0 : ℝ)).2
        have hjPos :
            0 < ((((e.symm j : s) : Set.Ioi (0 : ℝ)) : ℝ)) :=
          ((e.symm j : s) : Set.Ioi (0 : ℝ)).2
        linarith
    · simpa [coeff, paramsSq] using hcoeff
  have := congrFun hzero (e ⟨a, ha⟩)
  simpa [coeff] using this

-- Proof sketch: use a trigonometric-analytic argument, for instance via complex
-- exponentials or repeated differentiation, to separate distinct positive frequencies.
/-- Exercise 1.4.16 (2): the cosine family `x ↦ cos (a x)` indexed by positive real
frequencies is linearly independent over `ℝ`. -/
theorem realCosFamily_linearIndependent :
    LinearIndependent ℝ (fun a : Set.Ioi (0 : ℝ) ↦
      realCosMap.comp (ContinuousMap.const ℝ (a : ℝ) * ContinuousMap.id ℝ)) := by
  -- Reduce the continuous-map statement to the pointwise cosine family.
  refine
    LinearIndependent.of_comp
      (ContinuousMap.coeFnLinearMap (R := ℝ) (α := ℝ) (M := ℝ)) ?_
  simpa [realCosMap, ContinuousMap.comp_apply, ContinuousMap.mul_apply]
    using real_cos_functions_linearIndependent

/-- Helper for Exercise 1.4.16: a finite set admits a positive radius smaller than every
nonzero distance from the chosen center. -/
lemma exists_pos_lt_dist_of_mem_finset (s : Finset ℝ) {a : ℝ} :
    ∃ δ > 0, ∀ b ∈ s.erase a, δ < |b - a| := by
  by_cases hs : (s.erase a).Nonempty
  · let d : ℝ := (s.erase a).inf' hs fun b ↦ |b - a|
    have hdpos : 0 < d := by
      refine (Finset.lt_inf'_iff hs).2 ?_
      intro c hc
      have hca : c ≠ a := (Finset.mem_erase.mp hc).1
      simpa [d] using abs_pos.mpr (sub_ne_zero.mpr hca)
    refine ⟨d / 2, by linarith, ?_⟩
    intro b hb
    have hle : d ≤ |b - a| := by
      simpa [d] using (Finset.inf'_le (fun b ↦ |b - a|) hb)
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro b hb
    exact (hs ⟨b, hb⟩).elim

/-- Helper for Exercise 1.4.16: the symmetric second difference of `x ↦ |x-a|`
at its own breakpoint is `2δ`. -/
lemma abs_second_difference_same (a δ : ℝ) (hδ : 0 ≤ δ) :
    |(a + δ) - a| + |(a - δ) - a| - 2 * |a - a| = 2 * δ := by
  -- At the breakpoint the two absolute values contribute exactly `δ` each.
  rw [show (a + δ) - a = δ by ring]
  rw [show (a - δ) - a = -δ by ring]
  rw [show a - a = 0 by ring]
  rw [abs_of_nonneg hδ, abs_of_nonpos (by linarith : -δ ≤ 0)]
  ring

/-- Helper for Exercise 1.4.16: if `δ` is smaller than the distance from `a` to `b`,
then the symmetric second difference of `x ↦ |x-b|` around `a` vanishes. -/
lemma abs_second_difference_of_lt_dist {a b δ : ℝ} (hδ : 0 ≤ δ) (hδlt : δ < |b - a|) :
    |(a + δ) - b| + |(a - δ) - b| - 2 * |a - b| = 0 := by
  have habne : a ≠ b := by
    intro hab
    subst hab
    have : δ < 0 := by simpa using hδlt
    linarith
  rcases lt_or_gt_of_ne habne with hab | hba
  · have habs : |b - a| = b - a := abs_of_nonneg (by linarith)
    have hsmall : δ < b - a := by simpa [habs] using hδlt
    have hplus : a + δ - b ≤ 0 := by linarith
    have hminus : a - δ - b ≤ 0 := by linarith
    have hab' : a - b ≤ 0 := by linarith
    rw [abs_of_nonpos hplus, abs_of_nonpos hminus, abs_of_nonpos hab']
    ring
  · have habs : |b - a| = a - b := by
      rw [abs_of_nonpos (by linarith : b - a ≤ 0)]
      ring
    have hsmall : δ < a - b := by simpa [habs] using hδlt
    have hplus : 0 ≤ a + δ - b := by linarith
    have hminus : 0 ≤ a - δ - b := by linarith
    have hab' : 0 ≤ a - b := by linarith
    rw [abs_of_nonneg hplus, abs_of_nonneg hminus, abs_of_nonneg hab']
    ring

/-- Helper for Exercise 1.4.16: the plain translated absolute-value family
`x ↦ |x-a|` is linearly independent over `ℝ`. -/
lemma real_translate_abs_functions_linearIndependent :
    LinearIndependent ℝ (fun a : ℝ ↦ fun x : ℝ => |x - a|) := by
  -- Use a localized second-difference functional to isolate each coefficient.
  rw [linearIndependent_iff']
  intro s g hg a ha
  have hsum : (∑ i ∈ s, fun x : ℝ => g i * |x - i|) = 0 := by
    simpa [Pi.smul_apply, smul_eq_mul] using hg
  rcases exists_pos_lt_dist_of_mem_finset s (a := a) with ⟨δ, hδpos, hδlt⟩
  have hplus : (∑ x ∈ s, g x * |(a + δ) - x|) = 0 := by
    simpa using congrFun hsum (a + δ)
  have hminus : (∑ x ∈ s, g x * |(a - δ) - x|) = 0 := by
    simpa using congrFun hsum (a - δ)
  have hzero : (∑ x ∈ s, g x * |a - x|) = 0 := by
    simpa using congrFun hsum a
  have hdiff : ∑ x ∈ s, g x * (|(a + δ) - x| + |(a - δ) - x| - 2 * |a - x|) = 0 := by
    -- Apply the second-difference functional to the whole relation.
    calc
      ∑ x ∈ s, g x * (|(a + δ) - x| + |(a - δ) - x| - 2 * |a - x|) =
          (∑ x ∈ s, g x * |(a + δ) - x|) +
            (∑ x ∈ s, g x * |(a - δ) - x|) -
              2 * (∑ x ∈ s, g x * |a - x|) := by
        calc
          ∑ x ∈ s, g x * (|(a + δ) - x| + |(a - δ) - x| - 2 * |a - x|) =
              ∑ x ∈ s,
                (g x * |(a + δ) - x| + g x * |(a - δ) - x| + -(g x * |a - x| * 2)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring
          _ =
              (∑ x ∈ s, g x * |(a + δ) - x|) +
                (∑ x ∈ s, g x * |(a - δ) - x|) +
                  ∑ x ∈ s, -(g x * |a - x| * 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ =
              (∑ x ∈ s, g x * |(a + δ) - x|) +
                (∑ x ∈ s, g x * |(a - δ) - x|) -
                  2 * (∑ x ∈ s, g x * |a - x|) := by
            have hmul : (∑ x ∈ s, g x * |a - x|) * 2 = ∑ x ∈ s, g x * |a - x| * 2 := by
              rw [Finset.sum_mul]
            rw [Finset.sum_neg_distrib, ← hmul]
            ring
      _ = 0 := by
        rw [hplus, hminus, hzero]
        ring
  have hsplit : g a * (2 * δ) = 0 := by
    -- All other terms vanish because `δ` is smaller than every other breakpoint distance.
    rw [Finset.sum_eq_single a] at hdiff
    · simpa [abs_second_difference_same a δ hδpos.le] using hdiff
    · intro b hb hba
      have hsmall : δ < |b - a| := hδlt b (Finset.mem_erase.mpr ⟨hba, hb⟩)
      rw [abs_second_difference_of_lt_dist hδpos.le hsmall, mul_zero]
    · simp [ha]
  have hnonzero : 2 * δ ≠ 0 := by positivity
  exact (mul_eq_zero.mp hsplit).resolve_right hnonzero

-- Proof sketch: evaluate a finite linear relation at the break points and compare
-- one-sided derivatives to isolate the coefficients attached to each translate.
/-- Exercise 1.4.16 (3): the translated absolute-value family `x ↦ |x - a|` is linearly
independent over `ℝ`. -/
theorem realTranslateAbsFamily_linearIndependent :
    LinearIndependent ℝ (fun a ↦
      |ContinuousMap.id ℝ - ContinuousMap.const ℝ a|) := by
  -- Reduce the continuous-map statement to the pointwise absolute-value family.
  refine
    LinearIndependent.of_comp
      (ContinuousMap.coeFnLinearMap (R := ℝ) (α := ℝ) (M := ℝ)) ?_
  simpa [ContinuousMap.sub_apply]
    using real_translate_abs_functions_linearIndependent

-- Proof sketch: take two distinct lines in `ℝ²`; their union misses closure under
-- addition, so it cannot be the carrier of any submodule.
/-- Exercise 1.4.16 (4): there exist two subspaces whose union is not a subspace. -/
theorem submodule_union_not_submodule_example :
    ∃ W₁ W₂ : Submodule ℝ (ℝ × ℝ),
      ¬ ∃ W : Submodule ℝ (ℝ × ℝ),
        (W : Set (ℝ × ℝ)) = (W₁ : Set (ℝ × ℝ)) ∪ (W₂ : Set (ℝ × ℝ)) := by
  let W₁ : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ)
  let W₂ : Submodule ℝ (ℝ × ℝ) := ℝ ∙ (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ)
  refine ⟨W₁, W₂, ?_⟩
  intro hUnion
  rcases hUnion with ⟨W, hW⟩
  -- The two basis vectors belong to the displayed union, hence to the candidate submodule.
  have h10 : (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ W := by
    have hmem :
        (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ (W₁ : Set (ℝ × ℝ)) ∪ (W₂ : Set (ℝ × ℝ)) :=
      Or.inl (Submodule.mem_span_singleton_self _)
    have : (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈ (W : Set (ℝ × ℝ)) := by
      rwa [hW]
    exact this
  have h01 : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ W := by
    have hmem :
        (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ (W₁ : Set (ℝ × ℝ)) ∪ (W₂ : Set (ℝ × ℝ)) :=
      Or.inr (Submodule.mem_span_singleton_self _)
    have : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ (W : Set (ℝ × ℝ)) := by
      rwa [hW]
    exact this
  -- Closure under addition then forces `(1,1)` into the same union.
  have h11 : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ W := by
    have hadd :
        (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) + (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) =
          (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) := by
      ext <;> norm_num
    simpa [hadd] using W.add_mem h10 h01
  have hUnion11 :
      (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈ (W₁ : Set (ℝ × ℝ)) ∪ (W₂ : Set (ℝ × ℝ)) :=
    hW ▸ h11
  rcases hUnion11 with hW₁ | hW₂
  · -- The first axis consists of vectors with vanishing second coordinate.
    rcases Submodule.mem_span_singleton.mp hW₁ with ⟨a, ha⟩
    have : (0 : ℝ) = 1 := by
      simpa using congrArg Prod.snd ha
    norm_num at this
  · -- The second axis consists of vectors with vanishing first coordinate.
    rcases Submodule.mem_span_singleton.mp hW₂ with ⟨a, ha⟩
    have : (0 : ℝ) = 1 := by
      simpa using congrArg Prod.fst ha
    norm_num at this

-- Proof sketch: if neither subspace contains the other, choose vectors outside the
-- opposite subspace; closure of the union under addition forces a contradiction.
/-- Exercise 1.4.16 (5): if the union of two submodules is a submodule, then one is
contained in the other; in particular this applies to subspaces. -/
theorem submodule_union_isSubmodule_implies_le_or_le
    {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]
    (W₁ W₂ : Submodule R M)
    (hUnion : ∃ W : Submodule R M, (W : Set M) = (W₁ : Set M) ∪ (W₂ : Set M)) :
    W₁ ≤ W₂ ∨ W₂ ≤ W₁ := by
  rcases hUnion with ⟨W, hW⟩
  have hW₁ : W₁ ≤ W := by
    intro x hx
    simpa [hW.symm] using (show x ∈ (W₁ : Set M) ∪ (W₂ : Set M) from Or.inl hx)
  have hW₂ : W₂ ≤ W := by
    intro x hx
    simpa [hW.symm] using (show x ∈ (W₁ : Set M) ∪ (W₂ : Set M) from Or.inr hx)
  have hsubset : (W : Set M) ⊆ (W₁ : Set M) ∪ (W₂ : Set M) := by
    simp [hW]
  rcases (AddSubgroupClass.subset_union).1 hsubset with hWW₁ | hWW₂
  · exact Or.inr (hW₂.trans hWW₁)
  · exact Or.inl (hW₁.trans hWW₂)

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

-- Proof sketch: argue by counting one-dimensional directions in finite unions of
-- proper subspaces; if the field were infinite or too small, the union could not cover
-- all of `V`.
/-- Exercise 1.4.16 (6): a finite cover of a vector space by proper subspaces forces
the field to be finite. -/
theorem finite_submodule_cover_implies_finite_field
    (W : Finset (Submodule K V))
    (hproper : ∀ U ∈ W, U ≠ ⊤)
    (hcover : (Set.univ : Set V) = ⋃ U ∈ W, (U : Set V)) :
    Finite K := by
  by_contra hK
  haveI : Infinite K := not_finite_iff_infinite.mp hK
  have hUnion' :
      (⋃ U : { U // U ∈ W }, ((U : Submodule K V) : Set V)) ⊂ (Set.univ : Set V) := by
    simpa using
      (Submodule.iUnion_ssubset_of_forall_ne_top_of_card_lt
        W.attach ((↑) : { U // U ∈ W } → Submodule K V)
        (fun U ↦ hproper U U.2) (by simp))
  have hUnion :
      (⋃ U ∈ W, (U : Set V)) ⊂ (Set.univ : Set V) := by
    simpa only [Set.iUnion_subtype] using hUnion'
  exact hUnion.ne <| by simpa using hcover.symm

/-- Helper for Exercise 1.4.16: every proper submodule over a finite field contributes at most
`1 / |K|` to the coset-cover index sum. -/
lemma inv_index_le_inv_card_of_proper_submodule
    [Finite K] {U : Submodule K V} (hU : U ≠ ⊤) :
    (((U.toAddSubgroup.index : ℚ)⁻¹) ≤ ((Nat.card K : ℚ)⁻¹)) := by
  by_cases hfi : U.toAddSubgroup.FiniteIndex
  · letI : U.toAddSubgroup.FiniteIndex := hfi
    letI : Finite (V ⧸ U) := AddSubgroup.finite_quotient_of_finiteIndex (H := U.toAddSubgroup)
    letI : Fintype K := Fintype.ofFinite K
    letI : Fintype (V ⧸ U) := Fintype.ofFinite (V ⧸ U)
    let b := Module.Free.chooseBasis K (V ⧸ U)
    letI : FiniteDimensional K (V ⧸ U) := b.finiteDimensional_of_finite
    haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.mpr hU
    -- A proper finite-index quotient is a nontrivial finite-dimensional vector space.
    have hpos : 0 < Module.finrank K (V ⧸ U) := Module.finrank_pos (R := K) (M := V ⧸ U)
    have hKpos : 0 < Fintype.card K := by
      simpa [Nat.card_eq_fintype_card] using (Nat.card_pos (α := K))
    have hcard_le_index : Nat.card K ≤ U.toAddSubgroup.index := by
      -- The quotient has cardinality `|K|^n` with `n > 0`, so it contains at least `|K|` points.
      have hpow : Fintype.card K ≤ Fintype.card (V ⧸ U) := by
        rw [Module.card_eq_pow_finrank (K := K) (V := V ⧸ U)]
        rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨n, hn⟩
        rw [hn, pow_succ]
        exact Nat.le_mul_of_pos_left _ (Nat.pow_pos hKpos)
      calc
        Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
        _ ≤ Fintype.card (V ⧸ U) := hpow
        _ = Nat.card (V ⧸ U) := (Nat.card_eq_fintype_card).symm
        _ = U.toAddSubgroup.index := (AddSubgroup.index_eq_card _).symm
    have hindex_pos : 0 < (U.toAddSubgroup.index : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hfi.index_ne_zero
    have hcard_pos : 0 < (Nat.card K : ℚ) := by
      exact_mod_cast Nat.card_pos
    exact (inv_le_inv₀ hindex_pos hcard_pos).2 <| by
      exact_mod_cast hcard_le_index
  · -- Infinite-index submodules contribute `0`, so the bound is immediate.
    have hindex_zero : U.toAddSubgroup.index = 0 := (AddSubgroup.not_finiteIndex_iff).1 hfi
    have hcard_nonneg : (0 : ℚ) ≤ (Nat.card K : ℚ)⁻¹ := by
      positivity
    simp [hindex_zero, hcard_nonneg]

/-- Helper for Exercise 1.4.16: in the extremal case `W.card = |K|`, at least two members of the
cover have finite additive index. -/
lemma exists_two_finiteIndex_members_of_extremal_cover
    [Finite K]
    (W : Finset (Submodule K V))
    (hproper : ∀ U ∈ W, U ≠ ⊤)
    (hcover : (Set.univ : Set V) = ⋃ U ∈ W, (U : Set V))
    (hcard : W.card = Nat.card K) :
    ∃ U ∈ W, U.toAddSubgroup.FiniteIndex ∧
      ∃ U' ∈ W, U'.toAddSubgroup.FiniteIndex ∧ U ≠ U' := by
  classical
  letI : DecidablePred (fun U : Submodule K V => U.toAddSubgroup.FiniteIndex) :=
    Classical.decPred _
  have hcovers_add :
      ⋃ U ∈ W, (0 : V) +ᵥ ((U.toAddSubgroup : AddSubgroup V) : Set V) = Set.univ := by
    simp [hcover, zero_vadd]
  have haux := AddSubgroup.leftCoset_cover_filter_FiniteIndex_aux
    (H := fun U : Submodule K V => U.toAddSubgroup)
    (g := fun _ : Submodule K V => (0 : V))
    (s := W) hcovers_add
  have hsum_ge : (1 : ℚ) ≤ ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) := haux.2.1
  have hsum_le' :
      ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) ≤
        ∑ U ∈ W, ((Nat.card K : ℚ)⁻¹) := by
    refine Finset.sum_le_sum ?_
    intro U hU
    exact inv_index_le_inv_card_of_proper_submodule (hproper U hU)
  have hsum_eq : ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) = 1 := by
    -- The global lower bound and the uniform upper bound force exact equality.
    refine le_antisymm ?_ hsum_ge
    calc
      ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) ≤
          ∑ U ∈ W, ((Nat.card K : ℚ)⁻¹) := hsum_le'
      _ = W.card * ((Nat.card K : ℚ)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Nat.card K : ℚ) * ((Nat.card K : ℚ)⁻¹) := by rw [hcard]
      _ = 1 := by
        field_simp [Nat.card_pos.ne']
  let Wfi := W.filter (fun U => U.toAddSubgroup.FiniteIndex)
  have hsum_filter :
      ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) =
        ∑ U ∈ Wfi, ((U.toAddSubgroup.index : ℚ)⁻¹) := by
    -- Infinite-index members contribute `0`, so only the filtered family matters.
    calc
      ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) =
          ∑ U ∈ W, if U.toAddSubgroup.FiniteIndex then ((U.toAddSubgroup.index : ℚ)⁻¹) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro U hU
        by_cases hfi : U.toAddSubgroup.FiniteIndex
        · simp [hfi]
        · have hindex_zero : U.toAddSubgroup.index = 0 := (AddSubgroup.not_finiteIndex_iff).1 hfi
          simp [hfi, hindex_zero]
      _ = ∑ U ∈ Wfi, ((U.toAddSubgroup.index : ℚ)⁻¹) := by
        rw [show Wfi = W.filter (fun U => U.toAddSubgroup.FiniteIndex) by rfl]
        rw [(Finset.sum_filter _ _).symm]
  have hq_one_lt : 1 < Nat.card K := by
    letI : Fintype K := Fintype.ofFinite K
    simpa [Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  have hWfi_card : 1 < Wfi.card := by
    by_contra hnot
    have hWfi_le : Wfi.card ≤ 1 := Nat.not_lt.mp hnot
    have hsum_lt_one : ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) < 1 := by
      -- A filtered family with at most one member contributes strictly less than `1`.
      calc
        ∑ U ∈ W, ((U.toAddSubgroup.index : ℚ)⁻¹) =
            ∑ U ∈ Wfi, ((U.toAddSubgroup.index : ℚ)⁻¹) := hsum_filter
        _ ≤ ∑ U ∈ Wfi, ((Nat.card K : ℚ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro U hU
          have hUin : U ∈ W := (Finset.mem_filter.mp hU).1
          exact inv_index_le_inv_card_of_proper_submodule (hproper U hUin)
        _ = Wfi.card * ((Nat.card K : ℚ)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * ((Nat.card K : ℚ)⁻¹) := by
          gcongr
          exact_mod_cast hWfi_le
        _ = ((Nat.card K : ℚ)⁻¹) := by ring
        _ < 1 := by
          exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq_one_lt)
    exact (lt_irrefl (1 : ℚ)) <| hsum_eq.symm ▸ hsum_lt_one
  rcases Finset.one_lt_card.mp hWfi_card with ⟨U, hUfi, U', hU'fi, hUU'⟩
  exact ⟨U, (Finset.mem_filter.mp hUfi).1, (Finset.mem_filter.mp hUfi).2,
    U', (Finset.mem_filter.mp hU'fi).1, (Finset.mem_filter.mp hU'fi).2, hUU'⟩

-- Proof sketch: after establishing that the field must be finite, apply the finite-field
-- counting argument for unions of proper subspaces to obtain the lower bound.
/-- Exercise 1.4.16 (7): under the same cover hypotheses over a finite field, the covering
family has cardinality at least `|K| + 1`. -/
theorem finite_submodule_cover_card_bound_of_finite_field
    [Finite K]
    (W : Finset (Submodule K V))
    (hproper : ∀ U ∈ W, U ≠ ⊤)
    (hcover : (Set.univ : Set V) = ⋃ U ∈ W, (U : Set V)) :
    Nat.card K + 1 ≤ W.card := by
  classical
  letI : DecidablePred (fun U : Submodule K V => U.toAddSubgroup.FiniteIndex) :=
    Classical.decPred _
  have hcovers_add :
      ⋃ U ∈ W, (0 : V) +ᵥ ((U.toAddSubgroup : AddSubgroup V) : Set V) = Set.univ := by
    simp [hcover, zero_vadd]
  have hfield_le_card : Nat.card K ≤ W.card := by
    -- First get the coarse lower bound `|K| ≤ W.card` from the Neumann index theorem.
    obtain ⟨U, hUW, hfi, hindex_le⟩ :=
      AddSubgroup.exists_index_le_card_of_leftCoset_cover
        (H := fun U : Submodule K V => U.toAddSubgroup)
        (g := fun _ : Submodule K V => (0 : V))
        (s := W) hcovers_add
    have hbound := inv_index_le_inv_card_of_proper_submodule (hproper U hUW)
    have hindex_pos : 0 < (U.toAddSubgroup.index : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hfi.index_ne_zero
    have hcard_pos : 0 < (Nat.card K : ℚ) := by
      exact_mod_cast Nat.card_pos
    have hcard_le_index : (Nat.card K : ℚ) ≤ U.toAddSubgroup.index :=
      (inv_le_inv₀ hindex_pos hcard_pos).1 hbound
    exact le_trans (by exact_mod_cast hcard_le_index) hindex_le
  by_contra hbad
  have hcard_eq : W.card = Nat.card K := by
    exact le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hbad)) hfield_le_card
  obtain ⟨U1, hU1W, hU1fi, U2, hU2W, hU2fi, hU12⟩ :=
    exists_two_finiteIndex_members_of_extremal_cover W hproper hcover hcard_eq
  have haux := AddSubgroup.leftCoset_cover_filter_FiniteIndex_aux
    (H := fun T : Submodule K V => T.toAddSubgroup)
    (g := fun _ : Submodule K V => (0 : V))
    (s := W) hcovers_add
  have hsum_ge : (1 : ℚ) ≤ ∑ T ∈ W, ((T.toAddSubgroup.index : ℚ)⁻¹) := haux.2.1
  have hsum_le' :
      ∑ T ∈ W, ((T.toAddSubgroup.index : ℚ)⁻¹) ≤
        ∑ T ∈ W, ((Nat.card K : ℚ)⁻¹) := by
    refine Finset.sum_le_sum ?_
    intro T hT
    exact inv_index_le_inv_card_of_proper_submodule (hproper T hT)
  have hsum_eq : ∑ T ∈ W, ((T.toAddSubgroup.index : ℚ)⁻¹) = 1 := by
    -- Route correction: the equality case is forced by the same index-sum bounds as above.
    refine le_antisymm ?_ hsum_ge
    calc
      ∑ T ∈ W, ((T.toAddSubgroup.index : ℚ)⁻¹) ≤
          ∑ T ∈ W, ((Nat.card K : ℚ)⁻¹) := hsum_le'
      _ = W.card * ((Nat.card K : ℚ)⁻¹) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (Nat.card K : ℚ) * ((Nat.card K : ℚ)⁻¹) := by rw [hcard_eq]
      _ = 1 := by
        field_simp [Nat.card_pos.ne']
  have hpair :
      ((↑(W.filter (fun T => T.toAddSubgroup.FiniteIndex)) : Set (Submodule K V)).PairwiseDisjoint
        fun T ↦ (T : Set V)) := by
    -- The equality case forces pairwise disjointness among the finite-index members.
    simpa [zero_vadd] using haux.2.2 hsum_eq
  have hU1fi_mem : U1 ∈ W.filter (fun T => T.toAddSubgroup.FiniteIndex) :=
    Finset.mem_filter.mpr ⟨hU1W, hU1fi⟩
  have hU2fi_mem : U2 ∈ W.filter (fun T => T.toAddSubgroup.FiniteIndex) :=
    Finset.mem_filter.mpr ⟨hU2W, hU2fi⟩
  have hdisj := hpair hU1fi_mem hU2fi_mem hU12
  -- But every submodule contains `0`, so two distinct filtered members cannot be disjoint.
  exact (Set.disjoint_left.mp hdisj) U1.zero_mem U2.zero_mem

-- Proof sketch: compute the cardinality of `ZMod 2` directly.
/-- Exercise 1.4.16 (8): for the sharp example, the field-size term satisfies
`|ZMod 2| + 1 = 3`. -/
theorem finite_submodule_cover_card_bound_sharp_card :
    Nat.card (ZMod 2) + 1 = 3 := by
  -- Compute the field-size term directly from the two-element field.
  rw [Nat.card_eq_fintype_card]
  decide

/-- The sharp finite-subspace-cover example in `(ZMod 2)^2`: the two coordinate axes together
with the diagonal line. -/
noncomputable def sharpCoverFamily : Finset (Submodule (ZMod 2) (Fin 2 → ZMod 2)) :=
  {(ZMod 2) ∙ ![1, 0], (ZMod 2) ∙ ![0, 1], (ZMod 2) ∙ ![1, 1]}

/-- Helper for Exercise 1.4.16: the horizontal axis, vertical axis, and diagonal line in
`(ZMod 2)^2` are pairwise distinct. -/
lemma sharpCoverFamily_three_lines_distinct :
    ((ZMod 2) ∙ ![1, 0] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![0, 1] ∧
    ((ZMod 2) ∙ ![1, 0] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![1, 1] ∧
    ((ZMod 2) ∙ ![0, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![1, 1] := by
  have h12 :
      ((ZMod 2) ∙ ![1, 0] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![0, 1] := by
    -- A vector on the vertical axis has zero first coordinate.
    intro hEq
    have hmem :
        (![1, 0] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![0, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      rw [← hEq]
      exact Submodule.mem_span_singleton_self _
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have : (1 : ZMod 2) = 0 := by
      simpa using congrFun ha 0
    exact one_ne_zero this
  have h1d :
      ((ZMod 2) ∙ ![1, 0] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![1, 1] := by
    -- A diagonal vector with second coordinate zero must be zero.
    intro hEq
    have hmem :
        (![1, 0] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![1, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      rw [← hEq]
      exact Submodule.mem_span_singleton_self _
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have ha0 : (a : ZMod 2) = 0 := by
      simpa using congrFun ha 1
    have : (1 : ZMod 2) = 0 := by
      simpa [ha0] using congrFun ha 0
    exact one_ne_zero this
  have h2d :
      ((ZMod 2) ∙ ![0, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) ≠ (ZMod 2) ∙ ![1, 1] := by
    -- The same coordinate argument separates the vertical axis from the diagonal.
    intro hEq
    have hmem :
        (![0, 1] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![1, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      rw [← hEq]
      exact Submodule.mem_span_singleton_self _
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have ha0 : (a : ZMod 2) = 0 := by
      simpa using congrFun ha 0
    have : (1 : ZMod 2) = 0 := by
      simpa [ha0] using congrFun ha 1
    exact one_ne_zero this
  exact ⟨h12, h1d, h2d⟩

/-- The sharp covering family of the two coordinate axes and the diagonal line has exactly three
members. -/
theorem finite_submodule_cover_card_bound_sharp_cover_card :
    sharpCoverFamily.card = 3 := by
  have hdist := sharpCoverFamily_three_lines_distinct
  -- The family is exactly the finset with those three pairwise distinct lines.
  simp [sharpCoverFamily, hdist.1, hdist.2.1, hdist.2.2]

-- Proof sketch: each listed line is one-dimensional, hence not equal to the whole
-- two-dimensional ambient space.
/-- Exercise 1.4.16 (9): in the sharp example, each subspace in the covering family is strict. -/
theorem finite_submodule_cover_card_bound_sharp_proper :
    ∀ U ∈ sharpCoverFamily, U ≠ ⊤ := by
  intro U hU
  -- Reduce membership in the three-element family to the three concrete lines.
  simp [sharpCoverFamily] at hU
  rcases hU with rfl | rfl | rfl
  · -- The horizontal axis misses the second basis vector.
    intro htop
    have hmem :
        (![0, 1] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![1, 0] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      simp [htop]
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have : (1 : ZMod 2) = 0 := by
      simpa using congrFun ha 1
    exact one_ne_zero this
  · -- The vertical axis misses the first basis vector.
    intro htop
    have hmem :
        (![1, 0] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![0, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      simp [htop]
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have : (1 : ZMod 2) = 0 := by
      simpa using congrFun ha 0
    exact one_ne_zero this
  · -- The diagonal misses the vector `(1,0)`.
    intro htop
    have hmem :
        (![1, 0] : Fin 2 → ZMod 2) ∈
          ((ZMod 2) ∙ ![1, 1] : Submodule (ZMod 2) (Fin 2 → ZMod 2)) := by
      simp [htop]
    rcases Submodule.mem_span_singleton.mp hmem with ⟨a, ha⟩
    have ha0 : (a : ZMod 2) = 0 := by
      simpa using congrFun ha 1
    have : (1 : ZMod 2) = 0 := by
      simpa [ha0] using congrFun ha 0
    exact one_ne_zero this

-- Proof sketch: every vector in `(ZMod 2)^2` lies either on a coordinate axis or on the diagonal,
-- so the three listed lines cover the whole space.
/-- Exercise 1.4.16 (10): in the sharp example, the three strict subspaces cover the whole ambient
vector space. -/
theorem finite_submodule_cover_card_bound_sharp_cover :
    (Set.univ : Set (Fin 2 → ZMod 2)) = ⋃ U ∈ sharpCoverFamily, (U : Set (Fin 2 → ZMod 2)) :=
  by
  ext v
  constructor
  · intro hv
    -- There are only four vectors in `(ZMod 2)^2`, determined by their two coordinates.
    simp [sharpCoverFamily, Submodule.mem_span_singleton]
    have hv0 : v 0 = 0 ∨ v 0 = 1 := by
      revert v
      decide
    have hv1 : v 1 = 0 ∨ v 1 = 1 := by
      revert v
      decide
    rcases hv0 with hv0 | hv0 <;> rcases hv1 with hv1 | hv1
    · left
      refine ⟨0, ?_⟩
      ext i
      fin_cases i
      · simp [hv0]
      · simp [hv1]
    · right
      left
      refine ⟨1, ?_⟩
      ext i
      fin_cases i
      · simp [hv0]
      · simp [hv1]
    · left
      refine ⟨1, ?_⟩
      ext i
      fin_cases i
      · simp [hv0]
      · simp [hv1]
    · right
      right
      refine ⟨1, ?_⟩
      ext i
      fin_cases i
      · simp [hv0]
      · simp [hv1]
  · intro hv
    simp
