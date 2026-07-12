import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

open KaehlerDifferential

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Algebra ℚ S]
variable (f : S)

/-- Helper for Lemma 10.140.6: the derivation corresponding to an `S`-linear functional on
`Ω[S⁄R]` evaluates on `x` by applying the functional to `dx`. -/
private theorem linearMapEquivDerivation_apply_D
    (θ : Ω[S⁄R] →ₗ[S] S) (x : S) :
    ((KaehlerDifferential.linearMapEquivDerivation R S) θ) x = θ (D R S x) := by
  -- This is the universal-property bridge from linear maps on `Ω[S⁄R]` to derivations.
  simpa using
    (Derivation.liftKaehlerDifferential_comp_D
      (((KaehlerDifferential.linearMapEquivDerivation R S) θ)) x)

/-- Helper for Lemma 10.140.6: membership in a power of the principal ideal `(f)` is equivalent to
being a right multiple of `f ^ n`. -/
private theorem mem_span_singleton_pow_iff_exists_mul
    (a f : S) (n : ℕ) :
    a ∈ (Ideal.span ({f} : Set S)) ^ n ↔ ∃ b : S, a = f ^ n * b := by
  -- Rewrite principal-ideal powers and then unpack principal-ideal membership as divisibility.
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa [mul_comm] using hb⟩
  · rintro ⟨b, rfl⟩
    exact ⟨b, by simp [mul_comm]⟩

/-- Helper for Lemma 10.140.6: over a `ℚ`-algebra, a nonzero natural-number scalar cannot kill an
element. -/
private theorem eq_zero_of_nat_smul_eq_zero
    [Nontrivial S] (n : ℕ) (a : S) (hn : n ≠ 0) (h : n • a = 0) :
    a = 0 := by
  -- Convert the `ℕ`-smul relation to a `ℚ`-smul relation and cancel the nonzero scalar.
  rw [← Nat.cast_smul_eq_nsmul ℚ] at h
  have hnq : ((n : ℚ) : ℚ) ≠ 0 := by
    exact_mod_cast hn
  rcases smul_eq_zero.mp h with hzero | ha
  · exact (hnq hzero).elim
  · exact ha

/-- Helper for Lemma 10.140.6: a derivation with `δ(f) = 1` rules out nilpotence of `f`. -/
private theorem not_isNilpotent_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1) :
    ¬ IsNilpotent f := by
  intro hf
  -- Apply the derivation to the minimal nilpotence relation and cancel the nonzero scalar.
  have hpow : f ^ nilpotencyClass f = 0 := pow_nilpotencyClass hf
  have hderiv : nilpotencyClass f • f ^ (nilpotencyClass f - 1) = 0 := by
    simpa [hδf] using congrArg δ hpow
  have hzero : f ^ (nilpotencyClass f - 1) = 0 := by
    exact eq_zero_of_nat_smul_eq_zero
      (nilpotencyClass f) (f ^ (nilpotencyClass f - 1))
      (Nat.ne_of_gt <| (pos_nilpotencyClass_iff.mpr hf)) hderiv
  exact pow_pred_nilpotencyClass hf hzero

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` lies in every power of the
principal ideal `(f)`. -/
private theorem factorization_step_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a b : S) (n : ℕ) (hfa : f * a = 0) (hab : a = f ^ n * b) :
    ∃ c : S, a = f ^ (n + 1) * c := by
  -- Route correction: switch from ideal-membership induction to the source-faithful
  -- factorization induction `a = f^n * b`, so differentiation only sees a single product.
  have hpowMulZero : f ^ (n + 1) * b = 0 := by
    -- Rewrite the annihilator relation using the current factorization of `a`.
    calc
      f ^ (n + 1) * b = f * a := by
        rw [pow_succ', hab, mul_assoc]
      _ = 0 := hfa
  have hpowDeriv : δ (f ^ (n + 1)) = (n + 1) • f ^ n := by
    -- Differentiate the power and simplify using `δ(f) = 1`.
    calc
      δ (f ^ (n + 1)) = (n + 1) • f ^ ((n + 1) - 1) • δ f := by
        rw [Derivation.leibniz_pow]
      _ = (n + 1) • f ^ n • (1 : S) := by simp [hδf]
      _ = (n + 1) • f ^ n := by simp
  have hderivZero : δ (f ^ (n + 1) * b) = 0 := by
    -- Apply the derivation to the zero relation `f^(n+1) * b = 0`.
    simpa using congrArg δ hpowMulZero
  have hscaled : (n + 1 : S) * a + f ^ (n + 1) * δ b = 0 := by
    -- After Leibniz, rewrite the differentiated power term back in terms of `a`.
    rw [Derivation.leibniz, hpowDeriv] at hderivZero
    simpa [smul_eq_mul, nsmul_eq_mul, hab, pow_succ', mul_assoc, mul_left_comm, mul_comm,
      add_comm]
      using hderivZero
  have hscaledRat : ((n + 1 : ℚ) : ℚ) • a + f ^ (n + 1) * δ b = 0 := by
    -- Rewrite the cast multiple as scalar multiplication by the corresponding rational.
    simpa [Algebra.smul_def] using hscaled
  have hq_ne_zero : ((n + 1 : ℚ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hrescaled :
      a + ((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b) = 0 := by
    -- Multiply the relation by `(n + 1)⁻¹` in the `ℚ`-module `S`.
    have htmp :=
      congrArg (fun x : S => ((n + 1 : ℚ) : ℚ)⁻¹ • x) hscaledRat
    simpa [smul_add, smul_smul, hq_ne_zero] using htmp
  have hsmul_mul :
      ((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b) =
        f ^ (n + 1) * (((n + 1 : ℚ) : ℚ)⁻¹ • δ b) := by
    -- Move the rational scalar from the whole product to the second factor.
    rw [Algebra.smul_def, Algebra.smul_def]
    calc
      algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * (f ^ (n + 1) * δ b)
          = (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * f ^ (n + 1)) * δ b := by
            rw [mul_assoc]
      _ = (f ^ (n + 1) * algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹)) * δ b := by
            rw [mul_comm (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹)) (f ^ (n + 1))]
      _ = f ^ (n + 1) * (algebraMap ℚ S (((n + 1 : ℚ) : ℚ)⁻¹) * δ b) := by
            rw [← mul_assoc]
  refine ⟨-(((n + 1 : ℚ) : ℚ)⁻¹ • δ b), ?_⟩
  -- Repackage the rescaled relation as one extra factor of `f`.
  calc
    a = -(((n + 1 : ℚ) : ℚ)⁻¹ • (f ^ (n + 1) * δ b)) := by
      exact eq_neg_iff_add_eq_zero.mpr hrescaled
    _ = -(f ^ (n + 1) * (((n + 1 : ℚ) : ℚ)⁻¹ • δ b)) := by
      rw [hsmul_mul]
    _ = f ^ (n + 1) * (-(((n + 1 : ℚ) : ℚ)⁻¹ • δ b)) := by
      rw [neg_mul_eq_mul_neg]

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` factors as `f ^ n` times
some element for every `n`. -/
private theorem exists_factor_of_mul_eq_zero_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a : S) (hfa : f * a = 0) (n : ℕ) :
    ∃ b : S, a = f ^ n * b := by
  induction n with
  | zero =>
      -- The base case is the trivial factorization `a = f^0 * a`.
      refine ⟨a, ?_⟩
      simp
  | succ n ih =>
      -- The induction step differentiates the zero relation for the current factorization.
      rcases ih with ⟨b, hb⟩
      exact factorization_step_of_derivation_eq_one
        (R := R) (S := S) (f := f) δ hδf a b n hfa hb

/-- Helper for Lemma 10.140.6: if `δ(f) = 1` and `f * a = 0`, then `a` lies in every power of the
principal ideal `(f)`. -/
private theorem mem_span_singleton_pow_of_mul_eq_zero_of_derivation_eq_one
    [Nontrivial S] (δ : Derivation R S S) (hδf : δ f = 1)
    (a : S) (hfa : f * a = 0) (n : ℕ) :
    a ∈ (Ideal.span ({f} : Set S)) ^ n := by
  -- Convert the source-faithful factorization induction back into principal-ideal membership.
  rcases exists_factor_of_mul_eq_zero_of_derivation_eq_one
      (R := R) (S := S) (f := f) δ hδf a hfa n with ⟨b, hb⟩
  exact (mem_span_singleton_pow_iff_exists_mul (a := a) (f := f) n).2 ⟨b, hb⟩

/-- Helper for Lemma 10.140.6: in a Noetherian local `ℚ`-algebra, a derivation with `δ(f) = 1`
forces `f` to be regular. -/
private theorem isRegular_of_derivation_eq_one
    [Nontrivial S] [IsLocalRing S] [IsNoetherianRing S]
    (δ : Derivation R S S) (hδf : δ f = 1) :
    IsRegular f := by
  classical
  by_cases hunit : IsUnit f
  · -- A unit is automatically regular.
    exact hunit.isRegular
  · -- Otherwise the principal ideal `(f)` is proper, so Krull intersection kills every
    -- annihilator of `f`.
    rw [isRegular_iff_mem_nonZeroDivisors, mem_nonZeroDivisors_iff_left]
    intro a hfa
    let I : Ideal S := Ideal.span ({f} : Set S)
    have hmem : ∀ n : ℕ, a ∈ I ^ n := by
      intro n
      simpa [I] using
        mem_span_singleton_pow_of_mul_eq_zero_of_derivation_eq_one
          (R := R) (S := S) (f := f) δ hδf a hfa n
    have haInf : a ∈ ⨅ n : ℕ, I ^ n := by
      exact Ideal.mem_iInf.mpr hmem
    have hIneTop : I ≠ ⊤ := by
      intro hI
      apply hunit
      exact Ideal.span_singleton_eq_top.mp hI
    have hbot : a ∈ (⊥ : Ideal S) := by
      rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing I hIneTop]
      exact haInf
    simpa using hbot

-- Proof sketch: the hypothesis gives an `S`-linear functional `θ : Ω[S⁄R] →ₗ[S] S` with
-- `θ (df) = 1`. Via the owner equivalence `KaehlerDifferential.linearMapEquivDerivation`, this
-- yields an `R`-derivation `δ : S → S` with `δ f = 1`. If `f` were nilpotent, applying `δ` to a
-- minimal relation `f^n = 0` would give `n • f^(n - 1) = 0`; since `S` is a `ℚ`-algebra, `n` is
-- invertible, contradicting minimality.
/-- Lemma 10.140.6: if there exists an `S`-linear map `Ω[S⁄R] →ₗ[S] S` sending `df` to `1`
(equivalently, `df` generates a free rank-one direct summand of `Ω[S⁄R]`), then `f` is not
nilpotent. -/
@[stacks 00TW]
theorem not_isNilpotent_of_kaehlerDifferential_directSummand
    [Nontrivial S]
    (hdf : ∃ θ : Ω[S⁄R] →ₗ[S] S, θ (D R S f) = 1) :
    ¬ IsNilpotent f := by
  rcases hdf with ⟨θ, hθ⟩
  -- Pass from the linear functional on `Ω[S⁄R]` to the corresponding derivation.
  let δ : Derivation R S S := (KaehlerDifferential.linearMapEquivDerivation R S) θ
  have hδf : δ f = 1 := by
    have hδ : δ f = θ (D R S f) := by
      simpa [δ] using linearMapEquivDerivation_apply_D (R := R) (S := S) θ f
    exact hδ.trans hθ
  -- The abstract nilpotence obstruction finishes the source proof route.
  exact not_isNilpotent_of_derivation_eq_one (R := R) (S := S) (f := f) δ hδf

-- Proof sketch: with the same derivation `δ` satisfying `δ f = 1`, any relation `f * a = 0`
-- yields `a = -f * δ a`, so `a ∈ (f)`. Iterating this argument shows `a ∈ (f^n)` for every `n`.
-- In a Noetherian local ring, Krull's intersection theorem gives `⋂ n, (f^n) = 0`, hence `a = 0`
-- and multiplication by `f` is injective.
/-- Under the same hypothesis that `df` admits an `S`-linear functional with value `1`, if `S` is
Noetherian local, then `f` is a nonzerodivisor. -/
theorem isRegular_of_kaehlerDifferential_directSummand
    [Nontrivial S] [IsLocalRing S] [IsNoetherianRing S]
    (hdf : ∃ θ : Ω[S⁄R] →ₗ[S] S, θ (D R S f) = 1) :
    IsRegular f := by
  rcases hdf with ⟨θ, hθ⟩
  -- Pass to the derivation appearing in the source proof.
  let δ : Derivation R S S := (KaehlerDifferential.linearMapEquivDerivation R S) θ
  have hδf : δ f = 1 := by
    have hδ : δ f = θ (D R S f) := by
      simpa [δ] using linearMapEquivDerivation_apply_D (R := R) (S := S) θ f
    exact hδ.trans hθ
  -- The Krull-intersection argument is packaged at the derivation level.
  exact isRegular_of_derivation_eq_one (R := R) (S := S) (f := f) δ hδf

end
