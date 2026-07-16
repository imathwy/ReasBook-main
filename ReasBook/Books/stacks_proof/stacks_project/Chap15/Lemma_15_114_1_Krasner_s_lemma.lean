import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_160_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing Polynomial

universe u

section

variable {A : Type u} [CommRing A] [IsDomain A] [IsCompleteLocalRing A] [Ring.KrullDimLE 1 A]

/- Domain-style sampling:
- primary domain: Henselian local algebra of complete local domains, with source-facing control of
  roots under small coefficient perturbations;
- sampled owner-level declarations of the same kind:
  `Ring.KrullDimLE`,
  `Ring.krullDimLE_one_iff_of_noZeroDivisors`,
  `Ideal.mem_map_C_iff`,
  `HenselianLocalRing.is_henselian`,
  `HenselianRing.is_henselian`,
  `IsAdicComplete.henselianRing`,
  `localRing_henselian_of_isCompleteLocalRing`;
- best owner abstraction: the canonical local lifting owner is `HenselianLocalRing`, obtained here
  from completeness via `localRing_henselian_of_isCompleteLocalRing`; polynomial perturbations with
  coefficients in `𝔪 ^ n` are canonically expressed by membership in `(𝔪 ^ n).map C`,
  congruence modulo powers of the maximal ideal is canonically expressed by `SModEq`, and the
  dimension hypothesis is most canonically carried by the owner instance `[Ring.KrullDimLE 1 A]`;
- primitive data: the complete local domain `A`, the source-facing one-dimensional hypothesis
  encoded canonically by `[Ring.KrullDimLE 1 A]`, the polynomial `P`, the chosen root `α`, the
  nonvanishing derivative value `P.derivative.eval α`, and the target precision `c`;
- derived API: eventual stability of the root under perturbations lying in the polynomial ideal
  `(𝔪 ^ n).map C`.

Layer triage:
- `source-facing`: `exists_root_of_small_polynomial_perturbation`;
- `core/canonical`: `HenselianLocalRing`, `HenselianRing`, `Ideal.map`, and `SModEq`;
- `bridge/view`: `localRing_henselian_of_isCompleteLocalRing`, which upgrades complete-local data
  to the henselian owner used in the background proof strategy.
-/
local notation "𝔪" => maximalIdeal A

/-- Helper for Lemma 15.114.1 (Krasner's lemma): a nonfield local ring has a nonzero element in
its maximal ideal. -/
lemma exists_mem_maximalIdeal_ne_zero_of_not_isField
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : ¬ IsField R) :
    ∃ π : R, π ∈ maximalIdeal R ∧ π ≠ 0 := by
  -- A local ring is a field exactly when its maximal ideal vanishes, so a nonfield branch gives a
  -- strict inclusion `⊥ < maximalIdeal R`.
  have hm_ne : maximalIdeal R ≠ ⊥ := by
    intro hbot
    exact hR ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr hbot)
  have hlt : (⊥ : Ideal R) < maximalIdeal R := bot_lt_iff_ne_bot.mpr hm_ne
  rcases SetLike.exists_of_lt hlt with ⟨π, hπm, hπ0⟩
  -- Any element outside `⊥` is automatically nonzero.
  refine ⟨π, hπm, ?_⟩
  intro hzero
  exact hπ0 (hzero ▸ Ideal.zero_mem _)

/-- Helper for Lemma 15.114.1 (Krasner's lemma): if the coefficients of `Q` lie in `I ^ n`, then
so do both `Q.eval x` and `Q.derivative.eval x`. -/
lemma eval_and_derivative_eval_mem_of_mem_map_C
    {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} {Q : R[X]} {x : R}
    (hQ : Q ∈ (I ^ n).map C) : Q.eval x ∈ I ^ n ∧ Q.derivative.eval x ∈ I ^ n := by
  -- First translate ideal membership of the polynomial into coefficientwise membership.
  have hcoeff : ∀ k : ℕ, Q.coeff k ∈ I ^ n := Ideal.mem_map_C_iff.mp hQ
  have h_eval : Q.eval x ∈ I ^ n := by
    -- Evaluation is a finite sum of coefficient terms, and each summand stays in the ideal.
    rw [eval_eq_sum]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right (x ^ k) _ (hcoeff k)
  have hderiv_coeff : ∀ k : ℕ, Q.derivative.coeff k ∈ I ^ n := by
    -- Differentiation only multiplies coefficients by natural-number scalars.
    intro k
    rw [Polynomial.coeff_derivative]
    exact Ideal.mul_mem_right ((k : R) + 1) _ (hcoeff (k + 1))
  have h_deriv_eval : Q.derivative.eval x ∈ I ^ n := by
    -- Apply the same coefficientwise argument to the derivative polynomial.
    rw [eval_eq_sum]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right (x ^ k) _ (hderiv_coeff k)
  exact ⟨h_eval, h_deriv_eval⟩

/-- Helper for Lemma 15.114.1 (Krasner's lemma): over a field the maximal ideal is zero, so any
polynomial whose coefficients lie in `(maximalIdeal A)^1` is the zero polynomial. -/
lemma zero_poly_of_mem_maximal_pow_map_C_field
    {K : Type u} [Field K] {Q : K[X]} (hQ : Q ∈ ((maximalIdeal K) ^ 1).map C) : Q = 0 := by
  -- In the field case the maximal ideal is `⊥`, so every coefficient of `Q` is zero.
  have hmax : maximalIdeal K = (⊥ : Ideal K) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField K)
  rw [hmax, pow_one] at hQ
  have hcoeff := Ideal.mem_map_C_iff.mp hQ
  ext k
  simpa using hcoeff k

/-- Helper for Lemma 15.114.1 (Krasner's lemma): in a one-dimensional local domain, every nonzero
principal ideal has radical containing the maximal ideal. -/
lemma maximalIdeal_le_radical_span_singleton_of_nonzero
    {d : A} (hd : d ≠ 0) :
    𝔪 ≤ Ideal.radical (Ideal.span ({d} : Set A)) := by
  -- Any prime containing `(d)` is nonzero, hence maximal by the dimension-one hypothesis, and
  -- locality identifies that maximal prime with `𝔪`.
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  intro J hJ
  rcases hJ with ⟨hspan, hJprime⟩
  intro x hx
  have hdJ : d ∈ J := hspan (Ideal.subset_span (by simp))
  have hJne : J ≠ ⊥ := by
    intro hbot
    exact hd (by simpa [hbot] using hdJ)
  have hJmax : J.IsMaximal :=
    (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance) J hJne hJprime
  have hJeq : J = 𝔪 := IsLocalRing.eq_maximalIdeal hJmax
  simpa [hJeq] using hx

/-- Helper for Lemma 15.114.1 (Krasner's lemma): quotienting a one-dimensional local domain by a
nonzero principal ideal drops the Krull dimension to at most `0`. -/
lemma krullDimLE_zero_quotient_span_singleton_of_nonzero
    {d : A} (hd : d ≠ 0) :
    Ring.KrullDimLE 0 (A ⧸ Ideal.span ({d} : Set A)) := by
  let I : Ideal A := Ideal.span ({d} : Set A)
  let f : A →+* A ⧸ I := Ideal.Quotient.mk I
  -- Every prime of the quotient comes from a nonzero prime of `A`, hence is maximal there.
  refine Ring.KrullDimLE.mk₀ ?_
  intro J hJ
  let P : Ideal A := Ideal.comap f J
  have hPprime : P.IsPrime := Ideal.comap_isPrime f J
  have hd_mem_P : d ∈ P := by
    change f d ∈ J
    simpa [f, I] using (J.zero_mem : (0 : A ⧸ I) ∈ J)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hd_zero : d = 0 := by
      have : d ∈ (⊥ : Ideal A) := by simpa [P, hPbot] using hd_mem_P
      simpa using this
    exact hd hd_zero
  have hPmax : P.IsMaximal :=
    (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp inferInstance) P hPne hPprime
  have hker_le : RingHom.ker f ≤ P := by
    intro x hx
    change f x ∈ J
    simpa [RingHom.mem_ker.mp hx] using (J.zero_mem : (0 : A ⧸ I) ∈ J)
  have hmapmax : (Ideal.map f P).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := f) Ideal.Quotient.mk_surjective hker_le
  have hmap_eq : Ideal.map f P = J := by
    simpa [P, f] using
      (Ideal.map_comap_of_surjective f Ideal.Quotient.mk_surjective J)
  simpa [hmap_eq] using hmapmax

/-- Helper for Lemma 15.114.1 (Krasner's lemma): in the presence of Noetherianity, the radical
containment for a nonzero principal ideal upgrades to containment of a power of the maximal
ideal. -/
lemma maximalIdeal_pow_le_span_singleton_of_nonzero_of_isNoetherian [IsNoetherianRing A]
    {π : A} (hπ0 : π ≠ 0) :
    ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({π} : Set A) := by
  -- First identify the radical of the principal ideal `(π)` with the maximal ideal.
  have hrad : 𝔪 ≤ Ideal.radical (Ideal.span ({π} : Set A)) :=
    maximalIdeal_le_radical_span_singleton_of_nonzero (A := A) hπ0
  -- Then use the standard finitely-generated-ideal nilpotence bridge in the Noetherian setting.
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (Ideal.fg_of_isNoetherianRing 𝔪)

/-- Helper for Lemma 15.114.1 (Krasner's lemma): in a complete local domain of Krull dimension at
most `1`, every nonzero principal ideal should contain a power of the maximal ideal. -/
lemma maximalIdeal_pow_le_span_singleton_of_nonzero
    {d : A} (hd : d ≠ 0) :
    ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({d} : Set A) := by
  -- The quotient by `(d)` is now known to be zero-dimensional; what is still missing is an earlier
  -- dependency-closed theorem that turns that zero-dimensional complete-local quotient into a
  -- nilpotent maximal ideal, equivalently a kernel-power containment back in `A`.
  sorry

/-- Helper for Lemma 15.114.1 (Krasner's lemma): once a power of the maximal ideal lies in the
principal ideal `(d)`, every deeper power lies in `(d) · 𝔪^c`. -/
lemma maximalIdeal_pow_add_le_span_singleton_mul_pow
    {d : A} {s c : ℕ}
    (hs : 𝔪 ^ s ≤ Ideal.span ({d} : Set A)) :
    𝔪 ^ (s + c) ≤ Ideal.span ({d} : Set A) * 𝔪 ^ c := by
  -- Rewrite the deeper power as a product and use monotonicity in the first factor.
  calc
    𝔪 ^ (s + c) = 𝔪 ^ s * 𝔪 ^ c := by rw [pow_add]
    _ ≤ Ideal.span ({d} : Set A) * 𝔪 ^ c := Ideal.mul_mono_left hs

/-- Helper for Lemma 15.114.1 (Krasner's lemma): a coefficientwise `𝔪^n` perturbation changes
the value and derivative value at any point by elements of `𝔪^n`. -/
lemma perturbation_eval_and_derivative_sub_mem
    {P Q : A[X]} {α : A} {n : ℕ}
    (hQ : Q ∈ (𝔪 ^ n).map C) :
    (P + Q).eval α - P.eval α ∈ 𝔪 ^ n ∧
      (P + Q).derivative.eval α - P.derivative.eval α ∈ 𝔪 ^ n := by
  -- First isolate the value and derivative of the perturbation itself.
  rcases eval_and_derivative_eval_mem_of_mem_map_C (I := 𝔪) hQ with ⟨hEvalQ, hDerivQ⟩
  refine ⟨?_, ?_⟩
  · -- Evaluating `P + Q` differs from evaluating `P` exactly by `Q.eval α`.
    simpa [Polynomial.eval_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEvalQ
  · -- The same additivity holds after differentiating.
    simpa [Polynomial.derivative_add, Polynomial.eval_add, sub_eq_add_neg,
      add_assoc, add_left_comm, add_comm] using hDerivQ

/-- Helper for Lemma 15.114.1 (Krasner's lemma): a linear perturbation statement already forces
deep powers of the maximal ideal to lie in the corresponding principal ideal. -/
lemma maximalIdeal_pow_le_span_singleton_of_linear_perturbation
    {d : A}
    (hlin :
      ∃ n : ℕ, ∀ Q : A[X], Q ∈ (𝔪 ^ n).map C →
        ∃ β : A, (((C d) * X) + Q).IsRoot β) :
    ∃ n : ℕ, 𝔪 ^ n ≤ Ideal.span ({d} : Set A) := by
  -- Constant perturbations of the linear polynomial `d * X` already encode divisibility by `d`.
  rcases hlin with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro x hx
  have hQ : C x ∈ (𝔪 ^ n).map C := by
    -- The constant polynomial `C x` has coefficient `x` in degree `0` and `0` elsewhere.
    rw [Ideal.mem_map_C_iff]
    intro k
    cases k with
    | zero =>
        simpa using hx
    | succ k =>
        simp
  rcases hn (C x) hQ with ⟨β, hβ⟩
  have hEval : (((C d) * X) + C x).eval β = 0 := by
    -- Unpack `IsRoot` before simplifying the concrete evaluation formula.
    simpa [Polynomial.IsRoot] using hβ
  have hEq : d * β + x = 0 := by
    -- Evaluating the linear polynomial at a root gives the explicit relation `d * β + x = 0`.
    simpa using hEval
  rw [Ideal.mem_span_singleton']
  refine ⟨-β, ?_⟩
  calc
    (-β) * d = -(d * β) := by ring
    _ = x := by
      exact (eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hEq)).symm

/-- Helper for Lemma 15.114.1 (Krasner's lemma): once every nonzero principal ideal contains a
power of `𝔪`, multiplying a fraction by a high enough power of a fixed nonzero `π ∈ 𝔪` clears its
denominator. -/
lemma fractionRing_mul_pow_mem_of_nonzero_maximal
    {π : A} (hπm : π ∈ 𝔪)
    (hopen : ∀ {d : A}, d ≠ 0 → ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({d} : Set A))
    (x : FractionRing A) :
    ∃ m : ℕ, ∃ a : A,
      x * algebraMap A (FractionRing A) (π ^ m) = algebraMap A (FractionRing A) a := by
  -- Write the fraction as `a / b` with `b ≠ 0`.
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective A x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  -- Openness of `(b)` turns a high power of `π` into a multiple of `b`.
  obtain ⟨m, hm⟩ := hopen hb0
  have hπpow_mem_m : π ^ m ∈ 𝔪 ^ m := Ideal.pow_mem_pow hπm m
  have hπpow_mem_span : π ^ m ∈ Ideal.span ({b} : Set A) := hm hπpow_mem_m
  rw [Ideal.mem_span_singleton'] at hπpow_mem_span
  rcases hπpow_mem_span with ⟨c, hc⟩
  refine ⟨m, a * c, ?_⟩
  have hbK :
      algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  -- Rewrite `π ^ m` as `c * b` and cancel the denominator inside the fraction field.
  calc
    x * algebraMap A (FractionRing A) (π ^ m)
        = ((algebraMap A (FractionRing A) a) / (algebraMap A (FractionRing A) b)) *
            algebraMap A (FractionRing A) (π ^ m) := by
              rw [← hfrac]
    _ = ((algebraMap A (FractionRing A) a) / (algebraMap A (FractionRing A) b)) *
          (algebraMap A (FractionRing A) c * algebraMap A (FractionRing A) b) := by
            rw [← hc, RingHom.map_mul]
    _ = algebraMap A (FractionRing A) a * algebraMap A (FractionRing A) c := by
          field_simp [div_eq_mul_inv, hbK]
    _ = algebraMap A (FractionRing A) (a * c) := by
          rw [RingHom.map_mul]

/-- Helper for Lemma 15.114.1 (Krasner's lemma): after clearing denominators against powers of a
fixed nonzero `π ∈ 𝔪`, the inverse of `P'(α)` can be rewritten as `a / π^m`. -/
lemma derivative_inverse_scaled_by_pi_power
    {P : A[X]} {α π : A} (hπm : π ∈ 𝔪)
    (hopen : ∀ {d : A}, d ≠ 0 → ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({d} : Set A))
    (hderiv : P.derivative.eval α ≠ 0) :
    ∃ m : ℕ, ∃ a : A,
      algebraMap A (FractionRing A) a *
          algebraMap A (FractionRing A) (P.derivative.eval α) =
        algebraMap A (FractionRing A) (π ^ m) := by
  -- Apply denominator-clearing to the inverse of the derivative value in the fraction field.
  obtain ⟨m, a, ha⟩ :=
    fractionRing_mul_pow_mem_of_nonzero_maximal (A := A) hπm hopen
      ((algebraMap A (FractionRing A) (P.derivative.eval α))⁻¹)
  refine ⟨m, a, ?_⟩
  have hderivK :
      algebraMap A (FractionRing A) (P.derivative.eval α) ≠ 0 := by
    intro hzero
    apply hderiv
    exact (IsFractionRing.injective A (FractionRing A)) (by simpa using hzero)
  -- Multiply the cleared-denominator identity by `P'(α)` and cancel the inverse.
  have hmul :=
    congrArg
      (fun z : FractionRing A ↦
        algebraMap A (FractionRing A) (P.derivative.eval α) * z) ha
  simpa [RingHom.map_mul, mul_assoc, hderivK, mul_comm, mul_left_comm] using hmul.symm

/-- Helper for Lemma 15.114.1 (Krasner's lemma): once nonzero principal ideals are known to be
open, the remaining source-faithful work is the translated-and-scaled Hensel step. -/
lemma exists_root_of_small_polynomial_perturbation_of_principal_open
    {π : A} (hπm : π ∈ 𝔪)
    (hopen : ∀ {d : A}, d ≠ 0 → ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({d} : Set A))
    (P : A[X]) {α : A} (hα : P.IsRoot α) (hderiv : P.derivative.eval α ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : A[X], Q ∈ (𝔪 ^ n).map C →
      ∃ β : A, (P + Q).IsRoot β ∧ β ≡ α [SMOD 𝔪 ^ c] := by
  -- First rewrite the inverse of `P'(α)` with denominator a power of the chosen `π ∈ 𝔪`.
  obtain ⟨m, a, ha⟩ :=
    derivative_inverse_scaled_by_pi_power (A := A) (P := P) (α := α) (π := π)
      hπm hopen hderiv
  -- TODO: translate `P + Q` by `α`, scale by `π ^ c`, and use `ha` together with
  -- `perturbation_eval_and_derivative_sub_mem` to build the normalized Hensel polynomial at `0`.
  -- A root of that normalized polynomial then back-substitutes to the required `β`.
  sorry

-- Proof sketch: use the canonical henselian owner supplied by completeness together with the
-- canonical dimension-at-most-one owner `[Ring.KrullDimLE 1 A]` to compare the nonzero derivative
-- value `P.derivative.eval α` with a sufficiently high power of `𝔪`. For `Q ∈ (𝔪 ^ n).map C`,
-- the values `(P + Q).eval α` and `(P + Q).derivative.eval α` are small perturbations of the
-- corresponding values for `P`; the henselian lifting step then produces a root congruent to `α`
-- modulo `𝔪 ^ c`. The zero-dimensional edge case allowed by `[Ring.KrullDimLE 1 A]` is harmless
-- for this conclusion, so the exact equality `ringKrullDim A = 1` is omitted from the main API.
/-- Lemma 15.114.1 (Krasner's lemma): in a complete local domain of Krull dimension at most `1`,
a simple root `α` of a polynomial `P` persists under sufficiently small perturbations of the
coefficients, with the new root congruent to `α` modulo any prescribed power of the maximal
ideal. This keeps the source mathematics while replacing the redundant exact equality
`ringKrullDim A = 1` by the canonical owner hypothesis `[Ring.KrullDimLE 1 A]`. -/
@[stacks 09EI]
theorem exists_root_of_small_polynomial_perturbation
    (P : A[X]) {α : A} (hα : P.IsRoot α) (hderiv : P.derivative.eval α ≠ 0) (c : ℕ) :
    ∃ n : ℕ, ∀ Q : A[X], Q ∈ (𝔪 ^ n).map C →
      ∃ β : A, (P + Q).IsRoot β ∧ β ≡ α [SMOD 𝔪 ^ c] := by
  classical
  by_cases hA : IsField A
  · letI : Field A := hA.toField
    -- In the field case `𝔪 = ⊥`, so every admissible perturbation is zero and `β = α` works.
    refine ⟨1, ?_⟩
    intro Q hQ
    have hQzero : Q = 0 := zero_poly_of_mem_maximal_pow_map_C_field hQ
    refine ⟨α, ?_, ?_⟩
    · simpa [hQzero] using hα
    · exact SModEq.rfl
  · -- Route correction: the standard Henselian API only handles unit derivatives, so the
    -- nonfield branch must pass through a principal-ideal openness statement before Newton
    -- iteration can start.
    rcases exists_mem_maximalIdeal_ne_zero_of_not_isField hA with ⟨π, hπm, _hπ0⟩
    have hopen : ∀ {d : A}, d ≠ 0 → ∃ s : ℕ, 𝔪 ^ s ≤ Ideal.span ({d} : Set A) := by
      -- This packages the missing openness bridge in the exact form needed by the denominator
      -- clearing step.
      intro d hd
      exact maximalIdeal_pow_le_span_singleton_of_nonzero (A := A) hd
    -- Once principal ideals are open, the remaining source proof is the translated/scaled Hensel
    -- normalization around `α`.
    exact
      exists_root_of_small_polynomial_perturbation_of_principal_open
        (A := A) hπm hopen P hα hderiv c

end
