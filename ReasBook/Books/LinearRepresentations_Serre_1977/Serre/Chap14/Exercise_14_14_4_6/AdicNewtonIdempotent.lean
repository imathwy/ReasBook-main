import Mathlib

/-!
# Adic completeness of finite modules and Newton-style idempotent lifting

Two results:

1. `Representation.isAdicComplete_of_module_finite`: a finite module over a Noetherian
   `I`-adically complete commutative ring is itself `I`-adically complete.
2. `Representation.exists_idempotent_lift_newton`: Newton iteration produces an idempotent
   in a finite algebra over a complete Noetherian local base, refining an "almost idempotent"
   element `x` and agreeing with `x` after a reduction map killing `𝔪 • S`.
-/

open TensorProduct

universe u

namespace Representation

/-- Same-universe version of `isAdicComplete_of_module_finite`, proved via
`AdicCompletion.ofTensorProduct`. -/
private theorem isAdicComplete_of_module_finite_aux
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  rw [← AdicCompletion.of_bijective_iff]
  -- Factor `of I M` through `AdicCompletion I R ⊗[R] M`.
  let e₁ : M ≃ₗ[R] (R ⊗[R] M) := (_root_.TensorProduct.lid R M).symm
  let e₂ : (R ⊗[R] M) ≃ₗ[R] (AdicCompletion I R ⊗[R] M) :=
    _root_.TensorProduct.congr (AdicCompletion.ofLinearEquiv I R) (LinearEquiv.refl R M)
  have hone : AdicCompletion.of I R 1 = 1 := by
    simpa using (AdicCompletion.algebraMap_apply I (S := R) 1).symm
  have hcomp : ∀ x : M, AdicCompletion.ofTensorProduct I M (e₂ (e₁ x)) =
      AdicCompletion.of I M x := by
    intro x
    have h₁ : e₁ x = (1 : R) ⊗ₜ[R] x := _root_.TensorProduct.lid_symm_apply x
    have h₂ : e₂ ((1 : R) ⊗ₜ[R] x) = AdicCompletion.of I R 1 ⊗ₜ[R] x := by
      simp [e₂, AdicCompletion.ofLinearEquiv]
    rw [h₁, h₂, AdicCompletion.ofTensorProduct_tmul, hone, one_smul]
  have hbij := AdicCompletion.ofTensorProduct_bijective_of_finite_of_isNoetherian I M
  have heq : (fun x : M => AdicCompletion.ofTensorProduct I M (e₂ (e₁ x))) =
      AdicCompletion.of I M := funext hcomp
  have : Function.Bijective
      (fun x : M => AdicCompletion.ofTensorProduct I M (e₂ (e₁ x))) :=
    hbij.comp (e₂.bijective.comp e₁.bijective)
  rwa [heq] at this

/-- `I`-adic completeness transfers across a linear equivalence. -/
private theorem isAdicComplete_of_linearEquiv
    {R : Type*} [CommRing R] (I : Ideal R)
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) [IsAdicComplete I M] : IsAdicComplete I N := by
  have hmap : ∀ n : ℕ, Submodule.map (e : M →ₗ[R] N) (I ^ n • ⊤ : Submodule R M) =
      (I ^ n • ⊤ : Submodule R N) := by
    intro n
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have hmem : ∀ (n : ℕ) (x : M), x ∈ (I ^ n • ⊤ : Submodule R M) ↔
      e x ∈ (I ^ n • ⊤ : Submodule R N) := by
    intro n x
    constructor
    · intro hx
      rw [← hmap n]
      exact Submodule.mem_map_of_mem hx
    · intro hx
      rw [← hmap n] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      rwa [← e.injective hxy]
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · -- Hausdorff
    constructor
    intro x hx
    have : e.symm x = 0 := by
      apply IsHausdorff.haus (inferInstance : IsHausdorff I M) (e.symm x)
      intro n
      rw [SModEq.zero, hmem n, e.apply_symm_apply]
      exact SModEq.zero.mp (hx n)
    simpa using congrArg e this
  · -- Precomplete
    constructor
    intro f hf
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I M)
      (f := fun n => e.symm (f n)) (by
        intro m n hmn
        rw [SModEq.sub_mem, hmem m, map_sub, e.apply_symm_apply, e.apply_symm_apply,
          ← SModEq.sub_mem]
        exact hf hmn)
    refine ⟨e L, fun n => ?_⟩
    have h := hL n
    rw [SModEq.sub_mem, hmem n, map_sub, e.apply_symm_apply] at h
    rw [SModEq.sub_mem]
    exact h

/-- A finite module over a Noetherian `I`-adically complete commutative ring is itself
`I`-adically complete. -/
theorem isAdicComplete_of_module_finite
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e : ((Fin n → R) ⧸ LinearMap.ker f) ≃ₗ[R] M := f.quotKerEquivOfSurjective hf
  haveI : IsAdicComplete I ((Fin n → R) ⧸ LinearMap.ker f) :=
    isAdicComplete_of_module_finite_aux I
  exact isAdicComplete_of_linearEquiv I e

/-! ## Newton iteration for idempotents -/

section Newton

variable {A : Type*} [CommRing A] {S : Type*} [CommRing S] [Algebra A S]

/-- `I • ⊤ ⊆ S` absorbs multiplication by arbitrary elements of `S`. -/
private theorem mul_mem_ideal_smul_top {I : Ideal A} {y : S}
    (hy : y ∈ I • (⊤ : Submodule A S)) (s : S) : s * y ∈ I • (⊤ : Submodule A S) := by
  refine Submodule.smul_induction_on hy (fun a ha t _ => ?_) (fun u v hu hv => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [mul_add]
    exact Submodule.add_mem _ hu hv

/-- The Newton iteration `y ↦ 3y² - 2y³` improving an approximate idempotent. -/
private def newton (x : S) : ℕ → S
  | 0 => x
  | n + 1 => 3 * (newton x n) ^ 2 - 2 * (newton x n) ^ 3

private lemma newton_zero (x : S) : newton x 0 = x := rfl

private lemma newton_succ (x : S) (n : ℕ) :
    newton x (n + 1) = 3 * (newton x n) ^ 2 - 2 * (newton x n) ^ 3 := rfl

private theorem newton_mem_adjoin (x : S) (n : ℕ) :
    newton x n ∈ Algebra.adjoin A {x} := by
  induction n with
  | zero => exact Algebra.self_mem_adjoin_singleton A x
  | succ n ih =>
    have h3 : (3 : S) ∈ Algebra.adjoin A {x} := by
      have h := Subalgebra.algebraMap_mem (Algebra.adjoin A {x}) (3 : A)
      rwa [map_ofNat] at h
    have h2 : (2 : S) ∈ Algebra.adjoin A {x} := by
      have h := Subalgebra.algebraMap_mem (Algebra.adjoin A {x}) (2 : A)
      rwa [map_ofNat] at h
    rw [newton_succ]
    exact sub_mem (mul_mem h3 (pow_mem ih 2)) (mul_mem h2 (pow_mem ih 3))

/-- The defect `(newton x n)² - newton x n` is divisible by `(x² - x) ^ (2 ^ n)`. -/
private theorem newton_eps_factor (x : S) (n : ℕ) :
    ∃ s : S, (newton x n) ^ 2 - newton x n = (x ^ 2 - x) ^ (2 ^ n) * s := by
  induction n with
  | zero => exact ⟨1, by simp [newton_zero]⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨s ^ 2 * (4 * (newton x n) ^ 2 - 4 * (newton x n) - 3), ?_⟩
    have key : (3 * (newton x n) ^ 2 - 2 * (newton x n) ^ 3) ^ 2 -
        (3 * (newton x n) ^ 2 - 2 * (newton x n) ^ 3) =
        ((newton x n) ^ 2 - newton x n) ^ 2 *
          (4 * (newton x n) ^ 2 - 4 * (newton x n) - 3) := by
      ring
    have hpow : ((x ^ 2 - x) ^ (2 ^ (n + 1)) : S) = ((x ^ 2 - x) ^ (2 ^ n)) ^ 2 := by
      rw [pow_succ 2 n, pow_mul]
    rw [newton_succ, key, hs, hpow]
    ring

end Newton

/-- **Newton-style idempotent lifting.** If `A` is a complete Noetherian local ring, `S` a
finite `A`-algebra, and `x ∈ S` is "almost idempotent" in the sense that powers of `x² - x`
fall arbitrarily deep into the `𝔪`-adic filtration of `S`, then Newton iteration converges to
a genuine idempotent `e ∈ A[x] ⊆ S` with the same image as `x` under any reduction map
killing `𝔪 • S`. -/
theorem exists_idempotent_lift_newton
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {S : Type*} [CommRing S] [Algebra A S] [Module.Finite A S]
    (x : S)
    (hsmall : ∃ c : ℕ, ∀ n : ℕ, (x ^ 2 - x) ^ (n + c) ∈
      ((IsLocalRing.maximalIdeal A) ^ n • (⊤ : Submodule A S)))
    {T : Type*} [CommRing T] [Algebra A T] (red : S →ₐ[A] T)
    (hker : ∀ s ∈ ((IsLocalRing.maximalIdeal A) • (⊤ : Submodule A S)), red s = 0)
    (hx : red (x ^ 2 - x) = 0) :
    ∃ e : S, IsIdempotentElem e ∧ e ∈ Algebra.adjoin A {x} ∧ red e = red x := by
  obtain ⟨c, hsmall⟩ := hsmall
  set I : Ideal A := IsLocalRing.maximalIdeal A with hIdef
  haveI : IsAdicComplete I S := isAdicComplete_of_module_finite I
  -- Step 1: powers of `x² - x` lie deep in the filtration.
  have hpow_mem : ∀ m n : ℕ, m + c ≤ 2 ^ n →
      (x ^ 2 - x) ^ (2 ^ n) ∈ (I ^ m • ⊤ : Submodule A S) := by
    intro m n h
    have h1 : (x ^ 2 - x) ^ (m + c) ∈ (I ^ m • ⊤ : Submodule A S) := hsmall m
    have h2 : (x ^ 2 - x) ^ (2 ^ n) =
        (x ^ 2 - x) ^ (2 ^ n - (m + c)) * (x ^ 2 - x) ^ (m + c) := by
      rw [← pow_add, Nat.sub_add_cancel h]
    rw [h2]
    exact mul_mem_ideal_smul_top h1 _
  -- Step 2: the defects of the Newton iterates are small.
  have heps_mem : ∀ m n : ℕ, m + c ≤ 2 ^ n →
      (newton x n) ^ 2 - newton x n ∈ (I ^ m • ⊤ : Submodule A S) := by
    intro m n h
    obtain ⟨s, hs⟩ := newton_eps_factor x n
    rw [hs, mul_comm]
    exact mul_mem_ideal_smul_top (hpow_mem m n h) s
  -- Step 3: consecutive Newton iterates are close.
  have hstep : ∀ m n : ℕ, m + c ≤ 2 ^ n →
      newton x (n + 1) - newton x n ∈ (I ^ m • ⊤ : Submodule A S) := by
    intro m n h
    have hd : newton x (n + 1) - newton x n =
        (-(2 * newton x n - 1)) * ((newton x n) ^ 2 - newton x n) := by
      rw [newton_succ]; ring
    rw [hd]
    exact mul_mem_ideal_smul_top (heps_mem m n h) _
  -- Step 4: telescoping.
  have htele : ∀ m k l : ℕ, m + c ≤ k → k ≤ l →
      newton x l - newton x k ∈ (I ^ m • ⊤ : Submodule A S) := by
    intro m k l hk hkl
    induction l, hkl using Nat.le_induction with
    | base => simp
    | succ l hkl ih =>
      have h1 : newton x (l + 1) - newton x l ∈ (I ^ m • ⊤ : Submodule A S) :=
        hstep m l ((hk.trans hkl).trans l.lt_two_pow_self.le)
      have heq : newton x (l + 1) - newton x k =
          (newton x (l + 1) - newton x l) + (newton x l - newton x k) := by ring
      rw [heq]
      exact Submodule.add_mem _ h1 ih
  -- Step 5: the limit of the Newton iterates.
  have hcoh : ∀ {m n : ℕ}, m ≤ n →
      newton x (m + c) ≡ newton x (n + c) [SMOD (I ^ m • ⊤ : Submodule A S)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have h := htele m (m + c) (n + c) le_rfl (by omega)
    have heq : newton x (m + c) - newton x (n + c) =
        -(newton x (n + c) - newton x (m + c)) := by ring
    rw [heq]
    exact Submodule.neg_mem _ h
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I S)
    (f := fun m => newton x (m + c)) hcoh
  have hLdiff : ∀ m : ℕ, newton x (m + c) - L ∈ (I ^ m • ⊤ : Submodule A S) :=
    fun m => SModEq.sub_mem.mp (hL m)
  -- Step 6: the limit is idempotent (by Hausdorff-ness of the filtration).
  have hidem : IsIdempotentElem L := by
    have hzero : L ^ 2 - L = 0 := by
      refine IsHausdorff.haus (inferInstance : IsHausdorff I S) _ (fun m => ?_)
      rw [SModEq.zero]
      have h1 : newton x (m + c) - L ∈ (I ^ m • ⊤ : Submodule A S) := hLdiff m
      have h2 : (newton x (m + c)) ^ 2 - newton x (m + c) ∈ (I ^ m • ⊤ : Submodule A S) :=
        heps_mem m (m + c) (m + c).lt_two_pow_self.le
      have h3 : L ^ 2 - (newton x (m + c)) ^ 2 ∈ (I ^ m • ⊤ : Submodule A S) := by
        have heq : L ^ 2 - (newton x (m + c)) ^ 2 =
            (L + newton x (m + c)) * (-(newton x (m + c) - L)) := by ring
        rw [heq]
        exact mul_mem_ideal_smul_top (Submodule.neg_mem _ h1) _
      have heq : L ^ 2 - L = (L ^ 2 - (newton x (m + c)) ^ 2) +
          ((newton x (m + c)) ^ 2 - newton x (m + c)) + (newton x (m + c) - L) := by ring
      rw [heq]
      exact Submodule.add_mem _ (Submodule.add_mem _ h3 h2) h1
    show L * L = L
    rw [← pow_two]
    exact sub_eq_zero.mp hzero
  -- Step 7: the limit lies in the subalgebra generated by `x`.
  have hadj : L ∈ Algebra.adjoin A {x} := by
    set N : Submodule A S := Subalgebra.toSubmodule (Algebra.adjoin A {x}) with hNdef
    have hq : ∀ m : ℕ, N.mkQ L ∈ (I ^ m • ⊤ : Submodule A (S ⧸ N)) := by
      intro m
      have h1 : N.mkQ (newton x (m + c) - L) ∈
          Submodule.map N.mkQ (I ^ m • ⊤ : Submodule A S) :=
        Submodule.mem_map_of_mem (hLdiff m)
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h1
      have h2 : N.mkQ (newton x (m + c)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact newton_mem_adjoin x (m + c)
      have h3 : N.mkQ (newton x (m + c) - L) = -(N.mkQ L) := by
        rw [map_sub, h2, zero_sub]
      rw [h3] at h1
      have h4 := Submodule.neg_mem _ h1
      rwa [neg_neg] at h4
    have hzero : N.mkQ L = 0 :=
      IsHausdorff.haus (inferInstance : IsHausdorff I (S ⧸ N)) _
        (fun m => SModEq.zero.mpr (hq m))
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hzero
    exact hzero
  -- Step 8: the limit has the same image as `x` under the reduction map.
  have hredx : red x * red x = red x := by
    have h := hx
    rw [map_sub, map_pow, sub_eq_zero] at h
    rw [← pow_two]
    exact h
  have hred_e : ∀ n : ℕ, red (newton x n) = red x := by
    intro n
    induction n with
    | zero => rw [newton_zero]
    | succ n ih =>
      rw [newton_succ, map_sub, map_mul, map_mul, map_pow, map_pow, ih,
        map_ofNat, map_ofNat]
      have h2 : red x ^ 2 = red x := by rw [pow_two]; exact hredx
      have h3 : red x ^ 3 = red x := by rw [pow_succ, h2]; exact hredx
      rw [h2, h3]
      ring
  have hL_red : red L = red x := by
    have h1 : newton x (1 + c) - L ∈ (I • ⊤ : Submodule A S) := by
      have h := hLdiff 1
      rwa [pow_one] at h
    have h2 : red (newton x (1 + c) - L) = 0 := hker _ h1
    rw [map_sub, hred_e] at h2
    exact (sub_eq_zero.mp h2).symm
  exact ⟨L, hidem, hadj, hL_red⟩

end Representation
