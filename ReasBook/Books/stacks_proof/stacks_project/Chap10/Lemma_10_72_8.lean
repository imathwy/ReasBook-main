import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_51_2_Artin_Rees
import stacks_proof.stacks_project.Chap10.Lemma_10_63_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open PrimeSpectrum
open scoped Pointwise

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain triage:
* primary domain: commutative algebra of associated primes of finite modules over a Noetherian
  ring, with passage to quotients by powers of a principal ideal;
* sampled owner declarations of the same kind:
  `associatedPrimes R M`,
  `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes`,
  `associatedPrimes.subset_of_injective`,
  `Submodule.exists_eq_colon_of_mem_minimalPrimes`;
* best owner abstraction: mathlib's owner set `associatedPrimes`, together with the canonical
  quotient object `QuotSMulTop (x ^ n) M`;
* primitive data: only the module `M`, the element `x`, the associated prime `p`, the minimal
  prime `q`, and the quotient modules `QuotSMulTop (x ^ n) M`;
* derived API: passage from minimal primes over annihilators to associated-prime membership, and
  inclusion of associated primes along the cyclic-submodule image in the quotient.

This numbered item is `source-facing`, but it already lives directly on the owner abstraction
`associatedPrimes`; there is no smaller local wrapper to keep or introduce here.
-/

/-- Helper for Lemma 10.72.8: Artin-Rees gives a positive power whose intersection with a chosen
submodule is forced inside multiplication by `x`. -/
private lemma exists_pow_inf_le_singleton_smul
    (x : R) (N : Submodule R M) :
    ∃ n : ℕ, 0 < n ∧
      (((x ^ n) • (⊤ : Submodule R M)) ⊓ N) ≤ x • N := by
  -- Apply the Artin-Rees cutoff to the cyclic submodule and then evaluate it one step later.
  obtain ⟨c, hc, hAR⟩ := Ideal.exists_pos_pow_inf_eq_pow_smul
    (R := R) (M := M) (Ideal.span ({x} : Set R)) N
  have hpow_left :
      ((x ^ (c + 1)) • (⊤ : Submodule R M)) =
        (Ideal.span ({x} : Set R)) ^ (c + 1) • (⊤ : Submodule R M) := by
    calc
      ((x ^ (c + 1)) • (⊤ : Submodule R M))
          = (Ideal.span ({x ^ (c + 1)} : Set R) : Ideal R) • (⊤ : Submodule R M) := by
              rw [Submodule.ideal_span_singleton_smul]
      _ = (Ideal.span ({x} : Set R)) ^ (c + 1) • (⊤ : Submodule R M) := by
        rw [Ideal.span_singleton_pow]
  refine ⟨c + 1, Nat.succ_pos _, ?_⟩
  calc
    (((x ^ (c + 1)) • (⊤ : Submodule R M)) ⊓ N)
        = ((Ideal.span ({x} : Set R)) ^ (c + 1) • (⊤ : Submodule R M)) ⊓ N := by
            rw [hpow_left]
    _ = (Ideal.span ({x} : Set R)) •
          ((Ideal.span ({x} : Set R)) ^ c • (⊤ : Submodule R M) ⊓ N) := by
      simpa using hAR (c + 1) (Nat.le_succ c)
    _ ≤ (Ideal.span ({x} : Set R)) • N := by
      exact smul_mono_right _ inf_le_right
    _ = x • N := by
      rw [Submodule.ideal_span_singleton_smul]

/-- Helper for Lemma 10.72.8: if the kernel in the cyclic submodule sits inside `xN`, then every
prime minimal over `p + (x)` remains in the support of the quotient by that kernel. -/
private lemma mem_support_quotient_range_of_le_singleton_smul
    {p q : Ideal R} {x : R} {f : R ⧸ p →ₗ[R] M} (hf : Function.Injective f)
    {K : Submodule R (LinearMap.range f)}
    (hK : K ≤ x • (⊤ : Submodule R (LinearMap.range f)))
    (hq : q ∈ (p ⊔ Ideal.span ({x} : Set R)).minimalPrimes) :
    (⟨q, Ideal.minimalPrimes_isPrime hq⟩ : PrimeSpectrum R) ∈
      Module.support R ((LinearMap.range f) ⧸ K) := by
  -- Use the image of the cyclic generator `1 mod p` to witness nonvanishing in the quotient.
  rw [Module.mem_support_iff_exists_annihilator]
  let y : LinearMap.range f :=
    ⟨f (Ideal.Quotient.mk p 1), ⟨Ideal.Quotient.mk p 1, rfl⟩⟩
  refine ⟨Submodule.Quotient.mk y, ?_⟩
  intro r hr
  rw [Submodule.mem_annihilator_span_singleton] at hr
  have hrK : r • y ∈ K := by
    exact (Submodule.Quotient.mk_eq_zero K).1 <| by
      show (Submodule.Quotient.mk (r • y) : (LinearMap.range f) ⧸ K) = 0
      simpa using hr
  have hrx : r • y ∈ x • (⊤ : Submodule R (LinearMap.range f)) := hK hrK
  rcases (Submodule.mem_smul_pointwise_iff_exists (r • y) x
      (⊤ : Submodule R (LinearMap.range f))).1 hrx with
    ⟨z, -, hz⟩
  rcases z.2 with ⟨t, ht⟩
  have hEqM :
      f (x • t) = f (r • (Ideal.Quotient.mk p 1 : R ⧸ p)) := by
    calc
      f (x • t) = x • f t := by rw [LinearMap.map_smul]
      _ = r • f (Ideal.Quotient.mk p 1) := by
        simpa [y, ht] using congrArg Subtype.val hz
      _ = f (r • (Ideal.Quotient.mk p 1 : R ⧸ p)) := by
        rw [LinearMap.map_smul]
  have hEqQuot :
      x • t = r • (Ideal.Quotient.mk p 1 : R ⧸ p) := hf hEqM
  rcases Ideal.Quotient.mk_surjective t with ⟨s, rfl⟩
  have hr_eq : Ideal.Quotient.mk p (x * s) = Ideal.Quotient.mk p r := by
    simpa [Algebra.smul_def, mul_comm] using hEqQuot
  have hr_sub0 : x * s - r ∈ p := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := p) (x * s) r).1 hr_eq
  have hr_sub : r - x * s ∈ p := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using p.neg_mem hr_sub0
  have hp_le_q : p ≤ q := (sup_le_iff.mp hq.1.2).1
  have hx_le_q : Ideal.span ({x} : Set R) ≤ q := (sup_le_iff.mp hq.1.2).2
  have hxsq : x * s ∈ q := by
    apply q.mul_mem_right
    exact (Ideal.span_singleton_le_iff_mem q).1 hx_le_q
  have hsubq : r - x * s ∈ q := hp_le_q hr_sub
  simpa [sub_eq_add_neg, add_assoc] using q.add_mem hsubq hxsq

/-- Lemma 10.72.8: if `p` is an associated prime of a finite module `M` over a Noetherian ring
`R`, and if `q` is minimal over `p + (x)`, then `q` is an associated prime of `M / x^n M`,
written canonically as `QuotSMulTop (x ^ n) M`, for some `n ≥ 1`. -/
-- Proof sketch: choose a cyclic submodule `N ⊆ M` isomorphic to `R ⧸ p` realizing `p` as an
-- associated prime. Artin-Rees gives `n > 0` with `N ∩ (Ideal.span {x}) ^ n • ⊤ ⊆ xN`. The image
-- of `N` in `QuotSMulTop (x ^ n) M` then surjects onto `N / xN ≅ R ⧸ (p ⊔ Ideal.span {x})`,
-- so `q` lies in its support. Since that image is annihilated by both `p` and `x^n`, the prime
-- `q` is minimal in its support, hence associated by the owner minimal-support criterion; finally
-- apply `associatedPrimes.subset_of_injective` to the cyclic-submodule image inside the ambient
-- quotient.
@[stacks 0CN5]
theorem exists_mem_associatedPrimes_quotient_span_singleton_pow_of_mem_minimalPrimes_sup
    (x : R) (p q : Ideal R)
    (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 0 < n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff_exists_injective_linearMap] at hp
  rcases hp with ⟨_, f, hf⟩
  let N : Submodule R M := LinearMap.range f
  let e : (R ⧸ p) ≃ₗ[R] N := LinearEquiv.ofInjective f hf
  obtain ⟨n, hn_pos, hxn⟩ := exists_pow_inf_le_singleton_smul (M := M) x N
  let ψ : N →ₗ[R] QuotSMulTop (x ^ n) M :=
    (Submodule.mkQ ((x ^ n) • (⊤ : Submodule R M))).comp N.subtype
  let K : Submodule R N := LinearMap.ker ψ
  have hK_le : K ≤ x • (⊤ : Submodule R N) := by
    intro y hy
    have hyM : ((y : N) : M) ∈ ((x ^ n) • (⊤ : Submodule R M)) := by
      change ψ y = 0 at hy
      simpa [ψ] using hy
    have hyInf : ((y : N) : M) ∈ (((x ^ n) • (⊤ : Submodule R M)) ⊓ N) := by
      exact ⟨hyM, y.2⟩
    have hyxN : ((y : N) : M) ∈ x • N := hxn hyInf
    rcases (Submodule.mem_smul_pointwise_iff_exists (((y : N) : M)) x N).1 hyxN with
      ⟨z, hz, hxy⟩
    have hyxTop : x • (⟨z, hz⟩ : N) = y := by
      apply Subtype.ext
      simpa using hxy
    exact (Submodule.mem_smul_pointwise_iff_exists y x (⊤ : Submodule R N)).2
      ⟨⟨z, hz⟩, by simp, hyxTop⟩
  let q' : PrimeSpectrum R := ⟨q, Ideal.minimalPrimes_isPrime hq⟩
  have hq_support : q' ∈ Module.support R (N ⧸ K) :=
    mem_support_quotient_range_of_le_singleton_smul (M := M) hf hK_le hq
  have hp_ann : p ≤ Module.annihilator R (N ⧸ K) := by
    -- Elements of `p` already annihilate the whole cyclic submodule `N`.
    have hAnnN : Module.annihilator R N = p := by
      simpa [Ideal.annihilator_quotient] using e.annihilator_eq.symm
    intro r hr
    rw [Module.mem_annihilator]
    intro z
    refine Submodule.Quotient.induction_on K z ?_
    intro y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hrN : r ∈ Module.annihilator R N := by
      simpa [hAnnN] using hr
    have hyzero : r • y = 0 := Module.mem_annihilator.mp hrN y
    simpa [hyzero] using (K.zero_mem : (0 : N) ∈ K)
  have hxpow_ann : Ideal.span ({x ^ n} : Set R) ≤ Module.annihilator R (N ⧸ K) := by
    intro r hr
    rw [Ideal.mem_span_singleton] at hr
    rcases hr with ⟨a, rfl⟩
    rw [Module.mem_annihilator]
    intro z
    refine Submodule.Quotient.induction_on K z ?_
    intro y
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hxK : (x ^ n : R) • y ∈ K := by
      change ψ ((x ^ n : R) • y) = 0
      change (Submodule.mkQ ((x ^ n) • (⊤ : Submodule R M))) (((x ^ n : R) • (y : N) : N) : M) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 <| by
        simpa using
          (Submodule.smul_mem_pointwise_smul (((y : N) : M)) (x ^ n)
            (⊤ : Submodule R M) (by simp))
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using K.smul_mem a hxK
  have hsup_ann : p ⊔ Ideal.span ({x ^ n} : Set R) ≤ Module.annihilator R (N ⧸ K) :=
    sup_le hp_ann hxpow_ann
  have hq_min_support : Minimal (· ∈ Module.support R (N ⧸ K)) q' := by
    refine ⟨hq_support, ?_⟩
    intro r hr_support hrq
    have hr_ann : Module.annihilator R (N ⧸ K) ≤ r.asIdeal :=
      Module.annihilator_le_of_mem_support hr_support
    have hpxn_le_r : p ⊔ Ideal.span ({x ^ n} : Set R) ≤ r.asIdeal :=
      hsup_ann.trans hr_ann
    have hpx_le_r : p ⊔ Ideal.span ({x} : Set R) ≤ r.asIdeal := by
      rw [sup_le_iff]
      refine ⟨(sup_le_iff.mp hpxn_le_r).1, ?_⟩
      have hxpow_le_r : Ideal.span ({x ^ n} : Set R) ≤ r.asIdeal := (sup_le_iff.mp hpxn_le_r).2
      have hxpow_mem : x ^ n ∈ r.asIdeal :=
        (Ideal.span_singleton_le_iff_mem r.asIdeal).1 hxpow_le_r
      exact (Ideal.span_singleton_le_iff_mem r.asIdeal).2 <| by
        exact Ideal.IsPrime.mem_of_pow_mem r.2 n hxpow_mem
    have hq_le_r : q ≤ r.asIdeal := hq.2 ⟨r.2, hpx_le_r⟩ hrq
    exact hq_le_r
  have hq_assoc_K : q ∈ associatedPrimes R (N ⧸ K) := by
    simpa using
      Module.minimal_support_mem_associatedPrimes (R := R) (M := N ⧸ K) q' hq_min_support
  have hq_assoc_range : q ∈ associatedPrimes R (LinearMap.range ψ) := by
    rw [← LinearEquiv.AssociatedPrimes.eq (LinearMap.quotKerEquivRange ψ)]
    simpa [K] using hq_assoc_K
  -- The cyclic image sits inside the ambient quotient via the canonical range inclusion.
  refine ⟨n, hn_pos, ?_⟩
  exact associatedPrimes.subset_of_injective (LinearMap.range ψ).subtype_injective hq_assoc_range

end
