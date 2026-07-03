import Mathlib
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_72_7 (from Chap10) -/
universe u

open RingTheory Sequence IsLocalRing

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.72.7: a finite subsingleton module has infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Subsingleton M] :
    moduleDepth R M = ⊤ := by
  -- For a subsingleton module, the top submodule is already `⊥`, so `𝔪 • M = M`.
  have htop_eq_bot : (⊤ : Submodule R M) = ⊥ := by
    ext m
    simp [Subsingleton.elim m 0]
  have hsmul_bot : maximalIdeal R • (⊥ : Submodule R M) = ⊥ := by
    ext m
    simp
  have hsmul_top : maximalIdeal R • (⊤ : Submodule R M) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal R) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal R) M hsmul_top

/-- Helper for Lemma 10.72.7: a maximal-ideal nonzerodivisor forces positive depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ moduleDepth R M := by
  letI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
  -- The singleton sequence `[x]` is regular, so its length contributes to the depth supremum.
  have hnil : IsRegular (R := R) (M := QuotSMulTop x M) [] := by
    simpa using (IsRegular.nil R (QuotSMulTop x M))
  have hsingleton_reg : IsRegular M [x] := by
    exact IsRegular.cons hreg hnil
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal R := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/- Domain-style sampling:
* primary domain: depth and regular sequences for finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_append_of_isRegular_of_quotient_isRegular`,
  `exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes`;
* best owner abstraction: the local depth owner is the chapter bridge `moduleDepth R M`, while
  regular sequences are owned by `RingTheory.Sequence.IsRegular`;
* source/core/bridge triage:
  `source-facing`: the one-step depth drop and the extension of a regular sequence to maximal
  length;
  `core/canonical`: `moduleDepth` and `IsRegular`;
  `bridge/view`: the quotient module `QuotSMulTop x M` and the tail list `rs'`.

Primitive data are only the module, the regular sequence owner predicate, and the quotient owner
`QuotSMulTop x M`. A package bundling the appended regularity proof, maximal-ideal membership, and
length equality is derived theorem-shaped API, so it should not be a public class. -/

namespace IsSMulRegular

/-- Helper for Lemma 10.72.7: quotienting by a maximal-ideal nonzerodivisor lowers depth by at
most one. -/
private lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    moduleDepth R (QuotSMulTop x M) ≤ moduleDepth R M - 1 := by
  letI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) hx
  -- Rewrite both depths as suprema of regular-sequence lengths and prepend `x`.
  have hquot_smul :
      maximalIdeal R • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top (R := R) (M := QuotSMulTop x M)
  have hmodule_smul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth R M = n := by
    simpa using hn.symm
  rw [show moduleDepth R (QuotSMulTop x M) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop x M)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop x M)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : IsRegular M ([x] ++ ys) := by
    have hfull : IsRegular M (x :: ys) := by
      exact IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal R := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
    · exact hx
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([x] ++ ys).length : ℕ∞) ≤ moduleDepth R M) := by
    rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hmodule_smul]
    refine le_sSup ?_
    exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([x] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

-- Proof sketch: apply Lemma `10.72.6` to the short exact sequence
-- `0 → M --(x • ·)→ M → QuotSMulTop x M → 0`. The hypothesis `hreg` gives injectivity on the left,
-- `hx` ensures the quotient is still a module over the local ring with respect to the maximal
-- ideal, and comparing with the regular sequence `x` shows the inequalities from Lemma `10.72.6`
-- force the depth to drop by exactly one. Any nontriviality needed in the proof is recovered
-- internally from `hreg`.
/-- Lemma 10.72.7 (1): if `x ∈ 𝔪` is a nonzerodivisor on a finite module `M` over a Noetherian
local ring `R`, then the depth of `M / xM` is the depth of `M` minus `1`. -/
theorem moduleDepth_quotSMulTop_eq_sub_one {x : R}
    (hreg : IsSMulRegular M x) (hx : x ∈ maximalIdeal R) :
    moduleDepth R (QuotSMulTop x M) = moduleDepth R M - 1 := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    letI : Subsingleton (QuotSMulTop x M) := by infer_instance
    -- In the zero-module branch, both depths are `⊤`.
    have hdepth_M : moduleDepth R M = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) M
    have hdepth_quot : moduleDepth R (QuotSMulTop x M) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (R := R) (QuotSMulTop x M)
    simpa [hdepth_M, hdepth_quot]
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    let S := ModuleCat.smulShortComplex (ModuleCat.of R M) x
    let hS : S.ShortExact :=
      IsSMulRegular.smulShortComplex_shortExact (M := ModuleCat.of R M) hreg
    letI : Module.Finite R S.X₁ := by
      change Module.Finite R M
      infer_instance
    letI : Module.Finite R S.X₃ := by
      change Module.Finite R (QuotSMulTop x M)
      infer_instance
    -- Lemma `10.72.6` gives the lower bound, and the regular-sequence argument gives the upper.
    have hlower :
        moduleDepth R (QuotSMulTop x M) ≥ moduleDepth R M - 1 := by
      simpa [S, min_eq_right (tsub_le_self : moduleDepth R M - 1 ≤ moduleDepth R M)] using
        CategoryTheory.ShortComplex.ShortExact.moduleDepth_right_ge_min
          (R := R) (S := S) hS
    have hupper :
        moduleDepth R (QuotSMulTop x M) ≤ moduleDepth R M - 1 :=
      moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal (R := R) (M := M) hx hreg
    exact le_antisymm hupper hlower

end IsSMulRegular

namespace IsRegular

-- Proof sketch: induct on the difference between the current regular sequence length and the
-- depth. If the lengths already agree, take the empty tail. Otherwise, recover internally that
-- the current regular sequence already lies in `maximalIdeal R` using the auxiliary companion
-- `ofList_le_maximalIdeal`, apply part (1) to the quotient by that regular sequence to obtain
-- another nonzerodivisor in the maximal ideal, adjoin it using
-- `isRegular_append_of_isRegular_of_quotient_isRegular`, and continue until the resulting
-- sequence has length equal to the depth.
/-- Lemma 10.72.7 (2): every `M`-regular sequence over a Noetherian local ring extends to an
`M`-regular sequence whose length is the depth of `M`. The maximal-ideal containment of the
extended sequence is recovered from the auxiliary companion
`IsRegular.ofList_le_maximalIdeal`. -/
theorem exists_append_eq_moduleDepth {rs : List R} (hreg : IsRegular M rs) :
    ∃ rs' : List R,
      IsRegular M (rs ++ rs') ∧
        moduleDepth R M = (rs ++ rs').length := by
  induction rs generalizing M with
  | nil =>
      letI : Nontrivial M := hreg.nontrivial
      -- In the empty case, choose a depth-realizing regular sequence.
      have hsmul :
          maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
        maximalIdeal_smul_top_ne_top (R := R) (M := M)
      have hfiniteDepth : moduleDepth R M < ⊤ := by
        simpa [moduleDepth] using
          Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hsmul
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
      have hdepth : moduleDepth R M = n := by
        simpa using hn.symm
      obtain ⟨rs', hreg', -, hlen'⟩ :=
        exists_regularSequence_of_length_eq_moduleDepth (R := R) (M := M) (n := n) hdepth
      refine ⟨rs', ?_, ?_⟩
      · simpa using hreg'
      · rw [hdepth]
        exact_mod_cast hlen'.symm
  | cons x xs ih =>
      -- Peel off the head element and recurse on the regular tail over the quotient.
      have hx : x ∈ maximalIdeal R := by
        by_contra hx_not_mem
        change x ∉ maximalIdeal R at hx_not_mem
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx_not_mem
        have hx_unit : IsUnit x := by
          exact not_not.mp hx_not_mem
        have hx_mem : x ∈ Ideal.ofList (x :: xs) := by
          exact Ideal.subset_span (by simp)
        have htop : Ideal.ofList (x :: xs) = ⊤ :=
          Ideal.eq_top_of_isUnit_mem (Ideal.ofList (x :: xs)) hx_mem hx_unit
        have hsmul : Ideal.ofList (x :: xs) • (⊤ : Submodule R M) = ⊤ := by
          simpa [htop]
        exact hreg.top_ne_smul hsmul.symm
      rcases (isRegular_cons_iff (M := M) x xs).1 hreg with ⟨hxreg, hxsreg⟩
      letI : Nontrivial (QuotSMulTop x M) := hxsreg.nontrivial
      obtain ⟨ys, htail_reg, htail_depth⟩ := ih (M := QuotSMulTop x M) hxsreg
      refine ⟨ys, ?_, ?_⟩
      · have hfull : IsRegular M (x :: (xs ++ ys)) := by
          exact IsRegular.cons hxreg htail_reg
        simpa [List.cons_append] using hfull
      · letI : Nontrivial M := hreg.nontrivial
        have hone : (1 : ℕ∞) ≤ moduleDepth R M :=
          one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular (R := R) (M := M) hx hxreg
        calc
          moduleDepth R M = moduleDepth R (QuotSMulTop x M) + 1 := by
            rw [IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := R) (M := M) hxreg hx]
            exact (tsub_add_cancel_of_le hone).symm
          _ = ((xs ++ ys).length : ℕ∞) + 1 := by
            rw [htail_depth]
          _ = (((x :: xs) ++ ys).length : ℕ∞) := by
            simp [List.cons_append]

-- Proof sketch: if `x ∈ rs` and `x ∉ maximalIdeal R`, then `x` generates the unit ideal, so
-- `Ideal.ofList rs = ⊤`. This contradicts the `top_ne_smul` field of `hreg`. Applying this to
-- every term of `rs` shows `Ideal.ofList rs ≤ maximalIdeal R`.
/-- Auxiliary companion: every `M`-regular sequence over a local ring is contained in
`maximalIdeal R`. -/
theorem ofList_le_maximalIdeal {rs : List R} (hreg : IsRegular M rs) :
    Ideal.ofList rs ≤ maximalIdeal R := by
  refine Ideal.span_le.mpr ?_
  intro x hx
  -- An element of a regular sequence outside `𝔪` would be a unit, forcing the unit ideal.
  by_contra hx_not_mem
  change x ∉ maximalIdeal R at hx_not_mem
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx_not_mem
  have hx_unit : IsUnit x := by
    exact not_not.mp hx_not_mem
  have hx_mem : x ∈ Ideal.ofList rs := by
    exact Ideal.subset_span hx
  have htop : Ideal.ofList rs = ⊤ :=
    Ideal.eq_top_of_isUnit_mem (Ideal.ofList rs) hx_mem hx_unit
  have hsmul : Ideal.ofList rs • (⊤ : Submodule R M) = ⊤ := by
    simpa [htop]
  exact hreg.top_ne_smul hsmul.symm

end IsRegular

end

/-! ### Lemma_10_72_8 (from Chap10) -/
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

/-! ### Lemma_10_72_9 (from Chap10) -/
universe u v

open IsLocalRing
open RingTheory.Sequence
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.72.9: an associated prime can occur only for a nonzero module. -/
private theorem nontrivial_of_mem_associatedPrimes {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    Nontrivial M := by
  -- A subsingleton module has no associated primes, so `hp` forces `M` to be nontrivial.
  by_contra hM
  letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
  have hempty : associatedPrimes R M = ∅ := associatedPrimes.eq_empty_of_subsingleton
  simpa [hempty] using hp

/-- Helper for Lemma 10.72.9: a nonzero finite module is not equal to its maximal-ideal multiple. -/
private lemma maximalIdeal_smul_top_ne_top_for_target [Nontrivial M] :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  -- Nakayama rules out `𝔪M = M` for a nonzero finite module over a local ring.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M)))

/-- Helper for Lemma 10.72.9: for a nonzero finite module, depth zero is equivalent to the absence
of a maximal-ideal regular element. -/
private lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_target [Nontrivial M] :
    moduleDepth R M = 0 ↔ ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  have hsmul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_target (R := R) (M := M)
  -- Rewrite depth as the supremum of regular-sequence lengths and test whether length one occurs.
  rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((isWeaklyRegular_singleton_iff M x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal R := by
            exact hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular M x :=
            ((isRegular_cons_iff (M := M) x xs).1 hreg).1
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.72.9: a module with an associated prime has finite local depth. -/
private lemma moduleDepth_lt_top_of_mem_associatedPrimes {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    moduleDepth R M < ⊤ := by
  letI : Nontrivial M := nontrivial_of_mem_associatedPrimes (R := R) (M := M) hp
  have hdepth_le :
      WithBot.some (moduleDepth R M : ℕ∞) ≤ Module.supportDim R M :=
    depth_le_supportDim (R := R) (M := M)
  have hsupport_ne_top : Module.supportDim R M ≠ ⊤ := by
    have hann_ne_top : Module.annihilator R M ≠ ⊤ := by
      intro hann_top
      have hsub : Subsingleton M := (Module.annihilator_eq_top_iff).1 hann_top
      exact (not_nontrivial_iff_subsingleton.mpr hsub) inferInstance
    letI : Nontrivial (R ⧸ Module.annihilator R M) :=
      Ideal.Quotient.nontrivial_iff.mpr hann_ne_top
    letI : IsLocalRing (R ⧸ Module.annihilator R M) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Module.annihilator R M))
        Ideal.Quotient.mk_surjective
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator (R := R) (M := M)]
    exact ringKrullDim_ne_top
  have hdepth_ne_top : moduleDepth R M ≠ ⊤ := by
    intro htop
    have : (⊤ : WithBot ℕ∞) ≤ Module.supportDim R M := by
      simpa [htop] using hdepth_le
    exact hsupport_ne_top (top_unique this)
  exact hdepth_ne_top.lt_top

/-- Helper for Lemma 10.72.9: if the maximal ideal is associated to `M`, then `M` has depth
zero. -/
private lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes [Nontrivial M]
    (hmax : maximalIdeal R ∈ associatedPrimes R M) :
    moduleDepth R M = 0 := by
  have hno : ¬ ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
    rintro ⟨x, hx, hxreg⟩
    have hx_not_mem_union : x ∉ ⋃ q ∈ associatedPrimes R M, (q : Set R) := by
      simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hxreg
    exact hx_not_mem_union <|
      Set.mem_iUnion.2 ⟨maximalIdeal R, Set.mem_iUnion.2 ⟨hmax, hx⟩⟩
  exact (moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_target (R := R) (M := M)).2 hno

/-- Helper for Lemma 10.72.9: positive depth produces a maximal-ideal nonzerodivisor. -/
private lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_target
    [Nontrivial M]
    (hdepth : moduleDepth R M ≠ 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hno
  exact hdepth
    ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_target (R := R) (M := M)).2 hno)

namespace IsSMulRegular

/-- Helper for Lemma 10.72.9: a regular element avoids every associated prime. -/
private lemma not_mem_associatedPrime {p : Ideal R} {x : R}
    (hreg : IsSMulRegular M x) (hp : p ∈ associatedPrimes R M) :
    x ∉ p := by
  -- Regularity says `x` avoids the union of associated primes, so in particular it avoids `p`.
  have hx_not_mem_union : x ∉ ⋃ q ∈ associatedPrimes R M, (q : Set R) := by
    simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hreg
  intro hx
  exact hx_not_mem_union <|
    Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hx⟩⟩

/-- Helper for Lemma 10.72.9: quotienting by a regular maximal-ideal element lowers depth by at
most one. -/
private lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal_for_target [Nontrivial M]
    {a : R} (ha : a ∈ maximalIdeal R) (hreg : IsSMulRegular M a) :
    moduleDepth R (QuotSMulTop a M) ≤ moduleDepth R M - 1 := by
  letI : Nontrivial (QuotSMulTop a M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := M) ha
  -- Rewrite both depths as suprema of regular-sequence lengths and prepend `a`.
  have hquot_smul :
      maximalIdeal R • (⊤ : Submodule R (QuotSMulTop a M)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top_for_target (R := R) (M := QuotSMulTop a M)
  have hmodule_smul :
      maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_target (R := R) (M := M)
  have hfiniteDepth : moduleDepth R M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := R) (I := maximalIdeal R) (M := M) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth R M = n := by
    simpa using hn.symm
  rw [show moduleDepth R (QuotSMulTop a M) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal R) (QuotSMulTop a M)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) (QuotSMulTop a M)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : IsRegular M ([a] ++ ys) := by
    have hfull : IsRegular M (a :: ys) := by
      exact IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([a] ++ ys) ≤ maximalIdeal R := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = a ∨ r ∈ ys) with rfl | hyr
    · exact ha
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([a] ++ ys).length : ℕ∞) ≤ moduleDepth R M) := by
    rw [show moduleDepth R M = sSup (Ideal.regularSequenceLengths (maximalIdeal R) M) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal R) M hmodule_smul]
    refine le_sSup ?_
    exact ⟨[a] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([a] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

end IsSMulRegular

/-- Helper for Lemma 10.72.9: after passing to `R / p`, quotienting by any ideal containing the
image of a regular element lowers Krull dimension by at most one. -/
private lemma ringKrullDim_quotient_succ_le_of_sup_le {p q : Ideal R} {x : R}
    (hx : x ∈ maximalIdeal R) (hp : p ∈ associatedPrimes R M)
    (hreg : IsSMulRegular M x) (hq : p ⊔ Ideal.span {x} ≤ q) :
    ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) := by
  letI : p.IsPrime := (AssociatedPrimes.mem_iff.mp hp).isPrime
  letI : Nontrivial (R ⧸ p) :=
    Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp).isPrime.ne_top
  letI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let xbar : R ⧸ p := Ideal.Quotient.mk p x
  have hxbar_ne_zero : xbar ≠ 0 := by
    -- Route correction: instead of unfolding zero divisors in `R / p`, first exclude `x` from
    -- `p` using associated primes and then read off that its class is nonzero.
    have hx_not_mem_p : x ∉ p :=
      IsSMulRegular.not_mem_associatedPrime (R := R) (M := M) hreg hp
    simpa [xbar, Ideal.Quotient.eq_zero_iff_mem] using hx_not_mem_p
  have hxbar_mem_max :
      xbar ∈ maximalIdeal (R ⧸ p) := by
    have hmap :
        Ideal.map (Ideal.Quotient.mk p) (maximalIdeal R) =
          maximalIdeal (R ⧸ p) := by
      exact IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective
    have hxbar_mem_map :
        xbar ∈ Ideal.map (Ideal.Quotient.mk p) (maximalIdeal R) :=
      Ideal.mem_map_of_mem (Ideal.Quotient.mk p) hx
    rw [hmap] at hxbar_mem_map
    exact hxbar_mem_map
  have hxbar_mem_nonZeroDivisors :
      xbar ∈ nonZeroDivisors (R ⧸ p) :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hxbar_ne_zero
  have hdrop :
      ringKrullDim ((R ⧸ p) ⧸ Ideal.span ({xbar} : Set (R ⧸ p))) + 1 =
        ringKrullDim (R ⧸ p) := by
    simpa [xbar] using
      (ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (R := R ⧸ p) hxbar_mem_nonZeroDivisors hxbar_mem_max)
  have hp_le_q : p ≤ q := (sup_le_iff.mp hq).1
  have hx_mem_q : x ∈ q := by
    exact hq (Ideal.mem_sup_right <| Ideal.subset_span (by simp))
  have hspan_le_qmap :
      Ideal.span ({xbar} : Set (R ⧸ p)) ≤ Ideal.map (Ideal.Quotient.mk p) q := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk p) hx_mem_q
  have hquot_le :
      ringKrullDim ((R ⧸ p) ⧸ Ideal.map (Ideal.Quotient.mk p) q) ≤
        ringKrullDim ((R ⧸ p) ⧸ Ideal.span ({xbar} : Set (R ⧸ p))) := by
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hspan_le_qmap)
      (Ideal.Quotient.factor_surjective hspan_le_qmap)
  have hthird :
      ringKrullDim ((R ⧸ p) ⧸ Ideal.map (Ideal.Quotient.mk p) q) =
        ringKrullDim (R ⧸ q) := by
    exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hp_le_q)
  -- Compare the further quotient with the one-step quotient by the image of `xbar`.
  calc
    ringKrullDim (R ⧸ q) + 1
        = ringKrullDim ((R ⧸ p) ⧸ Ideal.map (Ideal.Quotient.mk p) q) + 1 := by
            rw [← hthird]
    _ ≤ ringKrullDim ((R ⧸ p) ⧸ Ideal.span ({xbar} : Set (R ⧸ p))) + 1 := by
          simpa [add_comm] using add_le_add_right hquot_le 1
        _ = ringKrullDim (R ⧸ p) := hdrop

/-- Helper for Lemma 10.72.9: quotienting by a positive power of a maximal-ideal nonzerodivisor
lowers depth by at least one. -/
private lemma moduleDepth_quotSMulTop_pow_ge_sub_one [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) {m : ℕ} (hm_pos : 0 < m) :
    moduleDepth R M - 1 ≤ moduleDepth R (QuotSMulTop (x ^ m) M) := by
  -- Route correction: the induction only needs the lower bound coming from the short exact
  -- sequence `0 → M --(x^m)→ M → M / x^m M → 0`, so we pivot away from the exact-equality route.
  have hxpow : x ^ m ∈ maximalIdeal R :=
    (maximalIdeal R).pow_mem_of_mem hx m hm_pos
  have hpow_reg : IsSMulRegular M (x ^ m) :=
    hreg.pow m
  -- TODO: prove the split-universe lower bound by rebuilding only the `moduleDepth_right_ge_min`
  -- slice for `ModuleCat.{v} R` and applying it to the smul short exact sequence for `x ^ m`.
  sorry

/-- Helper for Lemma 10.72.9: if `n` is at most the depth of `M`, then every associated prime of
`M` has quotient dimension at least `n`. -/
private theorem ringKrullDim_quotient_ge_of_moduleDepth_ge_nat (n : ℕ) :
    ∀ {N : Type v} [AddCommGroup N] [Module R N] [Module.Finite R N] {p : Ideal R},
      p ∈ associatedPrimes R N → (.some n : ℕ∞) ≤ moduleDepth R N →
        .some n ≤ ringKrullDim (R ⧸ p) := by
  induction n with
  | zero =>
      intro N _ _ _ p hp hdepth
      letI : p.IsPrime := (AssociatedPrimes.mem_iff.mp hp).isPrime
      letI : Nontrivial (R ⧸ p) :=
        Ideal.Quotient.nontrivial_iff.mpr (AssociatedPrimes.mem_iff.mp hp).isPrime.ne_top
      -- In depth `0`, the nonnegativity of Krull dimension closes the goal immediately.
      simpa using (ringKrullDim_nonneg_of_nontrivial (R := R ⧸ p))
  | succ n ih =>
      intro N _ _ _ p hp hdepth
      letI : Nontrivial N := nontrivial_of_mem_associatedPrimes (R := R) (M := N) hp
      obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp <|
        ne_of_lt (moduleDepth_lt_top_of_mem_associatedPrimes (R := R) (M := N) hp)
      have hdepth_nat : n + 1 ≤ d := by
        rw [← hd] at hdepth
        have hdepth_enat : ((n + 1 : ℕ) : ℕ∞) ≤ (d : ℕ∞) := by
          simpa using hdepth
        exact_mod_cast hdepth_enat
      have hone_nat : 1 ≤ d := by
        omega
      have hone : (1 : ℕ∞) ≤ moduleDepth R N := by
        rw [← hd]
        exact_mod_cast hone_nat
      have hdepth_ne_zero : moduleDepth R N ≠ 0 := by
        rw [← hd]
        exact_mod_cast (Nat.ne_of_gt hone_nat)
      -- Choose a maximal-ideal nonzerodivisor and pass the associated prime to a quotient.
      obtain ⟨x, hx, hreg⟩ :=
        exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_target
          (R := R) (M := N) hdepth_ne_zero
      letI : p.IsPrime := (AssociatedPrimes.mem_iff.mp hp).isPrime
      have hsup_le_max : p ⊔ Ideal.span {x} ≤ maximalIdeal R := by
        rw [sup_le_iff]
        exact ⟨IsLocalRing.le_maximalIdeal_of_isPrime p,
          (Ideal.span_singleton_le_iff_mem (I := maximalIdeal R) (x := x)).2 hx⟩
      obtain ⟨q, hq, _⟩ := Ideal.exists_minimalPrimes_le (J := maximalIdeal R) hsup_le_max
      obtain ⟨m, hm_pos, hq_assoc⟩ :=
        exists_mem_associatedPrimes_quotient_span_singleton_pow_of_mem_minimalPrimes_sup
          (R := R) (M := N) x p q hp hq
      have hdepth_quot :
          (.some n : ℕ∞) ≤ moduleDepth R (QuotSMulTop (x ^ m) N) := by
        -- TODO: combine the finite-depth predecessor inequality `n ≤ d - 1` coming from
        -- `hdepth_nat : n + 1 ≤ d` with the source-faithful lower bound
        -- `moduleDepth_quotSMulTop_pow_ge_sub_one` to obtain
        -- `n ≤ depth (N / x^m N)` in `ℕ∞`.
        sorry
      have hih :
          .some n ≤ ringKrullDim (R ⧸ q) :=
        ih (N := QuotSMulTop (x ^ m) N) (p := q) hq_assoc hdepth_quot
      have hstep :
          ringKrullDim (R ⧸ q) + 1 ≤ ringKrullDim (R ⧸ p) :=
        ringKrullDim_quotient_succ_le_of_sup_le (R := R) (M := N) hx hp hreg hq.1.2
      -- Add the induction inequality to the one-step dimension comparison.
      calc
        .some (n + 1) = (.some n : WithBot ℕ∞) + 1 := by simp
        _ ≤ ringKrullDim (R ⧸ q) + 1 := by
          simpa [add_comm] using add_le_add_right hih 1
        _ ≤ ringKrullDim (R ⧸ p) := hstep

/- Domain-style sampling:
* primary domain: depth and associated primes for finite modules over Noetherian local rings;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `associatedPrimes R M`,
  `ringKrullDim (R ⧸ p)`,
  `depth_le_supportDim`;
* best owner abstraction: the local depth owner is the chapter bridge `moduleDepth R M`, while
  associated primes and quotient dimensions are already carried by the mathlib owners
  `associatedPrimes` and `ringKrullDim`;
* source/core/bridge triage:
  `source-facing`: the lower bound on `ringKrullDim (R ⧸ p)` for `p ∈ associatedPrimes R M`;
  `core/canonical`: `moduleDepth`, `associatedPrimes`, and `ringKrullDim`;
  `bridge/view`: the quotient ring `R ⧸ p`.

Primitive data are only the local ring, the finite module, and the associated prime `p`. The
local specialization of depth is derived API from the owner bridge `moduleDepth`, so the theorem
surface should use that bridge rather than restating `Ideal.depth (maximalIdeal R) M`.
-/
-- Proof sketch: induct on `moduleDepth R M`. If the maximal ideal is associated,
-- the depth is `0`. Otherwise choose a nonzerodivisor `x ∈ maximalIdeal R`, note that
-- `x ∉ p` for `p ∈ associatedPrimes R M`, and use the one-step dimension drop for
-- `(R ⧸ p) ⧸ (x)` together with Lemmas `10.72.8` and `10.72.7` to pass to an associated prime of
-- `M / x^n M`, whose depth is one smaller.
/-- Lemma 10.72.9: if `(R, 𝔪)` is a local Noetherian ring, `M` is a finite `R`-module, and
`p ∈ Ass(M)`, then the Krull dimension of `R / p`, written canonically as `ringKrullDim (R ⧸ p)`,
is at least the local depth `moduleDepth R M` of `M`. Since `ringKrullDim` takes values in
`WithBot ℕ∞`, the depth is viewed in the same codomain via the canonical coercions
`WithTop ℕ = ℕ∞ → WithBot ℕ∞`. -/
theorem moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (p : Ideal R)
    (hp : p ∈ associatedPrimes R M) :
    .some (moduleDepth R M) ≤ ringKrullDim (R ⧸ p) := by
  -- First rewrite the depth as a finite natural number using the associated-prime hypothesis.
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp <|
    ne_of_lt (moduleDepth_lt_top_of_mem_associatedPrimes (R := R) (M := M) hp)
  -- The auxiliary induction only needs the tautological inequality `n ≤ depth(M)`.
  have hdepth_ge : (.some n : ℕ∞) ≤ moduleDepth R M := by
    rw [← hn]
    exact le_rfl
  simpa [hn] using
    ringKrullDim_quotient_ge_of_moduleDepth_ge_nat (R := R) n (N := M) (p := p) hp hdepth_ge

end

/-! ### Lemma_10_72_10 (from Chap10) -/
open scoped ENat
open IsLocalRing
open RingTheory.Sequence

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable (p : Ideal R) [p.IsPrime]

local notation "Rₚ" => Localization.AtPrime p
local notation "Mₚ" => LocalizedModule.AtPrime p M

/- Domain-style sampling:
* primary domain: depth for finite modules over Noetherian local rings and its behavior under
  localization at a prime;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Localization.AtPrime`,
  `LocalizedModule.AtPrime`,
  `moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes`;
* best owner abstraction: the chapter owner surface for local depth is `moduleDepth`, while the
  localized ring/module are the canonical owner constructions `Localization.AtPrime` and
  `LocalizedModule.AtPrime`;
* source/core/bridge triage:
  `source-facing`: the depth inequality relating `M`, `Mₚ`, and `R / p`;
  `core/canonical`: `moduleDepth` together with the owner localization objects `Rₚ` and `Mₚ`;
  `bridge/view`: the quotient ring `R ⧸ p`.

Primitive data are only the local ring, the finite module, and the prime ideal. The localized ring
and module are derived from the owner localization constructions, so the public theorem surface
should name those owner objects directly instead of repeating the full expressions inline.
-/

/-- Helper for Lemma 10.72.10: a finite subsingleton module over a Noetherian local ring has
infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Subsingleton N] :
    moduleDepth A N = ⊤ := by
  -- A subsingleton module already satisfies `𝔪N = N`, so the depth is infinite by definition.
  have htop_eq_bot : (⊤ : Submodule A N) = ⊥ := by
    ext n
    simp [Subsingleton.elim n 0]
  have hsmul_bot : maximalIdeal A • (⊥ : Submodule A N) = ⊥ := by
    ext n
    simp
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A N) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal A) N = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal A) N hsmul_top

/-- Helper for Lemma 10.72.10: the maximal ideal of a Noetherian local ring cannot generate a
nonzero finite module. -/
private theorem maximalIdeal_smul_top_ne_top_for_entry
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] :
    maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ := by
  -- This is the Jacobson-ideal form of Nakayama's lemma.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator A N)))

/-- Helper for Lemma 10.72.10: a regular element in the maximal ideal forces positive depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {N : Type*} [AddCommGroup N] [Module A N] [Module.Finite A N] [Nontrivial N] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular N x) :
    (1 : ℕ∞) ≤ moduleDepth A N := by
  -- The singleton regular sequence `[x]` already contributes one to the depth.
  have hsingleton_reg : IsRegular N [x] := by
    exact IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal N
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((isWeaklyRegular_singleton_iff N x).2 hreg)
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal A := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A N) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry
  rw [show moduleDepth A N = sSup (Ideal.regularSequenceLengths (maximalIdeal A) N) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) N hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Helper for Lemma 10.72.10: linear equivalences preserve the set of regular-sequence
lengths. -/
private theorem regularSequenceLengths_eq_of_linearEquiv
    {A : Type*} [CommRing A] (I : Ideal A)
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    Ideal.regularSequenceLengths I N₁ = Ideal.regularSequenceLengths I N₂ := by
  -- Transport each witness sequence across the linear equivalence.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.72.10: linear equivalences preserve ideal depth. -/
private theorem idealDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] (I : Ideal A)
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    Ideal.depth I N₁ = Ideal.depth I N₂ := by
  -- Compare the two presentations of depth depending on whether `IN = N`.
  have htop :
      I • (⊤ : Submodule A N₁) = ⊤ ↔ I • (⊤ : Submodule A N₂) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hN₁ : I • (⊤ : Submodule A N₁) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I N₁ hN₁,
      Ideal.depth_eq_top_of_smul_top I N₂ (htop.mp hN₁)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₁ hN₁,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₂ (mt htop.mpr hN₁),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Lemma 10.72.10: linear equivalences preserve module depth over a local ring. -/
private theorem moduleDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    moduleDepth A N₁ = moduleDepth A N₂ :=
  idealDepth_eq_of_linearEquiv (maximalIdeal A) e

/-- Helper for Lemma 10.72.10: the quotient by a prime ideal has nonnegative Krull dimension. -/
private lemma zero_le_ringKrullDim_quotient :
    (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) := by
  -- Prime quotients are nontrivial rings, so their Krull dimension is nonnegative.
  letI : Nontrivial (R ⧸ p) := (Ideal.Quotient.nontrivial_iff).2 (Ideal.IsPrime.ne_top inferInstance)
  exact ringKrullDim_nonneg_of_nontrivial

/-- Helper for Lemma 10.72.10: if `depth(M)` is larger than `dim(R / p)`, then no associated
prime of `M` lies above `p`. -/
private lemma associated_prime_not_above_of_ringKrullDim_quotient_lt_moduleDepth
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (hlt : ringKrullDim (R ⧸ p) < (.some (moduleDepth R N) : WithBot ℕ∞)) :
    ∀ {q : Ideal R}, q ∈ associatedPrimes R N → ¬ p ≤ q := by
  intro q hq hpq
  -- Compare `R / q` with `R / p` through the canonical quotient map.
  have hdepth_le :
      (.some (moduleDepth R N) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) :=
    moduleDepth_le_ringKrullDim_quotient_of_mem_associatedPrimes (R := R) (M := N) q hq
  have hdim_le :
      ringKrullDim (R ⧸ q) ≤ ringKrullDim (R ⧸ p) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hpq)
      (Ideal.Quotient.factor_surjective hpq)
  exact not_lt_of_ge (le_trans hdepth_le hdim_le) hlt

/-- Helper for Lemma 10.72.10: a regular element remains regular after localizing at the same
prime. -/
private theorem localizedModule_atPrime_isSMulRegular_of_isSMulRegular
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Nontrivial (LocalizedModule.AtPrime p N)] {x : R}
    (hx : x ∈ p) (hreg : IsSMulRegular N x) :
    IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) := by
  -- Localize the singleton regular sequence `[x]` inside the maximal ideal of `Rₚ`.
  have hmem : ∀ r ∈ [x], r ∈ p := by
    intro r hr
    simpa [List.mem_singleton.mp hr] using hx
  have hreg_loc :
      IsRegular (LocalizedModule.AtPrime p N) [algebraMap R (Localization.AtPrime p) x] := by
    simpa using
      ((isWeaklyRegular_singleton_iff N x).2 hreg).isRegular_of_isLocalizedModule_of_mem
        (S := Localization.AtPrime p)
        (p := p)
        (N := LocalizedModule.AtPrime p N)
        (f := LocalizedModule.mkLinearMap p.primeCompl N)
        hmem
  exact
    ((isRegular_cons_iff
      (M := LocalizedModule.AtPrime p N)
      (algebraMap R (Localization.AtPrime p) x) []).1
      (by simpa using hreg_loc)).1

/-- Helper for Lemma 10.72.10: localizing the quotient by `x` agrees with quotienting the
localized module by the image of `x`. -/
private noncomputable def localizedModule_atPrime_quotSMulTop_equiv
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] (x : R) :
    LocalizedModule.AtPrime p (QuotSMulTop x N) ≃ₗ[Localization.AtPrime p]
      QuotSMulTop (algebraMap R (Localization.AtPrime p) x) (LocalizedModule.AtPrime p N) :=
  let e₁ := LocalizedModule.equivTensorProduct (R := R) p.primeCompl (QuotSMulTop x N)
  let e₂ := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
    (R := R) (r := x) (M := N) (Localization.AtPrime p)).symm
  let e₃ := QuotSMulTop.congr (algebraMap R (Localization.AtPrime p) x)
    (LocalizedModule.equivTensorProduct (R := R) p.primeCompl N).symm
  e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 10.72.10: after localizing at `p`, quotienting by a `p`-regular element
lowers the localized depth by one. -/
private theorem moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
    {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] {x : R}
    (hx : x ∈ p) (hreg : IsSMulRegular N x) :
    moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) =
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 := by
  -- First transport the localized quotient to the canonical quotient of the localized module.
  let e := localizedModule_atPrime_quotSMulTop_equiv (R := R) (p := p) (N := N) x
  have hx_loc :
      algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p x).2 hx
  by_cases hsub : Subsingleton (LocalizedModule.AtPrime p N)
  · letI : Subsingleton (LocalizedModule.AtPrime p N) := hsub
    -- In the zero-localization case both localized depths are infinite.
    have hdepth_local :
        moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton
    have hdepth_quot :
        moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) = ⊤ := by
      letI :
          Subsingleton
            (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
              (LocalizedModule.AtPrime p N)) := by
        infer_instance
      letI : Subsingleton (LocalizedModule.AtPrime p (QuotSMulTop x N)) := by
        exact e.injective.subsingleton
      exact moduleDepth_eq_top_of_subsingleton
    simpa [hdepth_local, hdepth_quot]
  · letI : Nontrivial (LocalizedModule.AtPrime p N) := not_subsingleton_iff_nontrivial.mp hsub
    have hreg_loc :
        IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) :=
      localizedModule_atPrime_isSMulRegular_of_isSMulRegular
        (R := R) (p := p) (N := N) hx hreg
    calc
      moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N))
          =
            moduleDepth (Localization.AtPrime p)
              (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
                (LocalizedModule.AtPrime p N)) := by
              simpa using
                moduleDepth_eq_of_linearEquiv
                  (A := Localization.AtPrime p) e
      _ =
          moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 := by
            exact IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one
              (R := Localization.AtPrime p)
              (M := LocalizedModule.AtPrime p N)
              hreg_loc
              hx_loc

/-- Helper for Lemma 10.72.10: once the global depth is the natural number `n`, the source-faithful
induction on `n` proves the localized depth inequality at the fixed prime `p`. -/
private theorem
    moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_of_moduleDepth_eq_nat
    (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N]
      [Nontrivial N] [Nontrivial (LocalizedModule.AtPrime p N)],
        moduleDepth R N = n →
          .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
              ringKrullDim (R ⧸ p) ≥
            (.some n : WithBot ℕ∞) := by
  induction n with
  | zero =>
      intro N _ _ _ _ _ hdepth
      -- In depth `0`, nonnegativity of both summands gives the claim immediately.
      have hlocal_nonneg :
          (0 : WithBot ℕ∞) ≤
            (.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) :
              WithBot ℕ∞) := by
        simp
      have hsum_nonneg :
          (0 : WithBot ℕ∞) ≤
            .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
              ringKrullDim (R ⧸ p) := by
        calc
          (0 : WithBot ℕ∞) = (0 : WithBot ℕ∞) + 0 := by simp
          _ ≤
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
                  exact add_le_add hlocal_nonneg (zero_le_ringKrullDim_quotient (R := R) (p := p))
      simpa [hdepth] using hsum_nonneg
  | succ n ih =>
      intro N _ _ _ _ _ hdepth
      by_cases hdim :
          (.some (n + 1 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p)
      · -- If the quotient dimension is already large enough, the localized depth term is extra slack.
        have hlocal_nonneg :
            (0 : WithBot ℕ∞) ≤
              (.some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) :
                WithBot ℕ∞) := by
          simp
        have hdim_le :
            ringKrullDim (R ⧸ p) ≤
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
          simpa [zero_add, add_comm] using
            add_le_add_left hlocal_nonneg (ringKrullDim (R ⧸ p))
        exact le_trans hdim hdim_le
      · -- Route correction: keep the same prime `p` and pass from `N` to `N / xN`.
        have hlt :
            ringKrullDim (R ⧸ p) <
              (.some (moduleDepth R N) : WithBot ℕ∞) := by
          rw [hdepth]
          exact lt_of_not_ge hdim
        have hforall :
            ∀ q ∈ associatedPrimes R N, ¬ p ≤ q :=
          by
            intro q hq
            exact associated_prime_not_above_of_ringKrullDim_quotient_lt_moduleDepth
              (R := R) (p := p) hlt hq
        obtain ⟨x, hx, hreg⟩ :=
          (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
            (R := R) (M := N) (I := p)).2 hforall
        have hx_max : x ∈ maximalIdeal R := by
          exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hx
        letI : Nontrivial (QuotSMulTop x N) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal (R := R) (L := N) hx_max
        have hx_loc :
            algebraMap R (Localization.AtPrime p) x ∈ maximalIdeal (Localization.AtPrime p) := by
          exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
            (Localization.AtPrime p) p x).2 hx
        have hreg_loc :
            IsSMulRegular (LocalizedModule.AtPrime p N) (algebraMap R (Localization.AtPrime p) x) :=
          localizedModule_atPrime_isSMulRegular_of_isSMulRegular
            (R := R) (p := p) (N := N) hx hreg
        letI :
            Nontrivial
              (QuotSMulTop (algebraMap R (Localization.AtPrime p) x)
                (LocalizedModule.AtPrime p N)) :=
          nontrivial_quotSMulTop_of_mem_maximalIdeal
            (R := Localization.AtPrime p)
            (L := LocalizedModule.AtPrime p N)
            hx_loc
        let e := localizedModule_atPrime_quotSMulTop_equiv (R := R) (p := p) (N := N) x
        letI : Nontrivial (LocalizedModule.AtPrime p (QuotSMulTop x N)) := e.nontrivial
        have hdepth_quot :
            moduleDepth R (QuotSMulTop x N) = n := by
          calc
            moduleDepth R (QuotSMulTop x N) = moduleDepth R N - 1 := by
              exact IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one
                (R := R) (M := N) hreg hx_max
            _ = n := by
              rw [hdepth]
              simpa using
                (tsub_add_cancel_of_le (show (1 : ℕ∞) ≤ (n : ℕ∞) + 1 by simp))
        have hih :
            .some (moduleDepth (Localization.AtPrime p)
                (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                ringKrullDim (R ⧸ p) ≥
              (.some n : WithBot ℕ∞) :=
          ih hdepth_quot
        have hlocal_drop :
            moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p (QuotSMulTop x N)) =
              moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) - 1 :=
          moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
            (R := R) (p := p) (N := N) hx hreg
        have hone :
            (1 : ℕ∞) ≤
              moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) :=
          one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
            (A := Localization.AtPrime p)
            (N := LocalizedModule.AtPrime p N)
            hx_loc
            hreg_loc
        have hlocal_succ :
            moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N) =
              moduleDepth (Localization.AtPrime p)
                (LocalizedModule.AtPrime p (QuotSMulTop x N)) + 1 := by
          rw [hlocal_drop]
          exact (tsub_add_cancel_of_le hone).symm
        -- Add back the one-step depth drop on the localized side.
        calc
          (.some (n + 1 : ℕ∞) : WithBot ℕ∞)
              = (.some n : WithBot ℕ∞) + 1 := by
                  simp
          _ ≤
              (.some (moduleDepth (Localization.AtPrime p)
                  (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                    ringKrullDim (R ⧸ p)) + 1 := by
                      have hih_add :
                          1 + (.some n : WithBot ℕ∞) ≤
                            1 + (.some (moduleDepth (Localization.AtPrime p)
                                (LocalizedModule.AtPrime p (QuotSMulTop x N))) +
                                  ringKrullDim (R ⧸ p)) :=
                        add_le_add_right hih 1
                      simpa [add_assoc, add_left_comm, add_comm] using hih_add
          _ =
              .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p N)) +
                ringKrullDim (R ⧸ p) := by
                  rw [hlocal_succ]
                  simp [add_left_comm, add_comm]

-- Proof sketch: argue by induction on the finite global depth. If `LocalizedModule.AtPrime p M`
-- is zero, its depth is `∞`, so the inequality is immediate. Otherwise the source proof keeps the
-- same prime `p`: if `depth(M) > dim(R / p)`, use Lemma `10.72.9` and prime avoidance to choose a
-- regular element `x ∈ p`, apply Lemma `10.72.7` to both `M` and `Mₚ`, and recurse on `M / xM`.
/-- Lemma 10.72.10: for a prime ideal `p` of a local Noetherian ring `R` and a finite
`R`-module `M`, the local depth `moduleDepth Rₚ Mₚ` of the localization `Mₚ` plus the Krull
dimension of `R / p` is at least the local depth `moduleDepth R M` of `M`. -/
theorem moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_moduleDepth :
    .some (moduleDepth Rₚ Mₚ) + ringKrullDim (R ⧸ p) ≥ .some (moduleDepth R M) := by
  by_cases hMp : Subsingleton Mₚ
  · letI : Subsingleton Mₚ := hMp
    -- If the localization is zero, its depth is infinite and dominates any finite global depth.
    have hdepth_local : moduleDepth Rₚ Mₚ = ⊤ :=
      moduleDepth_eq_top_of_subsingleton
    have htop_le :
        (.some (⊤ : ℕ∞) : WithBot ℕ∞) ≤
          (.some (⊤ : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) := by
      calc
        (.some (⊤ : ℕ∞) : WithBot ℕ∞) = (.some (⊤ : ℕ∞) : WithBot ℕ∞) + 0 := by
          simp
        _ ≤ (.some (⊤ : ℕ∞) : WithBot ℕ∞) + ringKrullDim (R ⧸ p) := by
          exact add_le_add_right (zero_le_ringKrullDim_quotient (R := R) (p := p))
            (.some (⊤ : ℕ∞) : WithBot ℕ∞)
    calc
      (.some (moduleDepth R M) : WithBot ℕ∞) ≤ (.some (⊤ : ℕ∞) : WithBot ℕ∞) := by
        simp
      _ = (.some (moduleDepth Rₚ Mₚ) : WithBot ℕ∞) := by
        rw [hdepth_local]
      _ ≤ .some (moduleDepth Rₚ Mₚ) + ringKrullDim (R ⧸ p) := by
        simpa [hdepth_local] using htop_le
  · letI : Nontrivial Mₚ := not_subsingleton_iff_nontrivial.mp hMp
    have hM_not_subsingleton : ¬ Subsingleton M := by
      intro hM
      letI : Subsingleton M := hM
      letI : Subsingleton Mₚ := by infer_instance
      exact hMp inferInstance
    letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM_not_subsingleton
    -- Once both modules are nonzero, the global depth is finite and the induction helper applies.
    have hfiniteDepth : moduleDepth R M < ⊤ := by
      simpa [moduleDepth] using
        Ideal.depth_lt_top_of_smul_top_ne_top
          (R := R) (I := maximalIdeal R) (M := M)
          (maximalIdeal_smul_top_ne_top_for_entry (A := R) (N := M))
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
    have hdepth : moduleDepth R M = n := by
      simpa using hn.symm
    simpa [hdepth] using
      moduleDepth_localizedModule_atPrime_add_ringKrullDim_quotient_ge_of_moduleDepth_eq_nat
        (R := R) (p := p) n hdepth

end
