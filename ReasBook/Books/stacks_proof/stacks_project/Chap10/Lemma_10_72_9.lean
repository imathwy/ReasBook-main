import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_72_1
import stacks_proof.stacks_project.Chap10.Lemma_10_72_3
import stacks_proof.stacks_project.Chap10.Lemma_10_72_7
import stacks_proof.stacks_project.Chap10.Lemma_10_72_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open IsLocalRing
open RingTheory.Sequence
open scoped ENat

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 72 9: an associated prime can occur only for a nonzero module. -/
private theorem nontrivial_of_mem_associatedPrimes {p : Ideal R}
    (hp : p ∈ associatedPrimes R M) :
    Nontrivial M := by
  -- A subsingleton module has no associated primes, so `hp` forces `M` to be nontrivial.
  by_contra hM
  letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hM
  have hempty : associatedPrimes R M = ∅ := associatedPrimes.eq_empty_of_subsingleton
  simp [hempty] at hp

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 9: a nonzero finite module is not equal to its maximal-ideal
multiple. -/
private lemma maximalIdeal_smul_top_ne_top_for_target [Nontrivial M] :
    maximalIdeal R • (⊤ : Submodule R M) ≠ ⊤ := by
  -- Nakayama rules out `𝔪M = M` for a nonzero finite module over a local ring.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator R M)))

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 9: for a nonzero finite module, depth zero is equivalent to the
absence of a maximal-ideal regular element. -/
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

/-- Helper for Chap10 Lemma 10 72 9: a module with an associated prime has finite local depth. -/
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

/-- Helper for Chap10 Lemma 10 72 9: if the maximal ideal is associated to `M`, then `M` has
depth zero. -/
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

omit [IsNoetherianRing R] in
/-- Helper for Chap10 Lemma 10 72 9: positive depth produces a maximal-ideal nonzerodivisor. -/
private lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_target
    [Nontrivial M]
    (hdepth : moduleDepth R M ≠ 0) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x := by
  by_contra hno
  exact hdepth
    ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_target (R := R) (M := M)).2 hno)

namespace IsSMulRegular

omit [IsLocalRing R] [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 72 9: a regular element avoids every associated prime. -/
private lemma not_mem_associatedPrime {p : Ideal R} {x : R}
    (hreg : IsSMulRegular M x) (hp : p ∈ associatedPrimes R M) :
    x ∉ p := by
  -- Regularity says `x` avoids the union of associated primes, so in particular it avoids `p`.
  have hx_not_mem_union : x ∉ ⋃ q ∈ associatedPrimes R M, (q : Set R) := by
    simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular R M] using hreg
  intro hx
  exact hx_not_mem_union <|
    Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hx⟩⟩

/-- Helper for Chap10 Lemma 10 72 9: quotienting by a regular maximal-ideal element lowers depth
by at most one. -/
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

omit [Module.Finite R M] in
/-- Helper for Chap10 Lemma 10 72 9: after passing to `R / p`, quotienting by any ideal
containing the image of a regular element lowers Krull dimension by at most one. -/
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

/-- Helper for Chap10 Lemma 10 72 9: quotienting by a positive power of a maximal-ideal
nonzerodivisor lowers depth by at least one. -/
private lemma moduleDepth_quotSMulTop_pow_ge_sub_one [Nontrivial M] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) {m : ℕ} (hm_pos : 0 < m) :
    moduleDepth R M - 1 ≤ moduleDepth R (QuotSMulTop (x ^ m) M) := by
  have hpow_reg : IsSMulRegular M (x ^ m) :=
    hreg.pow m
  have hpow_mem : x ^ m ∈ maximalIdeal R :=
    (maximalIdeal R).pow_mem_of_mem hx m hm_pos
  -- Read the depth drop directly from Lemma `10.72.7` specialized to `x ^ m`.
  rw [IsSMulRegular.moduleDepth_quotSMulTop_eq_sub_one (R := R) (M := M) hpow_reg hpow_mem]

/-- Helper for Chap10 Lemma 10 72 9: if `n` is at most the depth of `M`, then every associated
prime of `M` has quotient dimension at least `n`. -/
private theorem ringKrullDim_quotient_ge_of_moduleDepth_ge_nat (n : ℕ) :
    ∀ {N : Type u} [AddCommGroup N] [Module R N] [Module.Finite R N] {p : Ideal R},
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
        have hdepth_pred_nat : n ≤ d - 1 := by
          -- The successor-depth hypothesis over naturals descends to the predecessor.
          omega
        have hdepth_quot_eq :
            moduleDepth R (QuotSMulTop (x ^ m) N) = d - 1 := by
          -- Quotienting by the regular power `x ^ m` drops depth by exactly one.
          calc
            moduleDepth R (QuotSMulTop (x ^ m) N) = moduleDepth R N - 1 := by
              have hxm_mem : x ^ m ∈ maximalIdeal R :=
                (maximalIdeal R).pow_mem_of_mem hx m hm_pos
              exact le_antisymm
                (IsSMulRegular.moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal_for_target
                  (R := R) (M := N) hxm_mem (hreg.pow m))
                (moduleDepth_quotSMulTop_pow_ge_sub_one
                  (R := R) (M := N) hx hreg hm_pos)
            _ = d - 1 := by
              rw [hd]
        -- Rewriting the quotient depth to the natural predecessor makes the cast immediate.
        rw [hdepth_quot_eq]
        exact ENat.coe_le_coe.mpr hdepth_pred_nat
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
/-- Chap10 Lemma 10 72 9: if `(R, 𝔪)` is a local Noetherian ring, `M` is a finite `R`-module,
and `p ∈ Ass(M)`, then the Krull dimension of `R / p`, written canonically as
`ringKrullDim (R ⧸ p)`, is at least the local depth `moduleDepth R M` of `M`. Since
`ringKrullDim` takes values in `WithBot ℕ∞`, the depth is viewed in the same codomain via the
canonical coercions `WithTop ℕ = ℕ∞ → WithBot ℕ∞`. -/
@[stacks 0BK4]
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
