import Mathlib.RingTheory.Regular.RegularSequence
import StacksProject_2024.Chap10.Lemma_10_4_1
import StacksProject_2024.Chap10.Lemma_10_68_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace RingTheory.Sequence

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped Pointwise

/-- Helper for Lemma 10.68.9: higher powers of `r` generate smaller scalar-multiple submodules. -/
private lemma pow_smulTop_le (r : R) {m n : ℕ} (h : m ≤ n) :
    (r ^ n) • (⊤ : Submodule R M) ≤ (r ^ m) • (⊤ : Submodule R M) := by
  intro x hx
  rcases (Submodule.mem_smul_pointwise_iff_exists x (r ^ n)
      (⊤ : Submodule R M)).mp hx with ⟨y, -, rfl⟩
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  -- Rewrite the larger power as an extra factor times the smaller one.
  refine (Submodule.mem_smul_pointwise_iff_exists _ (r ^ m)
      (⊤ : Submodule R M)).2 ?_
  refine ⟨r ^ k • y, trivial, ?_⟩
  rw [pow_add, mul_smul]

/-- Helper for Lemma 10.68.9: multiplication by `r ^ n` descends from `M / rM` to
`M / r^(n + 1)M`. -/
private lemma smulTop_le_comap_powSucc (r : R) (n : ℕ) :
    r • (⊤ : Submodule R M) ≤
      Submodule.comap (LinearMap.lsmul R M (r ^ n))
        ((r ^ (n + 1)) • (⊤ : Submodule R M)) := by
  intro x hx
  rcases (Submodule.mem_smul_pointwise_iff_exists x r
      (⊤ : Submodule R M)).mp hx with ⟨y, -, rfl⟩
  -- One extra factor of `r` lands inside the `(n + 1)`st power quotient.
  change r ^ n • (r • y) ∈ (r ^ (n + 1)) • (⊤ : Submodule R M)
  refine (Submodule.mem_smul_pointwise_iff_exists _ (r ^ (n + 1))
    (⊤ : Submodule R M)).2 ?_
  refine ⟨y, trivial, ?_⟩
  simp [pow_succ', smul_smul, mul_comm]

/-- Helper for Lemma 10.68.9: the left map in the power-quotient short exact sequence. -/
private abbrev powQuotientLeftMap (r : R) (n : ℕ) :
    QuotSMulTop r M →ₗ[R] QuotSMulTop (r ^ (n + 1)) M :=
  Submodule.mapQ
    (r • (⊤ : Submodule R M))
    ((r ^ (n + 1)) • (⊤ : Submodule R M))
    (LinearMap.lsmul R M (r ^ n))
    (smulTop_le_comap_powSucc (M := M) r n)

/-- Helper for Lemma 10.68.9: the right map in the power-quotient short exact sequence. -/
private abbrev powQuotientRightMap (r : R) (n : ℕ) :
    QuotSMulTop (r ^ (n + 1)) M →ₗ[R] QuotSMulTop (r ^ n) M :=
  Submodule.factor (pow_smulTop_le (M := M) r (Nat.le_succ n))

/-- Helper for Lemma 10.68.9: the `(n + 1)`st power quotient surjects onto the first power
quotient. -/
private lemma pow_smulTop_succ_le (r : R) (n : ℕ) :
    (r ^ (n + 1)) • (⊤ : Submodule R M) ≤ r • (⊤ : Submodule R M) := by
  simpa using pow_smulTop_le (M := M) r (show 1 ≤ n + 1 by exact Nat.succ_le_succ (Nat.zero_le n))

/-- Helper for Lemma 10.68.9: if `M = rM`, then iterating the same equality gives
`M = r^(n + 1) M`. -/
private lemma top_eq_pow_smulTop_of_top_eq_smul (r : R) (n : ℕ)
    (htop : (⊤ : Submodule R M) = r • (⊤ : Submodule R M)) :
    (⊤ : Submodule R M) = (r ^ (n + 1)) • (⊤ : Submodule R M) := by
  induction n with
  | zero =>
      simpa using htop
  | succ n ih =>
      have hsmul :
          r • (⊤ : Submodule R M) = r • ((r ^ (n + 1)) • (⊤ : Submodule R M)) :=
        congrArg (fun N : Submodule R M ↦ r • N) ih
      calc
        (⊤ : Submodule R M) = r • (⊤ : Submodule R M) := htop
        _ = r • ((r ^ (n + 1)) • (⊤ : Submodule R M)) := hsmul
        _ = (r ^ (n + 2)) • (⊤ : Submodule R M) := by
              simp [pow_succ, smul_smul, mul_comm]

@[simp]
private lemma powQuotientLeftMap_apply_mk (r : R) (n : ℕ) (x : M) :
    powQuotientLeftMap (M := M) r n (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (r ^ n • x) : QuotSMulTop (r ^ (n + 1)) M) := by
  rfl

@[simp]
private lemma powQuotientRightMap_apply_mk (r : R) (n : ℕ) (x : M) :
    powQuotientRightMap (M := M) r n (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : QuotSMulTop (r ^ n) M) := by
  rfl

/-- Helper for Lemma 10.68.9: the left map between successive power quotients is injective when
`r` is a non-zero-divisor on `M`. -/
private lemma powQuotientLeftMap_injective {r : R} {n : ℕ} (hr : IsSMulRegular M r) :
    Function.Injective (powQuotientLeftMap (M := M) r n) := by
  intro x y hxy
  rcases Submodule.Quotient.mk_surjective (r • (⊤ : Submodule R M)) x with ⟨mx, rfl⟩
  rcases Submodule.Quotient.mk_surjective (r • (⊤ : Submodule R M)) y with ⟨my, rfl⟩
  rw [Submodule.Quotient.eq]
  have hzero :
      powQuotientLeftMap (M := M) r n
          (Submodule.Quotient.mk (mx - my) : QuotSMulTop r M) = 0 := by
    -- Subtract the two representatives to reduce to the kernel of the left map.
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using congrArg (fun z ↦ z - powQuotientLeftMap (M := M) r n
        (Submodule.Quotient.mk my : QuotSMulTop r M)) hxy
  rw [powQuotientLeftMap_apply_mk, Submodule.Quotient.mk_eq_zero] at hzero
  rcases (Submodule.mem_smul_pointwise_iff_exists (r ^ n • (mx - my)) (r ^ (n + 1))
      (⊤ : Submodule R M)).mp hzero with ⟨z, -, hz⟩
  have hcancel :
      mx - my - r • z = 0 := by
    -- Cancel the common factor `r ^ n` using regularity of `r ^ n`.
    have hpow :
        r ^ n • (mx - my - r • z) = 0 := by
      have hz' : r ^ n • (mx - my) = r ^ n • (r • z) := by
        simpa [pow_succ', smul_smul, mul_comm, mul_left_comm, mul_assoc] using hz.symm
      calc
        r ^ n • (mx - my - r • z)
            = r ^ n • (mx - my) - r ^ n • (r • z) := by
                simp [smul_sub]
        _ = 0 := by simpa [hz']
    exact (hr.pow n).right_eq_zero_of_smul hpow
  refine (Submodule.mem_smul_pointwise_iff_exists (mx - my) r
      (⊤ : Submodule R M)).2 ?_
  refine ⟨z, trivial, ?_⟩
  exact (sub_eq_zero.mp hcancel).symm

/-- Helper for Lemma 10.68.9: the successive power quotients form an exact sequence. -/
private lemma powQuotient_exact (r : R) (n : ℕ) :
    Function.Exact (powQuotientLeftMap (M := M) r n) (powQuotientRightMap (M := M) r n) := by
  intro x
  constructor
  · intro hx
    rcases Submodule.Quotient.mk_surjective ((r ^ (n + 1)) • (⊤ : Submodule R M)) x with ⟨m, rfl⟩
    rw [powQuotientRightMap_apply_mk, Submodule.Quotient.mk_eq_zero] at hx
    rcases (Submodule.mem_smul_pointwise_iff_exists m (r ^ n)
        (⊤ : Submodule R M)).mp hx with ⟨y, -, rfl⟩
    -- Any class killed by the projection is represented by a multiple of `r ^ n`.
    exact ⟨Submodule.Quotient.mk y, by rw [powQuotientLeftMap_apply_mk]⟩
  · rintro ⟨y, rfl⟩
    rcases Submodule.Quotient.mk_surjective (r • (⊤ : Submodule R M)) y with ⟨m, rfl⟩
    rw [powQuotientLeftMap_apply_mk, powQuotientRightMap_apply_mk, Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ (r ^ n)
      (⊤ : Submodule R M)).2 ⟨m, trivial, rfl⟩

/-- Helper for Lemma 10.68.9: the two power-quotient maps compose to zero. -/
private lemma powQuotient_comp_eq_zero (r : R) (n : ℕ) :
    (powQuotientRightMap (M := M) r n).comp (powQuotientLeftMap (M := M) r n) = 0 := by
  apply Submodule.quot_hom_ext _ _ _
  intro m
  rw [LinearMap.comp_apply, powQuotientLeftMap_apply_mk, powQuotientRightMap_apply_mk]
  change (Submodule.Quotient.mk (r ^ n • m) : QuotSMulTop (r ^ n) M) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact (Submodule.mem_smul_pointwise_iff_exists _ (r ^ n)
    (⊤ : Submodule R M)).2 ⟨m, trivial, rfl⟩

/-- Helper for Lemma 10.68.9: the quotients `M / rM`, `M / r^(n + 1)M`, and `M / r^n M` form a
short exact sequence when `r` is a non-zero-divisor on `M`. -/
private lemma pow_quotient_shortExact {r : R} {n : ℕ} (hr : IsSMulRegular M r) :
    (ModuleCat.shortComplexOfCompEqZero
      (powQuotientLeftMap (M := M) r n)
      (powQuotientRightMap (M := M) r n)
      (powQuotient_comp_eq_zero (M := M) r n)).ShortExact := by
  -- Exactness comes from the direct quotient computation above.
  refine ModuleCat.shortComplex_shortExact _ (powQuotient_exact (M := M) r n)
    (powQuotientLeftMap_injective (M := M) hr) ?_
  exact Submodule.factor_surjective (pow_smulTop_le (M := M) r (Nat.le_succ n))

/-- Helper for Lemma 10.68.9: quotient the left map in the power tower by a fixed prefix ideal. -/
private abbrev powQuotientPrefixLeftMap (a : R) (n : ℕ) (ps : List R) :
    ((QuotSMulTop a M) ⧸ (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M)))) →ₗ[R]
      ((QuotSMulTop (a ^ (n + 1)) M) ⧸
        (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 1)) M)))) :=
  Submodule.mapQ
    (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M)))
    (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 1)) M)))
    (powQuotientLeftMap (M := M) a n)
    (Submodule.smul_top_le_comap_smul_top (Ideal.ofList ps) _)

/-- Helper for Lemma 10.68.9: quotient the right map in the power tower by a fixed prefix ideal. -/
private abbrev powQuotientPrefixRightMap (a : R) (n : ℕ) (ps : List R) :
    ((QuotSMulTop (a ^ (n + 1)) M) ⧸
      (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 1)) M)))) →ₗ[R]
      ((QuotSMulTop (a ^ n) M) ⧸
        (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ n) M)))) :=
  Submodule.mapQ
    (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 1)) M)))
    (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ n) M)))
    (powQuotientRightMap (M := M) a n)
    (Submodule.smul_top_le_comap_smul_top (Ideal.ofList ps) _)

/-- Helper for Lemma 10.68.9: after quotienting by any fixed prefix ideal, the power-quotient row
still stays exact because the right map is already surjective. -/
private lemma pow_quotient_prefix_exact (a : R) (n : ℕ) (ps : List R) :
    Function.Exact
      (powQuotientPrefixLeftMap (M := M) a n ps)
      (powQuotientPrefixRightMap (M := M) a n ps) := by
  -- The right map is surjective, so the quotient exactness criterion reduces to rewriting the
  -- image of the prefixed submodule under that surjection.
  refine (Function.Exact.exact_mapQ_iff (hfg := powQuotient_exact (M := M) a n)
    (hpq := Submodule.smul_top_le_comap_smul_top (Ideal.ofList ps) _)
    (hqr := Submodule.smul_top_le_comap_smul_top (Ideal.ofList ps) _)).2 ?_
  rw [LinearMap.range_eq_top.mpr
      (Submodule.factor_surjective (pow_smulTop_le (M := M) a (Nat.le_succ n))),
    top_inf_eq, Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr
      (Submodule.factor_surjective (pow_smulTop_le (M := M) a (Nat.le_succ n)))]

/-- Helper for Lemma 10.68.9: the left map in the prefixed power row stays injective when the
prefix is weakly regular on the right term, which is the packaged module-theoretic snake step. -/
private lemma pow_quotient_prefix_left_injective {a : R} {n : ℕ} {ps : List R}
    (ha : IsSMulRegular M a) (hps : IsWeaklyRegular (QuotSMulTop (a ^ n) M) ps) :
    Function.Injective (powQuotientPrefixLeftMap (M := M) a n ps) := by
  -- Route correction: instead of chasing kernels elementwise after quotienting by a prefix, use
  -- the four-term exactness theorem with a zero first term to recover injectivity at once.
  have hzeroExact :
      Function.Exact (0 : Unit →ₗ[R] QuotSMulTop a M) (powQuotientLeftMap (M := M) a n) :=
    (LinearMap.exact_zero_iff_injective Unit (powQuotientLeftMap (M := M) a n)).2
      (powQuotientLeftMap_injective (M := M) ha)
  have hprefixExact :
      Function.Exact
        (0 :
          (Unit ⧸ (Ideal.ofList ps • (⊤ : Submodule R Unit))) →ₗ[R]
            ((QuotSMulTop a M) ⧸
              (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M)))))
        (powQuotientPrefixLeftMap (M := M) a n ps) := by
    simpa [powQuotientPrefixLeftMap, Submodule.mapQ_zero] using
      RingTheory.Sequence.map_first_exact_on_four_term_right_exact_of_isSMulRegular_last
        (M := Unit) (M₂ := QuotSMulTop a M) (M₃ := QuotSMulTop (a ^ (n + 1)) M)
        (M₄ := QuotSMulTop (a ^ n) M) (rs := ps) hzeroExact
        (powQuotient_exact (M := M) a n)
        (Submodule.factor_surjective (pow_smulTop_le (M := M) a (Nat.le_succ n))) hps
  exact
    (LinearMap.exact_zero_iff_injective
      (Unit ⧸ (Ideal.ofList ps • (⊤ : Submodule R Unit)))
      (powQuotientPrefixLeftMap (M := M) a n ps)).1 hprefixExact

/-- Helper for Lemma 10.68.9: after quotienting by a fixed prefix, regularity of the current tail
head descends from the two larger power quotients to the first power quotient. -/
private lemma pow_quotient_head_regular_descend_after_prefix {a s : R} {n : ℕ} {ps : List R}
    (ha : IsSMulRegular M a) (hps : IsWeaklyRegular (QuotSMulTop (a ^ n) M) ps)
    (hmid :
      IsSMulRegular
        (((QuotSMulTop (a ^ (n + 1)) M) ⧸
          (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 1)) M))))) s) :
    IsSMulRegular
      (((QuotSMulTop a M) ⧸
        (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M))))) s := by
  -- Route correction: the prefixed short exact row is already packaged into an injective left map,
  -- so regularity descends by pulling back along that injection.
  exact hmid.of_injective (powQuotientPrefixLeftMap (M := M) a n ps)
    (pow_quotient_prefix_left_injective (M := M) ha hps)

/-- Helper for Lemma 10.68.9: once the current prefix is known to be regular on the intermediate
power quotient, the next tail head descends from the `a^(n + 2)` quotient to the `a` quotient. -/
private lemma descend_next_tail_head_after_prefix {a b : R} {n : ℕ} {ps : List R}
    (ha : IsSMulRegular M a)
    (hps_mid : IsRegular (QuotSMulTop (a ^ (n + 1)) M) ps)
    (hb_pow :
      IsSMulRegular
        (((QuotSMulTop (a ^ (n + 2)) M) ⧸
          (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 2)) M))))) b) :
    IsSMulRegular
      (((QuotSMulTop a M) ⧸
        (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M))))) b := by
  -- This is the exact one-step descent used in the source proof's repeated "and so on" step.
  exact pow_quotient_head_regular_descend_after_prefix (M := M) (a := a) (s := b) (n := n + 1)
    ha hps_mid.toIsWeaklyRegular hb_pow

/-- Helper for Lemma 10.68.9: replacing a single regular element by a positive power preserves
regularity. -/
private lemma isRegular_singleton_pow_iff {r : R} {e : ℕ} (he : 0 < e) :
    IsRegular M [r] ↔ IsRegular M [r ^ e] := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨n, rfl⟩
  rw [isRegular_cons_iff, isRegular_cons_iff]
  constructor
  · intro hreg
    rcases hreg with ⟨hr, hquot⟩
    have hpow : IsSMulRegular M (r ^ (n + 1)) := hr.pow (n + 1)
    have hnontrivial :
        Nontrivial (QuotSMulTop (r ^ (n + 1)) M) := by
      -- Inject the first quotient into the higher-power quotient.
      letI := hquot.nontrivial
      exact Function.Injective.nontrivial (powQuotientLeftMap_injective (M := M) hr)
    have hnil : IsRegular (QuotSMulTop (r ^ (n + 1)) M) ([] : List R) := by
      letI := hnontrivial
      exact IsRegular.nil R _
    exact ⟨hpow, hnil⟩
  · intro hreg
    rcases hreg with ⟨hpow, hquot⟩
    have hr : IsSMulRegular M r := (IsSMulRegular.pow_iff (M := M) (Nat.succ_pos n)).mp hpow
    have hnontrivial :
        Nontrivial (QuotSMulTop r M) := by
      -- If `M = rM`, then repeated substitution would force `M = r^(n + 1)M`, contradicting
      -- the nontriviality of the higher-power quotient.
      have htop_ne : (⊤ : Submodule R M) ≠ r • (⊤ : Submodule R M) := by
        intro htop
        have hpow_top :
            (⊤ : Submodule R M) = (r ^ (n + 1)) • (⊤ : Submodule R M) :=
          top_eq_pow_smulTop_of_top_eq_smul (M := M) r n htop
        exact (Submodule.Quotient.nontrivial_iff.mp hquot.nontrivial) hpow_top.symm
      exact Submodule.Quotient.nontrivial_iff.mpr htop_ne.symm
    have hnil : IsRegular (QuotSMulTop r M) ([] : List R) := by
      letI := hnontrivial
      exact IsRegular.nil R _
    exact ⟨hr, hnil⟩

/-- Helper for Lemma 10.68.9: once `a` is regular on `M`, regularity on `M / aM` ascends to every
successive power quotient `M / a^(n + 1) M` by the short exact sequences from the source proof. -/
private lemma isRegular_power_quotient_ascend_succ {a : R} {n : ℕ}
    (ha : IsSMulRegular M a) {rs : List R} :
    IsRegular (QuotSMulTop a M) rs → IsRegular (QuotSMulTop (a ^ (n + 1)) M) rs := by
  induction n with
  | zero =>
    intro hreg
    -- For the first power, the quotient is the original `M / aM`.
    have hpow :
        (a ^ 1) • (⊤ : Submodule R M) = a • (⊤ : Submodule R M) := by
      simp [pow_one]
    exact ((Submodule.quotEquivOfEq _ _ hpow).isRegular_congr rs).2 hreg
  | succ n ih =>
      intro hleft
      have hright : IsRegular (QuotSMulTop (a ^ (n + 1)) M) rs := by
        -- First climb from `M / aM` to `M / a^(n + 1)M` by the induction hypothesis.
        exact ih hleft
      -- Then insert one more power step using the short exact sequence
      -- `0 → M / aM → M / a^(n + 2)M → M / a^(n + 1)M → 0`.
      simpa using
        CategoryTheory.ShortComplex.ShortExact.isRegular_X₂
          (S := ModuleCat.shortComplexOfCompEqZero
            (powQuotientLeftMap (M := M) a (n + 1))
            (powQuotientRightMap (M := M) a (n + 1))
            (powQuotient_comp_eq_zero (M := M) a (n + 1)))
          (pow_quotient_shortExact (M := M) (r := a) (n := n + 1) ha)
          hleft hright

/-- Helper for Lemma 10.68.9: replacing the head of a regular sequence by a positive power
preserves regularity in the forward direction. -/
private lemma isRegular_cons_pow_of_isRegular_cons {a : R} {e : ℕ} {rs : List R}
    (he : 0 < e) :
    IsRegular M (a :: rs) → IsRegular M (a ^ e :: rs) := by
  intro hreg
  rcases (isRegular_cons_iff (M := M) a rs).1 hreg with ⟨ha, htail⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨n, rfl⟩
  have htail_pow : IsRegular (QuotSMulTop (a ^ (n + 1)) M) rs := by
    -- The tail regularity ascends from `M / aM` to `M / a^e M`.
    simpa using isRegular_power_quotient_ascend_succ (M := M) (a := a) (n := n) ha htail
  -- Reassemble the sequence after replacing the head by its positive power.
  exact (isRegular_cons_iff (M := M) (a ^ (n + 1)) rs).2 ⟨ha.pow (n + 1), htail_pow⟩

/-- Helper for Lemma 10.68.9: regularity over an appended list splits into regularity of the
prefix and regularity of the tail on the quotient by that prefix. -/
private lemma isRegular_append_iff {rs₁ rs₂ : List R} :
    IsRegular M (rs₁ ++ rs₂) ↔
      IsRegular M rs₁ ∧
        IsRegular (M ⧸ (Ideal.ofList rs₁ • (⊤ : Submodule R M))) rs₂ := by
  induction rs₁ generalizing M with
  | nil =>
      let e : (M ⧸ (Ideal.ofList ([] : List R) • (⊤ : Submodule R M))) ≃ₗ[R] M :=
        Submodule.quotEquivOfEqBot _ (by simp [Ideal.ofList_nil])
      constructor
      · intro h
        -- The empty prefix is regular once the ambient module is known to be nontrivial.
        have hnil : IsRegular M ([] : List R) := by
          letI := h.nontrivial
          exact IsRegular.nil R M
        exact ⟨hnil, (e.isRegular_congr rs₂).2 h⟩
      · rintro ⟨_, h₂⟩
        -- Removing the empty prefix leaves the original regularity statement unchanged.
        exact (e.isRegular_congr rs₂).1 h₂
  | cons r rs₁ ih =>
      let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M r rs₁
      -- Peel off the head, recurse on the quotient by that head, then rewrite the quotient by
      -- the whole prefix back into the canonical owner form.
      rw [List.cons_append, isRegular_cons_iff, isRegular_cons_iff, ih,
        ← and_assoc, ← e.isRegular_congr rs₂]

/-- Helper for Lemma 10.68.9: permuting generators does not change the ideal they generate. -/
private lemma ofList_eq_of_perm {rs ts : List R} (hperm : List.Perm rs ts) :
    Ideal.ofList rs = Ideal.ofList ts := by
  -- The ideal depends only on membership in the generating list.
  refine congrArg Ideal.span <| Set.ext fun r => by
    simpa using hperm.mem_iff

/-- Helper for Lemma 10.68.9: moving the head generator to the end does not change the ideal it
generates. -/
private lemma ofList_cons_eq_ofList_append_singleton (r : R) (rs : List R) :
    Ideal.ofList (r :: rs) = Ideal.ofList (rs ++ [r]) := by
  -- Both lists generate the same ideal because they differ only by a cyclic permutation.
  simpa [Ideal.ofList_cons, Ideal.ofList_append, Ideal.ofList_singleton, sup_assoc, sup_comm,
    sup_left_comm]

/-- Helper for Lemma 10.68.9: the same head-to-tail permutation gives equal scalar-multiple
submodules after passing to a quotient by `r`. -/
private lemma ofList_cons_smulTop_eq_ofList_append_singleton_smulTop (r b : R) (ps : List R) :
    Ideal.ofList (b :: ps) • (⊤ : Submodule R (QuotSMulTop r M)) =
      Ideal.ofList (ps ++ [b]) • (⊤ : Submodule R (QuotSMulTop r M)) := by
  -- This is the ideal equality needed to compare the two quotient presentations.
  exact congrArg (fun I : Ideal R ↦ I • (⊤ : Submodule R (QuotSMulTop r M))) <|
    ofList_cons_eq_ofList_append_singleton (R := R) b ps

/-- Helper for Lemma 10.68.9: adjoining `b` after quotienting by `ps` is the same as quotienting
the extended prefix module `M / (ps ++ [b]) M` by the head `r`. -/
private abbrev quot_snoc_head_equiv (r b : R) (ps : List R) :
    QuotSMulTop b (((QuotSMulTop r M) ⧸
      (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop r M))))) ≃ₗ[R]
      QuotSMulTop r (M ⧸ (Ideal.ofList (ps ++ [b]) • (⊤ : Submodule R M))) :=
  (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter
    (M := QuotSMulTop r M) b ps).symm.trans <|
    (Submodule.quotEquivOfEq _ _
      (ofList_cons_smulTop_eq_ofList_append_singleton_smulTop (M := M) r b ps)).trans <|
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner
        (M := M) r (ps ++ [b])).symm.trans <|
        Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter
          (M := M) r (ps ++ [b])

/-- Helper for Lemma 10.68.9: once a quotient is already `rM`, the same holds for every positive
power of `r`. -/
private lemma quot_head_trivial_of_pow_head_trivial
    {N : Type v} [AddCommGroup N] [Module R N] {r : R} {k : ℕ}
    (htop : (⊤ : Submodule R N) = r • (⊤ : Submodule R N)) :
    (⊤ : Submodule R N) = (r ^ (k + 1)) • (⊤ : Submodule R N) := by
  -- This is exactly the iterated substitution used in the singleton source proof.
  simpa using top_eq_pow_smulTop_of_top_eq_smul (M := N) r k htop

/-- Helper for Lemma 10.68.9: after descending the injectivity of `b` across the prefixed power
row, the remaining singleton regularity on the prefixed quotient follows by contradiction on the
common extended-prefix quotient `M / (ps ++ [b]) M`. -/
private lemma prefixed_power_singleton_regular_descend {a b : R} {n : ℕ} {ps : List R}
    (ih_small :
      ∀ {N : Type v} [AddCommGroup N] [Module R N] {ts : List R},
        IsRegular N (a :: ts) ↔ IsRegular N (a ^ (n + 1) :: ts))
    (hprefix : IsRegular M (a :: ps))
    (hpow_prefix : IsRegular M (a ^ (n + 2) :: ps ++ [b])) :
    IsRegular
      (((QuotSMulTop a M) ⧸
        (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M))))) [b] := by
  -- Route correction: the exact row already descends injectivity; only the final nontriviality
  -- must be proved, and the source proof does so on the common quotient by `ps ++ [b]`.
  rcases (isRegular_cons_iff (M := M) a ps).1 hprefix with ⟨ha, _⟩
  have hprefix_mid : IsRegular M (a ^ (n + 1) :: ps) := by
    -- Lower the head exponent once before extracting the current tail prefix.
    exact (ih_small (N := M) (ts := ps)).1 hprefix
  rcases (isRegular_cons_iff (M := M) (a ^ (n + 1)) ps).1 hprefix_mid with ⟨_, hps_mid⟩
  rcases (isRegular_cons_iff (M := M) (a ^ (n + 2)) (ps ++ [b])).1 hpow_prefix with
    ⟨_, hpow_tail⟩
  rcases (isRegular_append_iff (M := QuotSMulTop (a ^ (n + 2)) M) (rs₁ := ps) (rs₂ := [b])).1
      hpow_tail with ⟨_, hb_single_pow⟩
  let X :=
    ((QuotSMulTop a M) ⧸
      (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M))))
  let Xpow :=
    ((QuotSMulTop (a ^ (n + 2)) M) ⧸
      (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop (a ^ (n + 2)) M))))
  rcases (isRegular_cons_iff (M := Xpow) b []).1 (by simpa [Xpow] using hb_single_pow) with
    ⟨hb_pow, hpow_nil⟩
  have hb : IsSMulRegular X b := by
    -- This is the already-established descent of injectivity through the prefixed power row.
    simpa [X] using
      descend_next_tail_head_after_prefix (M := M) (a := a) (b := b) (n := n) (ps := ps)
        ha hps_mid hb_pow
  refine (isRegular_cons_iff (M := X) b []).2 ?_
  refine ⟨hb, ?_⟩
  have hnontrivial : Nontrivial (QuotSMulTop b X) := by
    -- If the quotient by `b` vanished on the `a`-side, transport that vanishing to the common
    -- extended-prefix quotient, raise it to the higher power, and contradict the powered side.
    by_contra htriv
    have hsubX : Subsingleton (QuotSMulTop b X) :=
      not_nontrivial_iff_subsingleton.mp htriv
    let Y := M ⧸ (Ideal.ofList (ps ++ [b]) • (⊤ : Submodule R M))
    have hsubY : Subsingleton (QuotSMulTop a Y) := by
      let eHead := quot_snoc_head_equiv (M := M) a b ps
      exact (eHead.toEquiv.subsingleton_congr).1 hsubX
    have htopY : (⊤ : Submodule R Y) = a • (⊤ : Submodule R Y) := by
      -- Triviality of the `a`-quotient means the whole module is already `aY`.
      change Subsingleton (Y ⧸ (a • (⊤ : Submodule R Y))) at hsubY
      have hsmulTop : (a • (⊤ : Submodule R Y)) = (⊤ : Submodule R Y) :=
        Submodule.Quotient.subsingleton_iff.mp hsubY
      exact hsmulTop.symm
    have hpowY :
        (⊤ : Submodule R Y) = (a ^ (n + 2)) • (⊤ : Submodule R Y) := by
      -- Iterating the head equality gives the corresponding equality for the larger power.
      simpa using
        quot_head_trivial_of_pow_head_trivial (N := Y) (r := a) (k := n + 1) htopY
    have hsubPowY : Subsingleton (QuotSMulTop (a ^ (n + 2)) Y) := by
      -- The higher-power quotient on the common ambient module is therefore trivial too.
      change Subsingleton (Y ⧸ ((a ^ (n + 2)) • (⊤ : Submodule R Y)))
      exact Submodule.Quotient.subsingleton_iff.mpr hpowY.symm
    have hsubPowX : Subsingleton (QuotSMulTop b Xpow) := by
      let ePow := quot_snoc_head_equiv (M := M) (a ^ (n + 2)) b ps
      exact (ePow.toEquiv.subsingleton_congr).2 hsubPowY
    exact (not_nontrivial_iff_subsingleton.mpr hsubPowX) hpow_nil.nontrivial
  letI := hnontrivial
  -- With the quotient by `b` known to be nontrivial, the singleton is regular.
  exact IsRegular.nil R _

/-- Helper for Lemma 10.68.9: replacing the head of a regular sequence by a positive power is the
only remaining converse step after the outer induction powers the tail in the quotient. -/
private lemma isRegular_cons_pow_converse_step {a b : R} {n : ℕ} {ps : List R}
    (ih_small :
      ∀ {N : Type v} [AddCommGroup N] [Module R N] {ts : List R},
        IsRegular N (a :: ts) ↔ IsRegular N (a ^ (n + 1) :: ts))
    (hprefix : IsRegular M (a :: ps))
    (hpow_prefix : IsRegular M (a ^ (n + 2) :: ps ++ [b])) :
    IsRegular M (a :: ps ++ [b]) := by
  -- Route correction: package the singleton-after-prefix descent, then rewrite back to the owner
  -- quotient on `M`.
  refine (isRegular_append_iff (M := M) (rs₁ := a :: ps) (rs₂ := [b])).2 ?_
  refine ⟨hprefix, ?_⟩
  have hb_single :
      IsRegular
        (((QuotSMulTop a M) ⧸
          (Ideal.ofList ps • (⊤ : Submodule R (QuotSMulTop a M))))) [b] :=
    prefixed_power_singleton_regular_descend (M := M) (a := a) (b := b) (n := n) (ps := ps)
      ih_small hprefix hpow_prefix
  let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M a ps
  -- Rewrite the quotient by the extended prefix back into the canonical owner form on `M`.
  simpa using (e.isRegular_congr [b]).2 hb_single

/-- Helper for Lemma 10.68.9: after the exponent has been lowered by one step, the remaining tail
can be descended by extending the prefix one element at a time. -/
private lemma isRegular_cons_pow_converse_aux {a : R} {n : ℕ} {ps rs : List R}
    (ih_small :
      ∀ {N : Type v} [AddCommGroup N] [Module R N] {ts : List R},
        IsRegular N (a :: ts) ↔ IsRegular N (a ^ (n + 1) :: ts))
    (hprefix : IsRegular M (a :: ps))
    (hpow : IsRegular M (a ^ (n + 2) :: ps ++ rs)) :
    IsRegular M (a :: ps ++ rs) := by
  induction rs generalizing ps with
  | nil =>
      -- With no remaining tail, the descended prefix is exactly the given regular prefix.
      simpa using hprefix
  | cons b ts ih =>
      have hprefix_step :
          IsRegular M (a :: ps ++ [b]) := by
        -- First isolate the next head `b`; this is the source proof's single descent step.
        have hpow_step : IsRegular M (a ^ (n + 2) :: ps ++ [b]) := by
          have hsplit :=
            (isRegular_append_iff (M := M)
              (rs₁ := a ^ (n + 2) :: ps ++ [b]) (rs₂ := ts)).1 <|
              by simpa [List.append_assoc] using hpow
          simpa [List.append_assoc] using hsplit.1
        exact isRegular_cons_pow_converse_step (M := M) (a := a) (b := b) (n := n)
          (ps := ps) ih_small hprefix hpow_step
      have hpow_tail :
          IsRegular M (a ^ (n + 2) :: (ps ++ [b]) ++ ts) := by
        simpa [List.append_assoc] using hpow
      -- Then recurse after adding `b` to the already-descended prefix.
      simpa [List.append_assoc] using ih (ps := ps ++ [b]) hprefix_step hpow_tail

/-- Helper for Lemma 10.68.9: replacing the head of a regular sequence by a positive power is the
only remaining converse step after the outer induction powers the tail in the quotient. -/
private lemma isRegular_cons_pow_iff {a : R} {e : ℕ} {rs : List R}
    (he : 0 < e) :
    IsRegular M (a :: rs) ↔ IsRegular M (a ^ e :: rs) := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he) with ⟨n, rfl⟩
  induction n generalizing M rs with
  | zero =>
      -- The exponent-one case is definitional.
      simpa [pow_one]
  | succ n ih =>
      constructor
      · -- The forward implication is the already-proved ascent along the power tower.
        exact isRegular_cons_pow_of_isRegular_cons (M := M) (a := a) (e := n + 2)
          (Nat.succ_pos _)
      · intro hpow
        have ih_small :
            ∀ {N : Type v} [AddCommGroup N] [Module R N] {ts : List R},
              IsRegular N (a :: ts) ↔ IsRegular N (a ^ (n + 1) :: ts) := by
          intro N _ _ ts
          simpa using (ih (M := N) (rs := ts))
        have hsingleton_pow : IsRegular M [a ^ (n + 2)] := by
          -- The powered head alone is a regular prefix of the full powered sequence.
          simpa using
            (isRegular_append_iff (M := M) (rs₁ := [a ^ (n + 2)]) (rs₂ := rs)).1 hpow |>.1
        have hsingleton : IsRegular M [a] := by
          exact (isRegular_singleton_pow_iff (M := M) (r := a) (e := n + 2)
            (Nat.succ_pos _)).2 hsingleton_pow
        -- Apply the prefix-growing converse descent with the empty initial tail prefix.
        simpa using
          isRegular_cons_pow_converse_aux (M := M) (a := a) (n := n) (ps := [])
            (rs := rs) ih_small hsingleton (by simpa using hpow)

/-
Domain triage:
* primary domain: regular sequences in commutative algebra;
* sampled owner API:
  `RingTheory.Sequence.IsRegular`,
  `RingTheory.Sequence.isRegular_cons_iff`,
  `IsSMulRegular.pow_iff`,
  `CategoryTheory.ShortComplex.ShortExact.isRegular_X₂`;
* core/canonical owner: `RingTheory.Sequence.IsRegular M rs`;
* primitive vs derived split: the module `M`, the element list `rs`, and the owner predicate
  `IsRegular M rs` are primitive data; invariance under replacing entries by positive powers is
  derived source-facing API and should not be repackaged into a new owner wrapper;
* layer classification for this file: the theorem below is `source-facing`, while its proof should
  reuse the owner regular-sequence API and the quotient short-exact-sequence bridge from
  Lemma `10.68.8`.
-/

-- Proof sketch: argue by induction on the regular sequence. For a singleton, use that an element
-- is `M`-regular if and only if any positive power is `M`-regular. For a longer sequence, apply
-- the induction hypothesis to the quotient by the first element and then compare the first term
-- with its positive power using the short exact sequences relating `M / fM`, `M / f^e M`, and
-- `M / f^(e - 1) M` as in Lemmas 10.68.8 and 10.4.1.
/-- Lemma 10.68.9: a sequence `rs` is regular on `M` if and only if the sequence obtained by
taking pointwise positive powers of its terms is regular on `M`. -/
theorem isRegular_iff_isRegular_pow
    {rs : List R} {es : List ℕ}
    (hes : List.Forall₂ (fun (_ : R) e ↦ 0 < e) rs es) :
    IsRegular M rs ↔ IsRegular M (rs.zipWith (· ^ ·) es) := by
  constructor
  · -- Follow the source proof in the easy direction: power the head, then power the tail in the
    -- quotient by the powered head.
    intro hreg
    induction hes generalizing M with
    | nil =>
        simpa using hreg
    | @cons r e rs es he hes ih =>
        -- First replace the current head by its positive power.
        have hhead :
            IsRegular M (r ^ e :: rs) :=
          isRegular_cons_pow_of_isRegular_cons (M := M) (a := r) (e := e) he hreg
        rcases (isRegular_cons_iff (M := M) (r ^ e) rs).1 hhead with ⟨hre, htail⟩
        -- Then power the remaining tail inside the quotient by the already-powered head.
        have htail_pow :
            IsRegular (QuotSMulTop (r ^ e) M) (rs.zipWith (· ^ ·) es) :=
          ih htail
        exact (isRegular_cons_iff (M := M) (r ^ e) _).2 ⟨hre, htail_pow⟩
  · -- Follow the source-faithful converse: unpower the tail in the quotient, then descend the
    -- head exponent one step at a time through the prefixed quotient tower.
    intro hreg
    induction hes generalizing M with
    | nil =>
        simpa using hreg
    | @cons r e rs es he hes ih =>
        -- First unpower the tail inside the quotient by the already-powered head.
        rcases (isRegular_cons_iff (M := M) (r ^ e) (rs.zipWith (· ^ ·) es)).1 hreg with
          ⟨hre, htail_pow⟩
        have htail : IsRegular (QuotSMulTop (r ^ e) M) rs :=
          ih htail_pow
        have hhead : IsRegular M (r ^ e :: rs) :=
          (isRegular_cons_iff (M := M) (r ^ e) rs).2 ⟨hre, htail⟩
        -- Then replace the powered head by the original head using the dedicated local lemma.
        exact (isRegular_cons_pow_iff (M := M) (a := r) (e := e) (rs := rs) he).2 hhead

end

end RingTheory.Sequence
