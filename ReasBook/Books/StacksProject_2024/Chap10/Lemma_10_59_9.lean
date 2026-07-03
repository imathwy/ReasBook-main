import Mathlib
import stacks_project.Chap10.Lemma_10_52_8
import stacks_project.Chap10.Lemma_10_59_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter Ideal IsLocalRing
open scoped Ideal

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]

-- Source/core/bridge triage:
-- * source-facing: compare eventual Hilbert-Samuel `χ`-polynomials of `M` and a finite-colength
--   submodule `N ⊆ M`;
-- * core/canonical: the owner invariant `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the first theorem is the polynomial-representative comparison, while the second
--   theorem pushes that comparison down to the owner invariant.

-- Proof sketch: apply Lemma 10.59.2 to compare the `χ`-functions of `M` and `N` up to an
-- additive constant and a finite shift. After converting the finite lengths to rational-valued
-- functions, the difference of the two eventual Hilbert-Samuel polynomials is eventually bounded,
-- so elementary polynomial growth shows that `P - P'` has strictly smaller degree than both `P`
-- and `P'`.
/-- Helper for Lemma 10.59.9: every Hilbert-Samuel quotient attached to an ideal of definition has
finite length. -/
lemma isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (n : ℕ) :
    IsFiniteLength R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) := by
  -- Compare a power of the maximal ideal with the chosen ideal of definition.
  have hleRad : maximalIdeal R ≤ I.radical := by
    rw [hI]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  let Q : Type v := M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))
  -- The quotient is killed by `I ^ (n + 1)`, hence also by a power of the maximal ideal.
  have hQtors : Module.IsTorsionBySet R Q (I ^ (n + 1) : Ideal R) := by
    rw [Module.isTorsionBySet_quotient_iff]
    intro x r hr
    change r • x ∈ (I ^ (n + 1) • (⊤ : Submodule R M))
    exact Submodule.smul_mem_smul hr (show x ∈ (⊤ : Submodule R M) by simp)
  have hQann : (maximalIdeal R) ^ (c * (n + 1)) ≤ Module.annihilator R Q := by
    have hpow : (maximalIdeal R) ^ (c * (n + 1)) ≤ I ^ (n + 1) := by
      simpa [pow_mul] using Ideal.pow_right_mono hc (n + 1)
    exact hpow.trans <| (Module.isTorsionBySet_iff_subset_annihilator R Q).mp hQtors
  have hpowQ : ((maximalIdeal R) ^ (c * (n + 1))) • (⊤ : Submodule R Q) = ⊥ := by
    refine (Submodule.le_annihilator_iff).mp ?_
    simpa [Submodule.annihilator_top] using hQann
  -- Finite generation of the quotient lets us invoke the finite-length criterion for nilpotent
  -- maximal-ideal action.
  exact isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R)
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hpowQ

omit [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M] in
/-- Helper for Lemma 10.59.9: a finite-colength submodule of an infinite-length finite module also
has infinite length. -/
lemma not_isFiniteLength_of_finiteColength_submodule
    (N : Submodule R M) (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N)) :
    ¬ IsFiniteLength R N := by
  intro hN
  -- Finite length ascends from a submodule and quotient to the ambient module.
  have hMfinite : IsFiniteLength R M := by
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨(isNoetherian_iff_submodule_quotient N).mpr
        ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1,
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hquot).1⟩,
      (isArtinian_iff_submodule_quotient N).mpr
        ⟨(isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2,
          (isFiniteLength_iff_isNoetherian_isArtinian.mp hquot).2⟩⟩
  exact hM hMfinite

/-- Helper for Lemma 10.59.9: if an eventual Hilbert-Samuel polynomial had degree at most zero,
then the module would have finite length. -/
lemma degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {P : Polynomial ℚ}
    (hM : ¬ IsFiniteLength R M)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ)) :
    0 < P.degree := by
  by_contra hdeg
  have hdeg' : P.degree ≤ 0 := not_lt.mp hdeg
  -- Route correction: instead of differentiating `P`, force eventual constancy of `χ_{I,M}` and
  -- then use Nakayama to annihilate a power of `I`.
  have hconst : P = Polynomial.C (P.coeff 0) := by
    simpa using (Polynomial.degree_le_zero_iff.mp hdeg')
  rcases Filter.eventually_atTop.mp hP with ⟨N, hN⟩
  let J₀ : Submodule R M := I ^ (N + 1) • (⊤ : Submodule R M)
  let J₁ : Submodule R M := I ^ (N + 2) • (⊤ : Submodule R M)
  have hRatEq :
      (((χ_ I M (N + 1)).toNat : ℕ) : ℚ) =
        (((χ_ I M N).toNat : ℕ) : ℚ) := by
    -- Evaluate the constant polynomial at `N` and `N + 1`.
    calc
      (((χ_ I M (N + 1)).toNat : ℕ) : ℚ) = P.eval ((N + 1 : ℕ) : ℚ) := by
        symm
        exact hN (N + 1) (Nat.le_add_right N 1)
      _ = P.coeff 0 := by
        rw [hconst]
        simp
      _ = P.eval (N : ℚ) := by
        rw [hconst]
        simp
      _ = (((χ_ I M N).toNat : ℕ) : ℚ) := hN N le_rfl
  have hNatEq : (χ_ I M (N + 1)).toNat = (χ_ I M N).toNat := by
    exact_mod_cast hRatEq
  have hfin₀ : IsFiniteLength R (M ⧸ J₀) := by
    simpa [J₀] using isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
      (R := R) (M := M) I hI N
  have hfin₁ : IsFiniteLength R (M ⧸ J₁) := by
    simpa [J₁] using isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
      (R := R) (M := M) I hI (N + 1)
  have hχ₀ne : χ_ I M N ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, J₀, Module.length_ne_top_iff] using hfin₀
  have hχ₁ne : χ_ I M (N + 1) ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, J₁, Module.length_ne_top_iff] using hfin₁
  have hJ₁le : J₁ ≤ J₀ := by
    -- Powers of `I` form a descending chain.
    simpa [J₀, J₁] using Submodule.pow_smul_top_le I M (Nat.le_succ (N + 1))
  have hdecomp :
      χ_ I M (N + 1) =
        χ_ I M N + Module.length R (J₀ ⧸ J₁.submoduleOf J₀) := by
    -- The successive quotient measures the jump in the Hilbert-Samuel function.
    simpa [Ideal.hilbertSamuelChi, J₀, J₁] using
      (length_quotient_eq_add_length_submodule_quotient_of_le
        (R := R) (M := M) hJ₁le)
  have hLne : Module.length R (J₀ ⧸ J₁.submoduleOf J₀) ≠ ⊤ := by
    intro htop
    have : χ_ I M (N + 1) = ⊤ := by simpa [hdecomp, htop]
    exact hχ₁ne this
  have hdecompNat :
      (χ_ I M (N + 1)).toNat =
        (χ_ I M N).toNat + (Module.length R (J₀ ⧸ J₁.submoduleOf J₀)).toNat := by
    simpa [ENat.toNat_add hχ₀ne hLne] using congrArg ENat.toNat hdecomp
  have hLNatZero : (Module.length R (J₀ ⧸ J₁.submoduleOf J₀)).toNat = 0 := by
    omega
  have hLZero : Module.length R (J₀ ⧸ J₁.submoduleOf J₀) = 0 := by
    calc
      Module.length R (J₀ ⧸ J₁.submoduleOf J₀) =
          (((Module.length R (J₀ ⧸ J₁.submoduleOf J₀)).toNat : ℕ) : ℕ∞) := by
            exact (ENat.coe_toNat hLne).symm
      _ = 0 := by simp [hLNatZero]
  have hSubsingleton : Subsingleton (J₀ ⧸ J₁.submoduleOf J₀) := by
    exact Module.length_eq_zero_iff.mp hLZero
  have htop : J₁.submoduleOf J₀ = ⊤ := by
    exact Submodule.Quotient.subsingleton_iff.mp hSubsingleton
  have hJ₀le : J₀ ≤ J₁ := by
    intro x hx
    have hmemTop : (⟨x, hx⟩ : J₀) ∈ (⊤ : Submodule R J₀) := by simp
    have hmem : (⟨x, hx⟩ : J₀) ∈ J₁.submoduleOf J₀ := by
      simpa [htop] using hmemTop
    exact hmem
  have hstable : J₀ = J₁ := le_antisymm hJ₀le hJ₁le
  have hEqSmul : J₀ = I • J₀ := by
    calc
      J₀ = J₁ := hstable
      _ = I • J₀ := by
        dsimp [J₀, J₁]
        rw [pow_succ', mul_smul]
  have hIleJac : I ≤ Ideal.jacobson (⊥ : Ideal R) := by
    calc
      I ≤ maximalIdeal R := by
        calc
          I ≤ I.radical := Ideal.le_radical
          _ = maximalIdeal R := hI
      _ ≤ Ideal.jacobson (⊥ : Ideal R) := IsLocalRing.maximalIdeal_le_jacobson _
  have hJ₀bot : J₀ = ⊥ := by
    exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I J₀
      (IsNoetherian.noetherian _) hEqSmul.le hIleJac
  have hleRad : maximalIdeal R ≤ I.radical := by
    rw [hI]
  obtain ⟨c, hc⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hleRad
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  have hpowBot : ((maximalIdeal R) ^ (c * (N + 1))) • (⊤ : Submodule R M) = ⊥ := by
    apply le_antisymm
    · calc
        ((maximalIdeal R) ^ (c * (N + 1))) • (⊤ : Submodule R M) ≤
            I ^ (N + 1) • (⊤ : Submodule R M) := by
              exact Submodule.smul_mono_left <| by
                simpa [pow_mul] using Ideal.pow_right_mono hc (N + 1)
        _ = ⊥ := by simpa [J₀] using hJ₀bot
    · exact bot_le
  have hFinite : IsFiniteLength R M := by
    exact isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R)
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hpowBot
  exact hM hFinite

/-- Helper for Lemma 10.59.9: translating a positive-degree polynomial by a constant lowers the
degree of the corresponding finite-difference polynomial. -/
lemma degree_translate_sub_lt {Q : Polynomial ℚ} (hQ : 0 < Q.degree) (a : ℚ) :
    (Q.comp (Polynomial.X + Polynomial.C a) - Q).degree < Q.degree ∧
      (Q - Q.comp (Polynomial.X - Polynomial.C a)).degree < Q.degree := by
  have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQ
  have hdegAdd :
      (Q.comp (Polynomial.X + Polynomial.C a)).degree = Q.degree := by
    calc
      (Q.comp (Polynomial.X + Polynomial.C a)).degree =
          Q.degree * (Polynomial.X + Polynomial.C a).degree := by
            exact Polynomial.degree_comp (p := Q) (q := Polynomial.X + Polynomial.C a) <| by
              rw [Polynomial.degree_X_add_C]
              decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_add_C]
        simp
  have hlcAdd :
      (Q.comp (Polynomial.X + Polynomial.C a)).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · simp [Polynomial.leadingCoeff_X_add_C]
    · rw [Polynomial.natDegree_X_add_C]
      decide
  have hltAdd :
      (Q.comp (Polynomial.X + Polynomial.C a) - Q).degree <
        (Q.comp (Polynomial.X + Polynomial.C a)).degree := by
    exact Polynomial.degree_sub_lt hdegAdd
      ((Polynomial.comp_X_add_C_ne_zero_iff (p := Q) (t := a)).2 hQ0) hlcAdd
  have hdegSub :
      (Q.comp (Polynomial.X - Polynomial.C a)).degree = Q.degree := by
    calc
      (Q.comp (Polynomial.X - Polynomial.C a)).degree =
          Q.degree * (Polynomial.X - Polynomial.C a).degree := by
            exact Polynomial.degree_comp (p := Q) (q := Polynomial.X - Polynomial.C a) <| by
              rw [Polynomial.degree_X_sub_C]
              decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_sub_C]
        simp
  have hlcSub :
      (Q.comp (Polynomial.X - Polynomial.C a)).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · simp [Polynomial.leadingCoeff_X_sub_C]
    · rw [Polynomial.natDegree_X_sub_C]
      decide
  have hltSub :
      (Q - Q.comp (Polynomial.X - Polynomial.C a)).degree < Q.degree := by
    exact Polynomial.degree_sub_lt hdegSub.symm hQ0 hlcSub.symm
  exact ⟨by simpa [hdegAdd] using hltAdd, hltSub⟩

/-- Helper for Lemma 10.59.9: an eventually nonnegative polynomial bounded above by a lower-degree
polynomial must itself have lower degree. -/
lemma degree_lt_of_eventually_nonneg_le {E Q : Polynomial ℚ} {k : WithBot ℕ}
    (hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ E.eval (n : ℚ) ∧ E.eval (n : ℚ) ≤ Q.eval (n : ℚ))
    (hQk : Q.degree < k) :
    E.degree < k := by
  by_contra hEk
  have hEk' : k ≤ E.degree := not_lt.mp hEk
  have hQE : Q.degree < E.degree := lt_of_lt_of_le hQk hEk'
  have hE0 : E ≠ 0 := by
    exact Polynomial.ne_zero_of_degree_gt hQE
  have hNoRoot :
      ∀ᶠ n : ℕ in atTop, ¬ E.IsRoot (n : ℚ) := by
    exact tendsto_natCast_atTop_atTop.eventually
      (Polynomial.eventually_atTop_not_isRoot (P := E) hE0)
  have hPos :
      ∀ᶠ n : ℕ in atTop, 0 < E.eval (n : ℚ) := by
    -- Eventual nonnegativity plus the absence of eventual roots gives eventual positivity.
    filter_upwards [hbound, hNoRoot] with n hn hnr
    have hne : E.eval (n : ℚ) ≠ 0 := by
      simpa [Polynomial.IsRoot] using hnr
    exact lt_of_le_of_ne hn.1 (Ne.symm hne)
  have hDiv :
      Tendsto (fun n : ℕ ↦ Q.eval (n : ℚ) / E.eval (n : ℚ)) atTop (nhds 0) := by
    exact (Polynomial.div_tendsto_atTop_zero_of_degree_lt (P := Q) (Q := E) hQE).comp
      tendsto_natCast_atTop_atTop
  have hSmall :
      ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) / E.eval (n : ℚ) ∈ Set.Ioo (-1) 1 := by
    exact hDiv.eventually (Ioo_mem_nhds (by norm_num : (-1 : ℚ) < 0)
      (by norm_num : (0 : ℚ) < 1))
  have hFalse : ∀ᶠ n : ℕ in atTop, False := by
    -- The ratio tends to `0`, but eventual positivity and the upper bound force it to be at least
    -- `1`, contradiction.
    filter_upwards [hPos, hSmall, hbound] with n hPosN hSmallN hBoundN
    have hRatioGe : (1 : ℚ) ≤ Q.eval (n : ℚ) / E.eval (n : ℚ) := by
      rw [one_le_div hPosN]
      exact hBoundN.2
    exact (not_le_of_gt hSmallN.2) hRatioGe
  rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
  exact hN N le_rfl

/-- Helper for Lemma 10.59.9: the forward-shifted colength error polynomial is eventually
nonnegative and bounded above by the translate-difference of `P`. -/
lemma eventually_shifted_difference_nonneg_le_translate
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) {P P' : Polynomial ℚ} (c : ℕ)
    (hc : ∀ᶠ n : ℕ in atTop,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤ χ_ I M n ∧
        χ_ I M n ≤ Module.length R (M ⧸ N) + χ_ I N n)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((χ_ I N n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ (P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P' -
            Polynomial.C (((Module.length R (M ⧸ N)).toNat : ℚ))).eval (n : ℚ) ∧
        (P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P' -
            Polynomial.C (((Module.length R (M ⧸ N)).toNat : ℚ))).eval (n : ℚ) ≤
          (P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P).eval (n : ℚ) := by
  let Lq : ℚ := ((Module.length R (M ⧸ N)).toNat : ℚ)
  have hlen : Module.length R (M ⧸ N) ≠ ⊤ := by
    simpa [Module.length_ne_top_iff] using hquot
  have hPshift :
      ∀ᶠ n : ℕ in atTop,
        P.eval ((n + c : ℕ) : ℚ) = ((χ_ I M (n + c)).toNat : ℚ) := by
    exact (tendsto_add_atTop_nat c).eventually hP
  have hcshift :
      ∀ᶠ n : ℕ in atTop,
        Module.length R (M ⧸ N) + χ_ I N ((n + c) - c) ≤ χ_ I M (n + c) ∧
          χ_ I M (n + c) ≤ Module.length R (M ⧸ N) + χ_ I N (n + c) := by
    exact (tendsto_add_atTop_nat c).eventually hc
  filter_upwards [hPshift, hP, hP', hcshift, hc] with n hPshiftN hPN hP'N hcshiftN hcN
  have hχMn : χ_ I M n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI n
  have hχMnShift : χ_ I M (n + c) ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI (n + c)
  have hχNn : χ_ I N n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := N) I hI n
  have hLowerNat :
      (Module.length R (M ⧸ N)).toNat + (χ_ I N n).toNat ≤ (χ_ I M (n + c)).toNat := by
    -- Convert the shifted lower `ENat`-bound into a nat inequality.
    have hLower :
        Module.length R (M ⧸ N) + χ_ I N n ≤ χ_ I M (n + c) := by
      simpa [Nat.add_sub_cancel] using hcshiftN.1
    have hLowerToNat := ENat.toNat_le_toNat hLower hχMnShift
    simpa [ENat.toNat_add hlen hχNn] using hLowerToNat
  have hUpperNat :
      (χ_ I M n).toNat ≤ (Module.length R (M ⧸ N)).toNat + (χ_ I N n).toNat := by
    -- Convert the upper `ENat`-bound into a nat inequality.
    have hsum_ne : Module.length R (M ⧸ N) + χ_ I N n ≠ ⊤ := by
      lift Module.length R (M ⧸ N) to ℕ using hlen with m
      lift χ_ I N n to ℕ using hχNn with k
      intro htop
      have : (((m + k : ℕ) : ℕ∞) = ⊤) := by simpa using htop
      exact ENat.coe_ne_top (m + k) this
    have hUpperToNat := ENat.toNat_le_toNat hcN.2 hsum_ne
    simpa [ENat.toNat_add hlen hχNn] using hUpperToNat
  have hLowerRat :
      Lq + ((χ_ I N n).toNat : ℚ) ≤ ((χ_ I M (n + c)).toNat : ℚ) := by
    have :
        (((Module.length R (M ⧸ N)).toNat : ℚ) + ((χ_ I N n).toNat : ℚ)) ≤
          ((χ_ I M (n + c)).toNat : ℚ) := by
      exact_mod_cast hLowerNat
    simpa [Lq] using this
  have hUpperRat :
      ((χ_ I M n).toNat : ℚ) ≤ Lq + ((χ_ I N n).toNat : ℚ) := by
    have :
        ((χ_ I M n).toNat : ℚ) ≤
          (((Module.length R (M ⧸ N)).toNat : ℚ) + ((χ_ I N n).toNat : ℚ)) := by
      exact_mod_cast hUpperNat
    simpa [Lq] using this
  have hLowerEval :
      Lq + P'.eval (n : ℚ) ≤ P.eval ((n + c : ℕ) : ℚ) := by
    rw [hPshiftN, hP'N]
    exact hLowerRat
  have hUpperEval :
      P.eval (n : ℚ) ≤ Lq + P'.eval (n : ℚ) := by
    rw [hPN, hP'N]
    exact hUpperRat
  have hEval :
      (P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P' - Polynomial.C Lq).eval (n : ℚ) =
        P.eval ((n + c : ℕ) : ℚ) - P'.eval (n : ℚ) - Lq := by
    -- Evaluate the translate at `n` and rewrite it as evaluation at `n + c`.
    simp [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, Nat.cast_add, Lq,
      sub_eq_add_neg, add_left_comm, add_comm]
  have hTranslateEval :
      (P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P).eval (n : ℚ) =
        P.eval ((n + c : ℕ) : ℚ) - P.eval (n : ℚ) := by
    -- The bounding polynomial is exactly the translate-difference of `P`.
    simp [Polynomial.eval_add, Polynomial.eval_comp, Polynomial.eval_X, Nat.cast_add,
      sub_eq_add_neg, add_comm]
  constructor
  · -- The shifted lower bound forces the error term to be nonnegative.
    rw [hEval]
    linarith
  · -- Comparing the shifted lower and unshifted upper bounds gives the translate control.
    rw [hEval, hTranslateEval]
    linarith

/-- Helper for Lemma 10.59.9: the colength error polynomial is eventually nonnegative and bounded
above by the backward translate-difference of `P'`. -/
lemma eventually_colength_error_nonneg_le_backward_translate
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hquot : IsFiniteLength R (M ⧸ N)) {P P' : Polynomial ℚ} (c : ℕ)
    (hc : ∀ᶠ n : ℕ in atTop,
      Module.length R (M ⧸ N) + χ_ I N (n - c) ≤ χ_ I M n ∧
        χ_ I M n ≤ Module.length R (M ⧸ N) + χ_ I N n)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((χ_ I N n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      0 ≤ (Polynomial.C (((Module.length R (M ⧸ N)).toNat : ℚ)) - (P - P')).eval (n : ℚ) ∧
        (Polynomial.C (((Module.length R (M ⧸ N)).toNat : ℚ)) - (P - P')).eval (n : ℚ) ≤
          (P' - P'.comp (Polynomial.X - Polynomial.C (c : ℚ))).eval (n : ℚ) := by
  let Lq : ℚ := ((Module.length R (M ⧸ N)).toNat : ℚ)
  have hlen : Module.length R (M ⧸ N) ≠ ⊤ := by
    simpa [Module.length_ne_top_iff] using hquot
  have hP'back :
      ∀ᶠ n : ℕ in atTop,
        P'.eval ((n - c : ℕ) : ℚ) = ((χ_ I N (n - c)).toNat : ℚ) := by
    exact (tendsto_sub_atTop_nat c).eventually hP'
  filter_upwards [hP, hP', hP'back, hc, Filter.eventually_ge_atTop c] with
      n hPN hP'N hP'backN hcN hnc
  have hχMn : χ_ I M n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI n
  have hχNn : χ_ I N n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := N) I hI n
  have hχNback : χ_ I N (n - c) ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := N) I hI (n - c)
  have hUpperNat :
      (χ_ I M n).toNat ≤ (Module.length R (M ⧸ N)).toNat + (χ_ I N n).toNat := by
    -- The upper `ENat`-bound gives nonnegativity of the colength error.
    have hsum_ne : Module.length R (M ⧸ N) + χ_ I N n ≠ ⊤ := by
      lift Module.length R (M ⧸ N) to ℕ using hlen with m
      lift χ_ I N n to ℕ using hχNn with k
      intro htop
      have : (((m + k : ℕ) : ℕ∞) = ⊤) := by simpa using htop
      exact ENat.coe_ne_top (m + k) this
    have hUpperToNat := ENat.toNat_le_toNat hcN.2 hsum_ne
    simpa [ENat.toNat_add hlen hχNn] using hUpperToNat
  have hLowerNat :
      (Module.length R (M ⧸ N)).toNat + (χ_ I N (n - c)).toNat ≤ (χ_ I M n).toNat := by
    -- The lower `ENat`-bound controls the error by the backward translate of `P'`.
    have hLowerToNat := ENat.toNat_le_toNat hcN.1 hχMn
    simpa [ENat.toNat_add hlen hχNback] using hLowerToNat
  have hUpperRat :
      ((χ_ I M n).toNat : ℚ) ≤ Lq + ((χ_ I N n).toNat : ℚ) := by
    have :
        ((χ_ I M n).toNat : ℚ) ≤
          (((Module.length R (M ⧸ N)).toNat : ℚ) + ((χ_ I N n).toNat : ℚ)) := by
      exact_mod_cast hUpperNat
    simpa [Lq] using this
  have hLowerRat :
      Lq + ((χ_ I N (n - c)).toNat : ℚ) ≤ ((χ_ I M n).toNat : ℚ) := by
    have :
        (((Module.length R (M ⧸ N)).toNat : ℚ) + ((χ_ I N (n - c)).toNat : ℚ)) ≤
          ((χ_ I M n).toNat : ℚ) := by
      exact_mod_cast hLowerNat
    simpa [Lq] using this
  have hUpperEval :
      P.eval (n : ℚ) ≤ Lq + P'.eval (n : ℚ) := by
    rw [hPN, hP'N]
    exact hUpperRat
  have hLowerEval :
      Lq + P'.eval ((n - c : ℕ) : ℚ) ≤ P.eval (n : ℚ) := by
    rw [hPN, hP'backN]
    exact hLowerRat
  have hEval :
      (Polynomial.C Lq - (P - P')).eval (n : ℚ) =
        Lq - (P.eval (n : ℚ) - P'.eval (n : ℚ)) := by
    -- Expand the error polynomial at `n`.
    simp [sub_eq_add_neg, add_comm]
  have hBackwardEval :
      (P' - P'.comp (Polynomial.X - Polynomial.C (c : ℚ))).eval (n : ℚ) =
        P'.eval (n : ℚ) - P'.eval ((n - c : ℕ) : ℚ) := by
    -- Evaluate the backward translate using the eventual threshold `c ≤ n`.
    simp [Polynomial.eval_comp, Polynomial.eval_X, Nat.cast_sub hnc, sub_eq_add_neg, add_comm]
  constructor
  · -- The upper bound says `P - P'` never exceeds the quotient length.
    rw [hEval]
    linarith
  · -- Combining the upper and lower bounds compares the error to a backward translate of `P'`.
    rw [hEval, hBackwardEval]
    linarith

/-- Helper for Lemma 10.59.9: adding a lower-degree polynomial and then subtracting a constant
does not change the dominating degree. -/
lemma degree_add_sub_const_eq_of_lt {A D : Polynomial ℚ} {b : ℚ}
    (hA : A.degree < D.degree) (hD : 0 < D.degree) :
    (A + D - Polynomial.C b).degree = D.degree := by
  -- First the dominating summand `D` controls the degree of `A + D`.
  have hAD : (A + D).degree = D.degree := by
    exact Polynomial.degree_add_eq_right_of_degree_lt hA
  have hC : (Polynomial.C b).degree < (A + D).degree := by
    -- Constants have degree at most `0`, which is still below the positive degree of `D`.
    rw [hAD]
    exact lt_of_le_of_lt Polynomial.degree_C_le hD
  -- Subtracting a constant preserves the same dominant degree.
  rw [Polynomial.degree_sub_eq_left_of_degree_lt hC, hAD]

/-- Lemma 10.59.9: if `R` is a Noetherian local ring, `I` is an ideal of definition, `M` is a
finite `R`-module of infinite length, and `N ⊆ M` has finite colength, then the difference of any
two Hilbert-Samuel polynomials attached to `χ_{I,M}` and `χ_{I,N}` has degree strictly smaller
than the degree of either polynomial. -/
theorem degree_sub_lt_degree_of_finiteColength
    (I : Ideal R) (hI : I.IsIdealOfDefinition) (N : Submodule R M)
    (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N))
    {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((χ_ I N n).toNat : ℚ)) :
    (P - P').degree < P.degree ∧ (P - P').degree < P'.degree := by
  obtain ⟨c, hc⟩ := exists_eventually_hilbertSamuelChi_bounds_of_isFiniteLength_quotient
    I hI N hquot
  let Lq : ℚ := ((Module.length R (M ⧸ N)).toNat : ℚ)
  let D : Polynomial ℚ := P - P'
  let A : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P
  let E₁ : Polynomial ℚ := P.comp (Polynomial.X + Polynomial.C (c : ℚ)) - P' - Polynomial.C Lq
  let E₂ : Polynomial ℚ := Polynomial.C Lq - D
  have hN : ¬ IsFiniteLength R N := by
    exact not_isFiniteLength_of_finiteColength_submodule (R := R) (M := M) N hM hquot
  have hdegP : 0 < P.degree := by
    exact degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
      (R := R) (M := M) I hI hM hP
  have hdegP' : 0 < P'.degree := by
    exact degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
      (R := R) (M := N) I hI hN hP'
  have hTranslate := degree_translate_sub_lt hdegP (c : ℚ)
  have hBackward := degree_translate_sub_lt hdegP' (c : ℚ)
  have hE₁bound :
      ∀ᶠ n : ℕ in atTop, 0 ≤ E₁.eval (n : ℚ) ∧ E₁.eval (n : ℚ) ≤ A.eval (n : ℚ) := by
    -- Package the forward shift from Lemma 10.59.2 into a polynomial inequality.
    simpa [E₁, A, D, Lq] using eventually_shifted_difference_nonneg_le_translate
      (R := R) (M := M) I hI N hquot c hc hP hP'
  have hE₂bound :
      ∀ᶠ n : ℕ in atTop, 0 ≤ E₂.eval (n : ℚ) ∧
        E₂.eval (n : ℚ) ≤ (P' - P'.comp (Polynomial.X - Polynomial.C (c : ℚ))).eval (n : ℚ) := by
    -- Package the backward shift from Lemma 10.59.2 into a second polynomial inequality.
    simpa [E₂, D, Lq] using eventually_colength_error_nonneg_le_backward_translate
      (R := R) (M := M) I hI N hquot c hc hP hP'
  have hE₁deg : E₁.degree < P.degree := by
    -- The first error polynomial is dominated by the translate-difference of `P`.
    exact degree_lt_of_eventually_nonneg_le hE₁bound hTranslate.1
  have hE₂deg : E₂.degree < P'.degree := by
    -- The second error polynomial is dominated by the translate-difference of `P'`.
    exact degree_lt_of_eventually_nonneg_le hE₂bound hBackward.2
  constructor
  · -- If `D` had degree at least that of `P`, then `E₁` would inherit that same degree.
    refine lt_of_not_ge ?_
    intro hPD
    have hA_lt_D : A.degree < D.degree := by
      exact lt_of_lt_of_le hTranslate.1 hPD
    have hDpos : 0 < D.degree := by
      exact lt_of_lt_of_le hdegP hPD
    have hE₁split : E₁ = A + D - Polynomial.C Lq := by
      -- Route correction: isolate the dominant summand `D` before taking degrees.
      dsimp [E₁, A, D]
      ring
    have hE₁eq : E₁.degree = D.degree := by
      rw [hE₁split]
      exact degree_add_sub_const_eq_of_lt hA_lt_D hDpos
    have : D.degree < P.degree := by
      simpa [hE₁eq] using hE₁deg
    exact not_lt_of_ge hPD this
  · -- If `D` had degree at least that of `P'`, then the second error polynomial would too.
    refine lt_of_not_ge ?_
    intro hP'D
    have hDpos : 0 < D.degree := by
      exact lt_of_lt_of_le hdegP' hP'D
    have hC_lt_D : (Polynomial.C Lq).degree < D.degree := by
      exact lt_of_le_of_lt Polynomial.degree_C_le hDpos
    have hE₂eq : E₂.degree = D.degree := by
      simpa [E₂, D] using Polynomial.degree_sub_eq_right_of_degree_lt hC_lt_D
    have : D.degree < P'.degree := by
      simpa [hE₂eq] using hE₂deg
    exact not_lt_of_ge hP'D this

end Ideal

end
