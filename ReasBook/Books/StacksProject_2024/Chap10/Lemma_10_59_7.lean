import StacksProject_2024.Chap10.Lemma_10_52_8
import StacksProject_2024.Chap10.Definition_10_59_6
import StacksProject_2024.Chap10.Lemma_10_59_2
import StacksProject_2024.Chap10.Lemma_10_59_4
import StacksProject_2024.Chap10.Proposition_10_59_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter IsLocalRing
open scoped Ideal fwdDiff

section

variable {R : Type u} {M : Type v}
variable [CommRing R]
variable [AddCommGroup M] [Module R M]

namespace Ideal

variable [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R M]
variable {I I' : Ideal R} {P P' : Polynomial ℚ}

/-- Helper for Lemma 10.59.7: every Hilbert-Samuel quotient attached to an ideal of definition has
finite length. -/
private lemma isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
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
  -- Finite generation of the quotient lets us invoke the finite-length criterion.
  exact isFiniteLength_of_pow_smul_eq_bot (m := maximalIdeal R)
    (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hpowQ

/-- Helper for Lemma 10.59.7: viewing an ideal multiple of a submodule inside the ambient module
agrees with the intrinsic ideal multiple in the submodule. -/
private lemma submoduleOf_smul_eq_smul_top
    (J : Ideal R) (N : Submodule R M) :
    (J • N).submoduleOf N = (J • (⊤ : Submodule R N)) := by
  -- Pull the ambient scalar multiple back along the subtype of `N`.
  simpa [Submodule.range_subtype] using
    (Submodule.comap_smul'' (f := N.subtype) N.subtype_injective
      (p := N) (I := J) (by simpa [Submodule.range_subtype]))

/-- Helper for Lemma 10.59.7: eventual equality on `ℕ` determines a rational polynomial
uniquely. -/
private lemma eventuallyEq_polynomial_unique_nat {f : ℕ → ℚ} {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = f n)
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = f n) :
    P = P' := by
  -- Evaluate both polynomials on an infinite tail of natural numbers.
  rcases eventually_atTop.mp (hP.and hP') with ⟨N, hN⟩
  let s : Set ℚ := Set.range fun n : ℕ ↦ ((n + N : ℕ) : ℚ)
  have hs : s.Infinite := Set.infinite_range_of_injective fun m n hmn ↦ by
    have hmn' : (m + N : ℚ) = (n + N : ℚ) := by
      simpa using hmn
    have hmn'' : m + N = n + N := by
      exact_mod_cast hmn'
    exact Nat.add_right_cancel hmn''
  refine Polynomial.eq_of_infinite_eval_eq P P' <| Set.Infinite.mono ?_ hs
  intro x hx
  rcases hx with ⟨n, rfl⟩
  rcases hN (n + N) (Nat.le_add_left N n) with ⟨hPn, hP'n⟩
  simpa [add_comm] using hPn.trans hP'n.symm

/-- Helper for Lemma 10.59.7: an eventually nonnegative polynomial bounded above by another
polynomial cannot have larger degree. -/
private lemma degree_le_of_eventually_nonneg_le {E Q : Polynomial ℚ}
    (hbound : ∀ᶠ n : ℕ in atTop,
      0 ≤ E.eval (n : ℚ) ∧ E.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    E.degree ≤ Q.degree := by
  by_contra hEQ
  have hQE : Q.degree < E.degree := lt_of_not_ge hEQ
  have hE0 : E ≠ 0 := Polynomial.ne_zero_of_degree_gt hQE
  have hNoRoot :
      ∀ᶠ n : ℕ in atTop, ¬ E.IsRoot (n : ℚ) := by
    exact tendsto_natCast_atTop_atTop.eventually
      (Polynomial.eventually_atTop_not_isRoot (P := E) hE0)
  have hPos :
      ∀ᶠ n : ℕ in atTop, 0 < E.eval (n : ℚ) := by
    -- Eventual nonnegativity plus eventual nonvanishing forces eventual positivity.
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
    -- The ratio tends to `0`, but eventual positivity and the upper bound force it to be at
    -- least `1`, contradiction.
    filter_upwards [hPos, hSmall, hbound] with n hPosN hSmallN hBoundN
    have hRatioGe : (1 : ℚ) ≤ Q.eval (n : ℚ) / E.eval (n : ℚ) := by
      rw [one_le_div hPosN]
      exact hBoundN.2
    exact (not_le_of_gt hSmallN.2) hRatioGe
  rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
  exact hN N le_rfl

/-- Helper for Lemma 10.59.7: positive-index Hilbert-Samuel `χ` equals the corresponding
`φ`-value plus the predecessor `χ`-value after converting finite lengths to `ℚ`. -/
private lemma hilbertSamuelChi_toNat_eq_hilbertSamuelPhi_toNat_add_pred_of_pos
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {n : ℕ} (hn : 0 < n) :
    ((χ_ I M n).toNat : ℚ) = ((φ_ I M n).toNat : ℚ) + ((χ_ I M (n - 1)).toNat : ℚ) := by
  let N : Submodule R M := I ^ n • (⊤ : Submodule R M)
  let J : Submodule R M := I ^ (n + 1) • (⊤ : Submodule R M)
  have hJN : J ≤ N := by
    -- Powers of an ideal act by a descending chain on `⊤`.
    simpa [J, N] using Submodule.pow_smul_top_le I M (Nat.le_succ n)
  have hphi :
      Module.length R (N ⧸ J.submoduleOf N) = φ_ I M n := by
    -- Identify the successive quotient with the intrinsic `φ`-quotient.
    have hsub :
        J.submoduleOf N = (I • (⊤ : Submodule R N)) := by
      simpa [J, N, pow_succ', mul_smul] using
        submoduleOf_smul_eq_smul_top (R := R) (M := M) I N
    rw [Ideal.hilbertSamuelPhi]
    simpa [N] using congrArg (fun S : Submodule R N ↦ Module.length R (N ⧸ S)) hsub
  have hdecomp :
      χ_ I M n = χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N) := by
    -- Decompose `M / I^(n+1)M` through `M / I^n M`.
    have hchiPred : Module.length R (M ⧸ N) = χ_ I M (n - 1) := by
      have hpred : n - 1 + 1 = n := by
        omega
      rw [Ideal.hilbertSamuelChi]
      dsimp [N]
      rw [hpred]
    have hchi : χ_ I M n = Module.length R (M ⧸ J) := by
      simpa [Ideal.hilbertSamuelChi, J]
    have hlen :
        Module.length R (M ⧸ J) =
          Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := by
      simpa [J, N] using
        (length_quotient_eq_add_length_submodule_quotient_of_le
          (R := R) (M := M) hJN)
    calc
      χ_ I M n = Module.length R (M ⧸ J) := hchi
      _ = Module.length R (M ⧸ N) + Module.length R (N ⧸ J.submoduleOf N) := hlen
      _ = χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N) := by
        rw [hchiPred]
  have hχpred_ne : χ_ I M (n - 1) ≠ ⊤ := by
    -- Ideals of definition give finite length for every adic quotient.
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI (n - 1)
  have hχ_ne : χ_ I M n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := M) I hI n
  have hsucc_ne : Module.length R (N ⧸ J.submoduleOf N) ≠ ⊤ := by
    -- The successor quotient is finite because it is a finite summand of `χ n`.
    intro htop
    have : χ_ I M n = ⊤ := by simpa [hdecomp, htop]
    exact hχ_ne this
  have hnat :
      (χ_ I M n).toNat =
        (χ_ I M (n - 1)).toNat + (φ_ I M n).toNat := by
    -- Apply `ENat.toNat` to the exact length decomposition.
    have hnat' :
        (χ_ I M n).toNat =
          (χ_ I M (n - 1) + Module.length R (N ⧸ J.submoduleOf N)).toNat := by
      exact congrArg ENat.toNat hdecomp
    rw [ENat.toNat_add hχpred_ne hsucc_ne] at hnat'
    simpa [hphi] using hnat'
  have hrat :
      ((χ_ I M n).toNat : ℚ) =
        ((χ_ I M (n - 1)).toNat : ℚ) + ((φ_ I M n).toNat : ℚ) := by
    exact_mod_cast hnat
  simpa [add_comm] using hrat

/-- Helper for Lemma 10.59.7: an eventual `χ`-polynomial produces the corresponding eventual
backward-difference polynomial for `φ`. -/
private lemma eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi
    (I : Ideal R) (hI : I.IsIdealOfDefinition) {Q : Polynomial ℚ}
    (hQ : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
        ((φ_ I M n).toNat : ℚ) := by
  rcases eventually_atTop.mp hQ with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn
  have hnpos : 0 < n := lt_of_lt_of_le (Nat.succ_pos N) hn
  have hQn : Q.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ) := by
    exact hN n (le_trans (Nat.le_succ N) hn)
  have hQpred : Q.eval ((n - 1 : ℕ) : ℚ) = ((χ_ I M (n - 1)).toNat : ℚ) := by
    apply hN (n - 1)
    omega
  have hchi :
      ((χ_ I M n).toNat : ℚ) = ((φ_ I M n).toNat : ℚ) + ((χ_ I M (n - 1)).toNat : ℚ) := by
    exact hilbertSamuelChi_toNat_eq_hilbertSamuelPhi_toNat_add_pred_of_pos
      (R := R) (M := M) I hI hnpos
  have hphi :
      ((φ_ I M n).toNat : ℚ) =
        ((χ_ I M n).toNat : ℚ) - ((χ_ I M (n - 1)).toNat : ℚ) := by
    linarith
  -- Evaluate the backward difference at `n` and rewrite it using the `χ/φ` relation.
  calc
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ)
        = Q.eval (n : ℚ) - Q.eval ((n - 1 : ℕ) : ℚ) := by
          rw [Polynomial.eval_sub, Polynomial.eval_comp]
          simp [hnpos, sub_eq_add_neg]
    _ = ((φ_ I M n).toNat : ℚ) := by
      rw [hQn, hQpred]
      linarith

/-- Helper for Lemma 10.59.7: the first forward difference of a positive-degree polynomial drops
the degree by exactly one. -/
private lemma degree_forward_difference_eq_sub_one_of_degree_pos
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q.comp (Polynomial.X + Polynomial.C 1) - Q).degree = (Q.natDegree - 1 : ℕ) := by
  let D : Polynomial ℚ := Q.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q
  have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
  have hnatPos : 0 < Q.natDegree := by
    rw [Polynomial.degree_eq_natDegree hQ0, Nat.cast_pos] at hQdeg
    exact hQdeg
  have hdegComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree = Q.degree := by
    calc
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree =
          Q.degree * (Polynomial.X + Polynomial.C (1 : ℚ)).degree := by
            exact Polynomial.degree_comp (p := Q) (q := Polynomial.X + Polynomial.C (1 : ℚ)) <| by
              rw [Polynomial.degree_X_add_C (1 : ℚ)]
              decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_add_C (1 : ℚ)]
        simp
  have hlcComp :
      (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).leadingCoeff = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp]
    · rw [Polynomial.leadingCoeff_X_add_C]
      simp
    · rw [Polynomial.natDegree_X_add_C (1 : ℚ)]
      decide
  have hUpperLt' : D.degree < (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).degree := by
    -- The top coefficients cancel after translating by `1`.
    simpa [D] using
      (Polynomial.degree_sub_lt hdegComp
        ((Polynomial.comp_X_add_C_ne_zero_iff (p := Q) (t := (1 : ℚ))).2 hQ0)
        hlcComp)
  have hUpperLt : D.degree < Q.degree := by
    exact hdegComp ▸ hUpperLt'
  have hUpper : D.degree ≤ (Q.natDegree - 1 : ℕ) := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · have hDnat :
          D.natDegree < Q.natDegree := by
        exact (Polynomial.natDegree_lt_iff_degree_lt hD0).2 <| by
          simpa [Polynomial.degree_eq_natDegree hQ0] using hUpperLt
      rw [Polynomial.degree_eq_natDegree hD0]
      exact WithBot.coe_le_coe.2 (Nat.le_pred_of_lt hDnat)
  have hLower : ((Q.natDegree - 1 : ℕ) : WithBot ℕ) ≤ D.degree := by
    -- Compute a nonzero coefficient in degree `natDegree Q - 1`.
    let H : Polynomial ℚ := Polynomial.hasseDeriv (Q.natDegree - 1) Q
    have hcoeffComp :
        (Q.comp (Polynomial.X + Polynomial.C (1 : ℚ))).coeff (Q.natDegree - 1) =
          H.eval (1 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (1 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hcoeffQ :
        Q.coeff (Q.natDegree - 1) = H.eval (0 : ℚ) := by
      simpa [H, Polynomial.taylor_apply] using
        (Polynomial.taylor_coeff (r := (0 : ℚ)) (f := Q) (n := Q.natDegree - 1))
    have hHnat : H.natDegree = 1 := by
      dsimp [H]
      rw [Polynomial.natDegree_hasseDeriv]
      omega
    have hHdeg : H.degree ≤ 1 := by
      exact Polynomial.degree_le_of_natDegree_le (by rw [hHnat]; exact le_rfl)
    have hHshape :
        H = Polynomial.C (H.coeff 1) * Polynomial.X + Polynomial.C (H.coeff 0) := by
      exact Polynomial.eq_X_add_C_of_degree_le_one hHdeg
    have hEvalDiff : H.eval (1 : ℚ) - H.eval (0 : ℚ) = H.coeff 1 := by
      rw [hHshape]
      simp
    have hcoeffH :
        H.coeff 1 = (Q.natDegree : ℚ) * Q.leadingCoeff := by
      dsimp [H]
      rw [Polynomial.hasseDeriv_coeff]
      have hpred : 1 + (Q.natDegree - 1) = Q.natDegree := by
        omega
      have hchoose : (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = Q.natDegree := by
        have hchoose' :
            (1 + (Q.natDegree - 1)).choose (Q.natDegree - 1) = 1 + (Q.natDegree - 1) := by
          simpa [Nat.add_comm, Nat.succ_eq_add_one] using
            Nat.choose_succ_self_right (Q.natDegree - 1)
        rw [hchoose']
        omega
      rw [hchoose, hpred, Polynomial.leadingCoeff]
    have hcoeffNe : D.coeff (Q.natDegree - 1) ≠ 0 := by
      dsimp [D]
      rw [Polynomial.coeff_sub, hcoeffComp, hcoeffQ, hEvalDiff, hcoeffH]
      exact mul_ne_zero
        (by exact_mod_cast Nat.ne_of_gt hnatPos)
        (Polynomial.leadingCoeff_ne_zero.mpr hQ0)
    exact Polynomial.le_degree_of_ne_zero (n := Q.natDegree - 1) hcoeffNe
  change D.degree = (Q.natDegree - 1 : ℕ)
  exact le_antisymm hUpper hLower

/-- Helper for Lemma 10.59.7: the first backward difference of a positive-degree polynomial drops
the degree by exactly one. -/
private lemma degree_backward_difference_eq_sub_one_of_degree_pos
    {Q : Polynomial ℚ} (hQdeg : 0 < Q.degree) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree = (Q.natDegree - 1 : ℕ) := by
  let Q₁ : Polynomial ℚ := Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))
  have hQ₁deg : Q₁.degree = Q.degree := by
    calc
      Q₁.degree = (Q.comp (Polynomial.X - Polynomial.C (1 : ℚ))).degree := by rfl
      _ = Q.degree * (Polynomial.X - Polynomial.C (1 : ℚ)).degree := by
        exact Polynomial.degree_comp (p := Q) (q := Polynomial.X - Polynomial.C (1 : ℚ)) <| by
          rw [Polynomial.degree_X_sub_C (1 : ℚ)]
          decide
      _ = Q.degree := by
        rw [Polynomial.degree_X_sub_C (1 : ℚ)]
        simp
  have hQ₁pos : 0 < Q₁.degree := by
    simpa [hQ₁deg] using hQdeg
  have hQ₁nat : Q₁.natDegree = Q.natDegree := by
    have hQ₁0 : Q₁ ≠ 0 := Polynomial.ne_zero_of_degree_gt hQ₁pos
    have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQdeg
    exact WithBot.coe_eq_coe.mp <| by
      simpa [Polynomial.degree_eq_natDegree hQ₁0, Polynomial.degree_eq_natDegree hQ0] using hQ₁deg
  have hrewrite :
      Q₁.comp (Polynomial.X + Polynomial.C (1 : ℚ)) - Q₁ =
        Q - Q.comp (Polynomial.X - Polynomial.C (1 : ℚ)) := by
    -- Translating `Q(x - 1)` forward by `1` recovers `Q(x)`.
    simp [Q₁, Polynomial.comp_assoc, sub_eq_add_neg, add_left_comm, add_comm]
  rw [← hrewrite, degree_forward_difference_eq_sub_one_of_degree_pos hQ₁pos, hQ₁nat]

/-- Helper for Lemma 10.59.7: a degree-`≤ 0` polynomial has zero backward difference. -/
private lemma degree_backward_difference_eq_bot_of_degree_le_zero
    {Q : Polynomial ℚ} (hQdeg : Q.degree ≤ 0) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree = ⊥ := by
  -- Degree `≤ 0` means `Q` is constant, and constants have zero backward difference.
  rw [Polynomial.eq_C_of_degree_le_zero hQdeg]
  simp

/-- Helper for Lemma 10.59.7: equal `χ`-degrees give equal backward-difference degrees. -/
private lemma degree_sub_comp_X_sub_C_eq_of_degree_eq
    {Q Q' : Polynomial ℚ} (hdeg : Q.degree = Q'.degree) :
    (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree =
      (Q' - Q'.comp (Polynomial.X - Polynomial.C 1)).degree := by
  by_cases hQpos : 0 < Q.degree
  · have hQ'pos : 0 < Q'.degree := by
      simpa [hdeg] using hQpos
    have hnat : Q.natDegree = Q'.natDegree := by
      have hQ0 : Q ≠ 0 := Polynomial.ne_zero_of_degree_gt hQpos
      have hQ'0 : Q' ≠ 0 := Polynomial.ne_zero_of_degree_gt hQ'pos
      exact WithBot.coe_eq_coe.mp <| by
        simpa [Polynomial.degree_eq_natDegree hQ0, Polynomial.degree_eq_natDegree hQ'0] using hdeg
    rw [degree_backward_difference_eq_sub_one_of_degree_pos hQpos,
      degree_backward_difference_eq_sub_one_of_degree_pos hQ'pos, hnat]
  · have hQle : Q.degree ≤ 0 := le_of_not_gt hQpos
    have hQ'le : Q'.degree ≤ 0 := by
      simpa [hdeg] using hQle
    rw [degree_backward_difference_eq_bot_of_degree_le_zero hQle,
      degree_backward_difference_eq_bot_of_degree_le_zero hQ'le]

-- Source/core/bridge triage:
-- * source-facing: the Hilbert-Samuel `χ`- and `φ`-functions attached to an ideal of definition;
-- * core/canonical: Definition 10.59.8's owner invariant `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the current lemmas identify the degree of any eventual polynomial representative,
--   so the later owner invariant does not depend on the chosen ideal of definition.

-- Proof sketch: apply Lemma 10.59.4 to compare the two adic quotient-length functions after
-- linear reindexing in both directions. Once both `χ`-functions are known to be eventually given
-- by polynomials, these eventual inequalities force any two polynomial representatives to have the
-- same degree.
/-- Lemma 10.59.7 (2): for a finite module over a Noetherian local ring, the degree of any
eventual polynomial representative of the Hilbert-Samuel `χ`-function is independent of the chosen
ideal of definition. -/
lemma hilbertSamuelChi_degree_eq_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = ((χ_ I' M n).toNat : ℚ)) :
    P.degree = P'.degree := by
  -- Route correction: compare the two eventual `χ`-polynomials by Lemma 10.59.4's linear
  -- reindexing bounds, then convert those eventual inequalities into degree inequalities.
  rcases exists_eventually_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
      (M := M) hI hI' with ⟨a, ha, hcmp⟩
  let Qa : Polynomial ℚ := P'.comp (Polynomial.C (a : ℚ) * Polynomial.X)
  have hQa :
      ∀ᶠ n : ℕ in atTop, Qa.eval (n : ℚ) = ((χ_ I' M (a * n)).toNat : ℚ) := by
    -- Reindex the eventual polynomial identity for `P'` along `n ↦ a * n`.
    rcases eventually_atTop.mp hP' with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt ha
    have hmul : N ≤ a * n := by
      calc
        N ≤ n := hn
        _ = 1 * n := by simp
        _ ≤ a * n := Nat.mul_le_mul_right n ha1
    simpa [Qa, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hN (a * n) hmul
  have hQaDeg : Qa.degree = P'.degree := by
    have haQ : (a : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt ha
    have hlin : 0 < (Polynomial.C (a : ℚ) * Polynomial.X).degree := by
      rw [Polynomial.degree_C_mul_X haQ]
      decide
    calc
      Qa.degree = (P'.comp (Polynomial.C (a : ℚ) * Polynomial.X)).degree := by rfl
      _ = P'.degree * (Polynomial.C (a : ℚ) * Polynomial.X).degree := by
        rw [Polynomial.degree_comp hlin]
      _ = P'.degree := by
        rw [Polynomial.degree_C_mul_X haQ, mul_one]
  have hPdegLe : P.degree ≤ P'.degree := by
    have hbound :
        ∀ᶠ n : ℕ in atTop, 0 ≤ P.eval (n : ℚ) ∧ P.eval (n : ℚ) ≤ Qa.eval (n : ℚ) := by
      filter_upwards [hP, hQa, hcmp] with n hPn hQan hcmpn
      have hfinite :
          χ_ I' M (a * n) ≠ ⊤ := by
        simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
          isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
            (R := R) (M := M) I' hI' (a * n)
      refine ⟨?_, ?_⟩
      · rw [hPn]
        positivity
      · rw [hPn, hQan]
        exact_mod_cast ENat.toNat_le_toNat hcmpn hfinite
    calc
      P.degree ≤ Qa.degree := degree_le_of_eventually_nonneg_le hbound
      _ = P'.degree := hQaDeg
  rcases exists_eventually_reindex_hilbertSamuelChi_le_of_isIdealOfDefinition
      (M := M) hI' hI with ⟨b, hb, hcmp'⟩
  let Qb : Polynomial ℚ := P.comp (Polynomial.C (b : ℚ) * Polynomial.X)
  have hQb :
      ∀ᶠ n : ℕ in atTop, Qb.eval (n : ℚ) = ((χ_ I M (b * n)).toNat : ℚ) := by
    -- Reindex the eventual polynomial identity for `P` along `n ↦ b * n`.
    rcases eventually_atTop.mp hP with ⟨N, hN⟩
    filter_upwards [eventually_ge_atTop N] with n hn
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
    have hmul : N ≤ b * n := by
      calc
        N ≤ n := hn
        _ = 1 * n := by simp
        _ ≤ b * n := Nat.mul_le_mul_right n hb1
    simpa [Qb, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hN (b * n) hmul
  have hQbDeg : Qb.degree = P.degree := by
    have hbQ : (b : ℚ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hb
    have hlin : 0 < (Polynomial.C (b : ℚ) * Polynomial.X).degree := by
      rw [Polynomial.degree_C_mul_X hbQ]
      decide
    calc
      Qb.degree = (P.comp (Polynomial.C (b : ℚ) * Polynomial.X)).degree := by rfl
      _ = P.degree * (Polynomial.C (b : ℚ) * Polynomial.X).degree := by
        rw [Polynomial.degree_comp hlin]
      _ = P.degree := by
        rw [Polynomial.degree_C_mul_X hbQ, mul_one]
  have hP'degLe : P'.degree ≤ P.degree := by
    have hbound :
        ∀ᶠ n : ℕ in atTop, 0 ≤ P'.eval (n : ℚ) ∧ P'.eval (n : ℚ) ≤ Qb.eval (n : ℚ) := by
      filter_upwards [hP', hQb, hcmp'] with n hP'n hQbn hcmpn
      have hfinite :
          χ_ I M (b * n) ≠ ⊤ := by
        simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
          isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
            (R := R) (M := M) I hI (b * n)
      refine ⟨?_, ?_⟩
      · rw [hP'n]
        positivity
      · rw [hP'n, hQbn]
        exact_mod_cast ENat.toNat_le_toNat hcmpn hfinite
    calc
      P'.degree ≤ Qb.degree := degree_le_of_eventually_nonneg_le hbound
      _ = P.degree := hQbDeg
  exact le_antisymm hPdegLe hP'degLe

-- Proof sketch: first apply the `χ`-degree statement above to the two eventual `χ`-polynomials,
-- obtained from Proposition 10.59.5. Then use the eventual relation
-- `φ_{I,M}(n) = χ_{I,M}(n) - χ_{I,M}(n - 1)` and the finite-difference formula for polynomial
-- degree to transport the same degree equality to the `φ`-functions.
/-- Lemma 10.59.7 (1): for a finite module over a Noetherian local ring, the degree of any
eventual polynomial representative of the Hilbert-Samuel `φ`-function is independent of the chosen
ideal of definition. -/
lemma hilbertSamuelPhi_degree_eq_of_isIdealOfDefinition
    (hI : I.IsIdealOfDefinition) (hI' : I'.IsIdealOfDefinition)
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((φ_ I M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = ((φ_ I' M n).toNat : ℚ)) :
    P.degree = P'.degree := by
  -- Choose eventual `χ`-polynomials supplied by Proposition 10.59.5.
  let chiFun : ℕ → ℚ := fun n ↦ ((χ_ I M n).toNat : ℚ)
  have hnumQ :
      IsNumericalPolynomial fun n : ℤ ↦ chiFun n.toNat := by
    simpa [chiFun] using
    hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
      (R := R) (M := M) (I := I) hI
  rcases IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial hnumQ with ⟨Q, hQ⟩
  let chiFun' : ℕ → ℚ := fun n ↦ ((χ_ I' M n).toNat : ℚ)
  have hnumQ' :
      IsNumericalPolynomial fun n : ℤ ↦ chiFun' n.toNat := by
    simpa [chiFun'] using
    hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition
      (R := R) (M := M) (I := I') hI'
  rcases IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial hnumQ' with ⟨Q', hQ'⟩
  have hdegQQ' :
      Q.degree = Q'.degree := by
    exact hilbertSamuelChi_degree_eq_of_isIdealOfDefinition
      (R := R) (M := M) hI hI' hQ hQ'
  have hBackwardQ :
      ∀ᶠ n : ℕ in atTop,
        (Q - Q.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
          ((φ_ I M n).toNat : ℚ) := by
    exact eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi
      (R := R) (M := M) I hI hQ
  have hBackwardQ' :
      ∀ᶠ n : ℕ in atTop,
        (Q' - Q'.comp (Polynomial.X - Polynomial.C 1)).eval (n : ℚ) =
          ((φ_ I' M n).toNat : ℚ) := by
    exact eventuallyEq_hilbertSamuelPhi_of_eventuallyEq_hilbertSamuelChi
      (R := R) (M := M) I' hI' hQ'
  have hP_eq :
      P = Q - Q.comp (Polynomial.X - Polynomial.C 1) := by
    exact eventuallyEq_polynomial_unique_nat hP hBackwardQ
  have hP'_eq :
      P' = Q' - Q'.comp (Polynomial.X - Polynomial.C 1) := by
    exact eventuallyEq_polynomial_unique_nat hP' hBackwardQ'
  -- Compare the degrees after replacing both `φ`-polynomials by the backward differences of the
  -- chosen `χ`-polynomials.
  calc
    P.degree = (Q - Q.comp (Polynomial.X - Polynomial.C 1)).degree := by
      rw [hP_eq]
    _ = (Q' - Q'.comp (Polynomial.X - Polynomial.C 1)).degree := by
      exact degree_sub_comp_X_sub_C_eq_of_degree_eq hdegQQ'
    _ = P'.degree := by
      rw [hP'_eq]

end Ideal

end
