import StacksProject_2024.Chap10.Lemma_10_59_3
import StacksProject_2024.Chap10.Definition_10_59_8
import StacksProject_2024.Chap10.Lemma_10_59_9
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory Filter Ideal IsLocalRing
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃]

-- Source/core/bridge triage:
-- * source-facing: the first two theorems compare eventual Hilbert-Samuel `χ`-polynomials for the
--   three terms of a short exact sequence with respect to a fixed ideal of definition;
-- * core/canonical: the owner invariant is `hilbertSamuelPolynomialDegree`;
-- * bridge/view: the final theorem passes from the source-facing polynomial comparison to that
--   canonical degree invariant.

variable (I : Ideal R)
variable (P₁ P₂ P₃ : Polynomial ℚ)

/-- Helper for Lemma 10.59.10: eventual agreement on natural-number evaluations determines a
polynomial over `ℚ`. -/
lemma eq_of_eventually_eval_natCast {P Q : Polynomial ℚ}
    (hPQ : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = Q.eval (n : ℚ)) :
    P = Q := by
  rcases eventually_atTop.mp hPQ with ⟨N, hN⟩
  let s : Set ℚ := Set.range fun n : ℕ ↦ ((n + N : ℕ) : ℚ)
  have hs : s.Infinite := Set.infinite_range_of_injective fun m n hmn ↦ by
    have hmn' : (m + N : ℚ) = (n + N : ℚ) := by
      simpa using hmn
    have hmn'' : m + N = n + N := by
      exact_mod_cast hmn'
    exact Nat.add_right_cancel hmn''
  refine Polynomial.eq_of_infinite_eval_eq P Q <| Set.Infinite.mono ?_ hs
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact hN (n + N) (Nat.le_add_left N n)

/-- Helper for Lemma 10.59.10: an eventually nonnegative polynomial bounded above by another
polynomial cannot have larger degree. -/
lemma degree_le_of_eventually_nonneg_le {E Q : Polynomial ℚ}
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
    -- The ratio tends to `0`, but the eventual upper bound forces it to be at least `1`.
    filter_upwards [hPos, hSmall, hbound] with n hPosN hSmallN hBoundN
    have hRatioGe : (1 : ℚ) ≤ Q.eval (n : ℚ) / E.eval (n : ℚ) := by
      rw [one_le_div hPosN]
      exact hBoundN.2
    exact (not_le_of_gt hSmallN.2) hRatioGe
  rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
  exact hN N le_rfl

variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Helper for Lemma 10.59.10: if `M` has finite length, then the eventual Hilbert-Samuel
`χ`-values of `M` are the constant value `Module.length R M`, written in the rational-valued form
used by the polynomial API. -/
lemma eventually_hilbertSamuelChi_toNat_eq_length_of_isFiniteLength
    (hI : I.IsIdealOfDefinition) (hM : IsFiniteLength R M) :
    ∀ᶠ n : ℕ in atTop,
      ((χ_ I M n).toNat : ℚ) = ((Module.length R M).toNat : ℚ) := by
  obtain ⟨c, hc⟩ :=
    exists_pow_maximalIdeal_smul_eq_bot_of_isFiniteLength (R := R) (M := M) hM
  have hIle : I ≤ maximalIdeal R := by
    calc
      I ≤ I.radical := Ideal.le_radical
      _ = maximalIdeal R := hI
  have hkill : (I ^ c • (⊤ : Submodule R M)) = ⊥ := by
    apply le_antisymm
    · calc
        (I ^ c • (⊤ : Submodule R M)) ≤ (maximalIdeal R) ^ c • (⊤ : Submodule R M) := by
          exact Submodule.smul_mono_left (Ideal.pow_right_mono hIle c)
        _ = ⊥ := hc
    · exact bot_le
  filter_upwards [eventually_ge_atTop c] with n hn
  have hpow : (I ^ (n + 1) • (⊤ : Submodule R M)) = ⊥ := by
    apply le_antisymm
    · calc
        (I ^ (n + 1) • (⊤ : Submodule R M)) ≤ I ^ c • (⊤ : Submodule R M) := by
          exact Submodule.pow_smul_top_le I M (Nat.le_trans hn (Nat.le_succ n))
        _ = ⊥ := hkill
    · exact bot_le
  -- Once the denominator is zero, the Hilbert-Samuel quotient is canonically `M` itself.
  calc
    ((χ_ I M n).toNat : ℚ)
        = ((Module.length R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M)))).toNat : ℚ) := by
            rw [Ideal.hilbertSamuelChi]
    _ = ((Module.length R (M ⧸ ⊥)).toNat : ℚ) := by rw [hpow]
    _ = ((Module.length R M).toNat : ℚ) := by
      simpa using congrArg (fun x : ℕ∞ ↦ (x.toNat : ℚ))
        (LinearEquiv.length_eq (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl))

/-- Helper for Lemma 10.59.10: an eventual polynomial representative of a finite-length module is
the corresponding constant polynomial. -/
lemma eq_C_of_eventually_hilbertSamuelChi_of_isFiniteLength {P : Polynomial ℚ}
    (hI : I.IsIdealOfDefinition) (hM : IsFiniteLength R M)
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ)) :
    P = Polynomial.C (((Module.length R M).toNat : ℚ)) := by
  apply eq_of_eventually_eval_natCast
  filter_upwards [hP,
    eventually_hilbertSamuelChi_toNat_eq_length_of_isFiniteLength (R := R) (M := M) I hI hM]
      with n hPn hconst
  simpa using hPn.trans hconst

/-- Helper for Lemma 10.59.10: the shifted short-exact decomposition from Lemma 10.59.3 converts
to an equality of rational-valued eventual Hilbert-Samuel expressions. -/
lemma hilbertSamuelChi_decomposition_toRat {N : Submodule R S.X₁} {c n : ℕ}
    (hI : I.IsIdealOfDefinition) (hquot : IsFiniteLength R (S.X₁ ⧸ N))
    (hdecomp : ∀ m ≥ c,
      χ_ I S.X₂ m =
        χ_ I S.X₃ m + χ_ I N (m - c) + Module.length R (S.X₁ ⧸ N))
    (hn : c ≤ n) :
    ((χ_ I S.X₂ n).toNat : ℚ) =
      ((χ_ I S.X₃ n).toNat : ℚ) + ((χ_ I N (n - c)).toNat : ℚ) +
        (((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)) := by
  have hχ₂ne : χ_ I S.X₂ n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := S.X₂) I hI n
  have hχ₃ne : χ_ I S.X₃ n ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := S.X₃) I hI n
  have hχNne : χ_ I N (n - c) ≠ ⊤ := by
    simpa [Ideal.hilbertSamuelChi, Module.length_ne_top_iff] using
      Ideal.isFiniteLength_hilbertSamuelQuotient_of_isIdealOfDefinition
        (R := R) (M := N) I hI (n - c)
  have hlenne : Module.length R (S.X₁ ⧸ N) ≠ ⊤ := by
    simpa [Module.length_ne_top_iff] using hquot
  have hsumQL_ne : χ_ I N (n - c) + Module.length R (S.X₁ ⧸ N) ≠ ⊤ := by
    exact WithTop.add_ne_top.2 ⟨hχNne, hlenne⟩
  have hNat :
      (χ_ I S.X₂ n).toNat =
        (χ_ I S.X₃ n).toNat + (χ_ I N (n - c)).toNat +
          (Module.length R (S.X₁ ⧸ N)).toNat := by
    have hNat' := congrArg ENat.toNat (hdecomp n hn)
    simpa [ENat.toNat_add hχ₃ne hsumQL_ne, ENat.toNat_add hχNne hlenne, add_assoc] using hNat'
  exact_mod_cast hNat

/-- Helper for Lemma 10.59.10: a module and a finite-colength submodule have eventual
Hilbert-Samuel `χ`-polynomials of the same degree. -/
lemma hilbertSamuelChi_degree_eq_of_finiteColength
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hI : I.IsIdealOfDefinition) {N : Submodule R M}
    (hM : ¬ IsFiniteLength R M) (hquot : IsFiniteLength R (M ⧸ N))
    {P Q : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ))
    (hQ : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) = ((χ_ I N n).toNat : ℚ)) :
    P.degree = Q.degree := by
  have hdeg :=
    Ideal.degree_sub_lt_degree_of_finiteColength
      (R := R) (M := M) I hI N hM hquot hP hQ
  have hPQ : P.degree ≤ Q.degree := by
    by_contra hPQ
    have hQltP : Q.degree < P.degree := lt_of_not_ge hPQ
    have hdegPQ : (P - Q).degree = P.degree := by
      exact Polynomial.degree_sub_eq_left_of_degree_lt hQltP
    have : P.degree < P.degree := by
      simpa [hdegPQ] using hdeg.1
    exact (not_lt_of_ge le_rfl) this
  have hQP : Q.degree ≤ P.degree := by
    by_contra hQP
    have hPltQ : P.degree < Q.degree := lt_of_not_ge hQP
    have hdegPQ : (P - Q).degree = Q.degree := by
      exact Polynomial.degree_sub_eq_right_of_degree_lt hPltQ
    have : Q.degree < Q.degree := by
      simpa [hdegPQ] using hdeg.2
    exact (not_lt_of_ge le_rfl) this
  exact le_antisymm hPQ hQP

-- Proof sketch: use Lemma 10.59.3 to replace `S.X₁` by a finite-colength submodule
-- `N ⊆ S.X₁` and a shift `c` so that `χ_{I,S.X₂} - χ_{I,S.X₃}` is eventually `χ_{I,N}(n - c)` up
-- to a constant. Lemma 10.59.9 compares the Hilbert-Samuel polynomials of `S.X₁` and `N`, and the
-- finite-difference term coming from the shift lowers the degree by one.
/-- Lemma 10.59.10 (1): for a short exact sequence `S` of finite modules, if `P₁`, `P₂`, and `P₃`
are eventual Hilbert-Samuel `χ`-polynomials for `S.X₁`, `S.X₂`, and `S.X₃`, then
`P₂ - P₃ - P₁` is eventually the corresponding difference of `χ`-functions; if `S.X₁` has
infinite length, this difference has degree strictly smaller than `P₁`. -/
@[stacks 00KC]
theorem hilbertSamuelChi_difference_degree_lt_of_shortExact
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : ∀ᶠ n : ℕ in atTop, P₁.eval (n : ℚ) = ((χ_ I S.X₁ n).toNat : ℚ))
    (hP₂ : ∀ᶠ n : ℕ in atTop, P₂.eval (n : ℚ) = ((χ_ I S.X₂ n).toNat : ℚ))
    (hP₃ : ∀ᶠ n : ℕ in atTop, P₃.eval (n : ℚ) = ((χ_ I S.X₃ n).toNat : ℚ))
    (hX₁ : ¬ IsFiniteLength R S.X₁) :
    (∀ᶠ n : ℕ in atTop,
        (P₂ - P₃ - P₁).eval (n : ℚ) =
          ((χ_ I S.X₂ n).toNat : ℚ) -
            ((χ_ I S.X₃ n).toNat : ℚ) -
              ((χ_ I S.X₁ n).toNat : ℚ)) ∧
      (P₂ - P₃ - P₁).degree < P₁.degree := by
  constructor
  · -- The value statement is the direct pointwise subtraction of the three eventual identities.
    filter_upwards [hP₁, hP₂, hP₃] with n h₁ h₂ h₃
    simp [h₁, h₂, h₃, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
  · rcases Ideal.exists_hilbertSamuelChi_decomposition_of_shortExact
        (S := S) I hI hS with ⟨N, c, hquot, hdecomp⟩
    obtain ⟨PN, hPN⟩ :=
      exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition (R := R) (M := N) hI
    let Lq : ℚ := ((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)
    let D : Polynomial ℚ := P₂ - P₃ - PN.comp (Polynomial.X - Polynomial.C (c : ℚ))
    let A : Polynomial ℚ := PN.comp (Polynomial.X - Polynomial.C (c : ℚ)) - PN
    let B : Polynomial ℚ := PN - P₁
    have hN : ¬ IsFiniteLength R N := by
      exact Ideal.not_isFiniteLength_of_finiteColength_submodule
        (R := R) (M := S.X₁) N hX₁ hquot
    have hP₁pos : 0 < P₁.degree := by
      exact Ideal.degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
        (R := R) (M := S.X₁) I hI hX₁ hP₁
    have hPNpos : 0 < PN.degree := by
      exact Ideal.degree_pos_of_eventual_hilbertSamuelChi_of_not_finiteLength
        (R := R) (M := N) I hI hN hPN
    have hdegEq : PN.degree = P₁.degree := by
      exact hilbertSamuelChi_degree_eq_of_finiteColength
        (R := R) (I := I) hI hX₁ hquot hP₁ hPN |>.symm
    have hPNshift :
        ∀ᶠ n : ℕ in atTop,
          PN.eval ((n - c : ℕ) : ℚ) = ((χ_ I N (n - c)).toNat : ℚ) := by
      exact (tendsto_sub_atTop_nat c).eventually hPN
    have hDconstEvent :
        ∀ᶠ n : ℕ in atTop, D.eval (n : ℚ) = Lq := by
      filter_upwards [hP₂, hP₃, hPNshift, Filter.eventually_ge_atTop c] with n h₂ h₃ hNn hn
      have hRat :=
        hilbertSamuelChi_decomposition_toRat (R := R) (S := S) I hI hquot hdecomp hn
      have hEval :
          D.eval (n : ℚ) =
            ((χ_ I S.X₂ n).toNat : ℚ) -
              ((χ_ I S.X₃ n).toNat : ℚ) -
                ((χ_ I N (n - c)).toNat : ℚ) := by
        rw [show D = P₂ - P₃ - PN.comp (Polynomial.X - Polynomial.C (c : ℚ)) by rfl]
        rw [Polynomial.eval_sub, Polynomial.eval_sub, h₂, h₃]
        rw [Polynomial.eval_comp]
        simpa [Nat.cast_sub hn, sub_eq_add_neg] using hNn
      rw [hEval]
      linarith
    have hDconst : D = Polynomial.C Lq := by
      apply eq_of_eventually_eval_natCast
      simpa [D] using hDconstEvent
    have hAdeg' : A.degree < PN.degree := by
      simpa [A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (Ideal.degree_translate_sub_lt (Q := PN) hPNpos (-(c : ℚ))).1
    have hAdeg : A.degree < P₁.degree := by
      simpa [hdegEq] using hAdeg'
    have hBdeg :
        B.degree < P₁.degree := by
      have hBdeg' :
          (P₁ - PN).degree < P₁.degree :=
        (Ideal.degree_sub_lt_degree_of_finiteColength
          (R := R) (M := S.X₁) I hI N hX₁ hquot hP₁ hPN).1
      have hdegNeg : (PN - P₁).degree = (P₁ - PN).degree := by
        rw [show PN - P₁ = -(P₁ - PN) by ring, Polynomial.degree_neg]
      dsimp [B]
      rw [hdegNeg]
      exact hBdeg'
    have hCdeg : (Polynomial.C Lq).degree < P₁.degree := by
      exact lt_of_le_of_lt Polynomial.degree_C_le hP₁pos
    have hCAdeg : (Polynomial.C Lq + A).degree < P₁.degree := by
      calc
        (Polynomial.C Lq + A).degree ≤ max (Polynomial.C Lq).degree A.degree :=
          Polynomial.degree_add_le _ _
        _ < P₁.degree := max_lt hCdeg hAdeg
    have hsplit : P₂ - P₃ - P₁ = Polynomial.C Lq + A + B := by
      -- The decomposition separates the constant term, the translation error, and the colength
      -- comparison term.
      calc
        P₂ - P₃ - P₁ = D + A + B := by
          dsimp [D, A, B]
          ring
        _ = Polynomial.C Lq + A + B := by rw [hDconst]
    rw [hsplit]
    calc
      (Polynomial.C Lq + A + B).degree ≤ max (Polynomial.C Lq + A).degree B.degree :=
        Polynomial.degree_add_le _ _
      _ < P₁.degree := max_lt hCAdeg hBdeg

-- Proof sketch: when `S.X₁` has infinite length, combine the lower-degree error-term statement
-- above with nonnegativity of leading coefficients of Hilbert-Samuel polynomials. When `S.X₁` has
-- finite length, Artin-Rees shows that `χ_{I,S.X₂} - χ_{I,S.X₃}` is eventually constant.
/-- Lemma 10.59.10 (2): for a short exact sequence `S` of finite modules, the degree of any
eventual Hilbert-Samuel `χ`-polynomial for `S.X₂` is the maximum of the corresponding degrees for
`S.X₁` and `S.X₃`. -/
@[stacks 00KC]
theorem hilbertSamuelChi_degree_eq_max_of_shortExact
    (hI : I.IsIdealOfDefinition) (hS : S.ShortExact)
    (hP₁ : ∀ᶠ n : ℕ in atTop, P₁.eval (n : ℚ) = ((χ_ I S.X₁ n).toNat : ℚ))
    (hP₂ : ∀ᶠ n : ℕ in atTop, P₂.eval (n : ℚ) = ((χ_ I S.X₂ n).toNat : ℚ))
    (hP₃ : ∀ᶠ n : ℕ in atTop, P₃.eval (n : ℚ) = ((χ_ I S.X₃ n).toNat : ℚ)) :
    P₂.degree = max P₁.degree P₃.degree := by
  by_cases hX₁ : IsFiniteLength R S.X₁
  · have hP₁const :
        P₁ = Polynomial.C (((Module.length R S.X₁).toNat : ℚ)) := by
      exact eq_C_of_eventually_hilbertSamuelChi_of_isFiniteLength
        (R := R) (M := S.X₁) I hI hX₁ hP₁
    rcases Ideal.exists_hilbertSamuelChi_decomposition_of_shortExact
        (S := S) I hI hS with ⟨N, c, hquot, hdecomp⟩
    have hNfinite : IsFiniteLength R N := by
      exact IsFiniteLength.of_injective hX₁ N.subtype_injective
    let L₁ : ℚ := ((Module.length R S.X₁).toNat : ℚ)
    let LN : ℚ := ((Module.length R N).toNat : ℚ)
    let LQ : ℚ := ((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)
    have hNconst :
        ∀ᶠ n : ℕ in atTop, ((χ_ I N n).toNat : ℚ) = LN := by
      simpa [LN] using eventually_hilbertSamuelChi_toNat_eq_length_of_isFiniteLength
        (R := R) (M := N) I hI hNfinite
    have hNconstShift :
        ∀ᶠ n : ℕ in atTop, ((χ_ I N (n - c)).toNat : ℚ) = LN := by
      exact (tendsto_sub_atTop_nat c).eventually hNconst
    have hlen :
        Module.length R S.X₁ =
          Module.length R N + Module.length R (S.X₁ ⧸ N) := by
      -- The short exact sequence `0 → N → S.X₁ → S.X₁ / N → 0` computes the total length.
      simpa [add_comm] using
        Module.length_eq_add_of_exact N.subtype N.mkQ N.subtype_injective
          N.mkQ_surjective (LinearMap.exact_subtype_mkQ N)
    have hlenN_ne : Module.length R N ≠ ⊤ := by
      simpa [Module.length_ne_top_iff] using hNfinite
    have hlenQ_ne : Module.length R (S.X₁ ⧸ N) ≠ ⊤ := by
      simpa [Module.length_ne_top_iff] using hquot
    have hlenRat : L₁ = LN + LQ := by
      have hNat := congrArg ENat.toNat hlen
      have hNat' :
          (Module.length R S.X₁).toNat =
            (Module.length R N).toNat + (Module.length R (S.X₁ ⧸ N)).toNat := by
        simpa [ENat.toNat_add hlenN_ne hlenQ_ne] using hNat
      change ((Module.length R S.X₁).toNat : ℚ) =
          ((Module.length R N).toNat : ℚ) + ((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)
      exact_mod_cast hNat'
    have hDiffEvent :
        ∀ᶠ n : ℕ in atTop, (P₂ - P₃).eval (n : ℚ) = L₁ := by
      filter_upwards [hP₂, hP₃, hNconstShift, Filter.eventually_ge_atTop c] with
          n h₂ h₃ hNn hn
      have hRat :=
        hilbertSamuelChi_decomposition_toRat (R := R) (S := S) I hI hquot hdecomp hn
      have hEval :
          (P₂ - P₃).eval (n : ℚ) =
            ((χ_ I S.X₂ n).toNat : ℚ) - ((χ_ I S.X₃ n).toNat : ℚ) := by
        simp [h₂, h₃, sub_eq_add_neg]
      rw [hEval]
      linarith
    have hDiff : P₂ - P₃ = P₁ := by
      rw [hP₁const]
      apply eq_of_eventually_eval_natCast
      filter_upwards [hDiffEvent] with n hdiff
      simpa [L₁] using hdiff
    have hP₁le : P₁.degree ≤ P₂.degree := by
      have hbound :
          ∀ᶠ n : ℕ in atTop, 0 ≤ P₁.eval (n : ℚ) ∧ P₁.eval (n : ℚ) ≤ P₂.eval (n : ℚ) := by
        filter_upwards [hP₁, hP₂, hP₃] with n h₁ h₂ h₃
        have h₃nonneg : 0 ≤ P₃.eval (n : ℚ) := by
          rw [h₃]
          exact_mod_cast Nat.zero_le ((χ_ I S.X₃ n).toNat)
        have hDiffEval :
            P₂.eval (n : ℚ) - P₃.eval (n : ℚ) = P₁.eval (n : ℚ) := by
          simpa [Polynomial.eval_sub] using congrArg (fun Q : Polynomial ℚ ↦ Q.eval (n : ℚ)) hDiff
        constructor
        · rw [h₁]
          exact_mod_cast Nat.zero_le ((χ_ I S.X₁ n).toNat)
        · linarith
      exact degree_le_of_eventually_nonneg_le hbound
    have hP₃le : P₃.degree ≤ P₂.degree := by
      have hbound :
          ∀ᶠ n : ℕ in atTop, 0 ≤ P₃.eval (n : ℚ) ∧ P₃.eval (n : ℚ) ≤ P₂.eval (n : ℚ) := by
        filter_upwards [hP₂, hP₃] with n h₂ h₃
        have h₃nonneg : 0 ≤ P₃.eval (n : ℚ) := by
          rw [h₃]
          exact_mod_cast Nat.zero_le ((χ_ I S.X₃ n).toNat)
        have hDiffEval :
            P₂.eval (n : ℚ) - P₃.eval (n : ℚ) = P₁.eval (n : ℚ) := by
          simpa [Polynomial.eval_sub] using congrArg (fun Q : Polynomial ℚ ↦ Q.eval (n : ℚ)) hDiff
        constructor
        · exact h₃nonneg
        · have h₁nonneg : 0 ≤ P₁.eval (n : ℚ) := by
            rw [hP₁const]
            simp [L₁]
          linarith
      exact degree_le_of_eventually_nonneg_le hbound
    have hUpper : P₂.degree ≤ max P₁.degree P₃.degree := by
      have hsplit : P₂ = P₃ + P₁ := by
        calc
          P₂ = (P₂ - P₃) + P₃ := by ring
          _ = P₁ + P₃ := by rw [hDiff]
          _ = P₃ + P₁ := by rw [add_comm]
      rw [hsplit]
      calc
        (P₃ + P₁).degree ≤ max P₃.degree P₁.degree := Polynomial.degree_add_le _ _
        _ = max P₁.degree P₃.degree := by rw [max_comm]
    exact le_antisymm hUpper (max_le hP₁le hP₃le)
  · -- Route correction: instead of a leading-coefficient argument, use the same decomposition as
    -- in part (1) to bound `P₁` and `P₃` directly by `P₂`.
    have hX₁' : ¬ IsFiniteLength R S.X₁ := hX₁
    rcases hilbertSamuelChi_difference_degree_lt_of_shortExact
        (S := S) (I := I) (P₁ := P₁) (P₂ := P₂) (P₃ := P₃)
        hI hS hP₁ hP₂ hP₃ hX₁' with ⟨_, hErrDeg⟩
    rcases Ideal.exists_hilbertSamuelChi_decomposition_of_shortExact
        (S := S) I hI hS with ⟨N, c, hquot, hdecomp⟩
    obtain ⟨PN, hPN⟩ :=
      exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition (R := R) (M := N) hI
    have hdegEq : PN.degree = P₁.degree := by
      exact hilbertSamuelChi_degree_eq_of_finiteColength
        (R := R) (I := I) hI hX₁' hquot hP₁ hPN |>.symm
    have hP₃le : P₃.degree ≤ P₂.degree := by
      have hbound :
          ∀ᶠ n : ℕ in atTop, 0 ≤ P₃.eval (n : ℚ) ∧ P₃.eval (n : ℚ) ≤ P₂.eval (n : ℚ) := by
        filter_upwards [hP₂, hP₃, Filter.eventually_ge_atTop c] with n h₂ h₃ hn
        have hRat :=
          hilbertSamuelChi_decomposition_toRat (R := R) (S := S) I hI hquot hdecomp hn
        constructor
        · rw [h₃]
          exact_mod_cast Nat.zero_le ((χ_ I S.X₃ n).toNat)
        · rw [h₃, h₂]
          have hNnonneg : 0 ≤ ((χ_ I N (n - c)).toNat : ℚ) := by
            exact_mod_cast Nat.zero_le ((χ_ I N (n - c)).toNat)
          have hLnonneg : 0 ≤ (((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)) := by
            exact_mod_cast Nat.zero_le ((Module.length R (S.X₁ ⧸ N)).toNat)
          linarith
      exact degree_le_of_eventually_nonneg_le hbound
    have hP₁le : P₁.degree ≤ P₂.degree := by
      let Q₂ : Polynomial ℚ := P₂.comp (Polynomial.X + Polynomial.C (c : ℚ))
      have hQ₂ :
          ∀ᶠ n : ℕ in atTop, Q₂.eval (n : ℚ) = ((χ_ I S.X₂ (n + c)).toNat : ℚ) := by
        have hShift := (tendsto_add_atTop_nat c).eventually hP₂
        filter_upwards [hShift] with n h₂
        simpa [Q₂, Polynomial.eval_comp, Nat.cast_add, add_assoc, add_comm, add_left_comm] using h₂
      have hbound :
          ∀ᶠ n : ℕ in atTop, 0 ≤ PN.eval (n : ℚ) ∧ PN.eval (n : ℚ) ≤ Q₂.eval (n : ℚ) := by
        filter_upwards [hPN, hQ₂] with n hNn h₂
        have hRat :=
          hilbertSamuelChi_decomposition_toRat (R := R) (S := S) I hI hquot hdecomp
            (Nat.le_add_left c n)
        constructor
        · rw [hNn]
          exact_mod_cast Nat.zero_le ((χ_ I N n).toNat)
        · rw [hNn, h₂]
          have h₃nonneg : 0 ≤ ((χ_ I S.X₃ (n + c)).toNat : ℚ) := by
            exact_mod_cast Nat.zero_le ((χ_ I S.X₃ (n + c)).toNat)
          have hLnonneg : 0 ≤ (((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)) := by
            exact_mod_cast Nat.zero_le ((Module.length R (S.X₁ ⧸ N)).toNat)
          have hNle :
              ((χ_ I N n).toNat : ℚ) ≤ ((χ_ I S.X₂ (n + c)).toNat : ℚ) := by
            have :
                ((χ_ I S.X₂ (n + c)).toNat : ℚ) =
                  ((χ_ I S.X₃ (n + c)).toNat : ℚ) + ((χ_ I N n).toNat : ℚ) +
                    (((Module.length R (S.X₁ ⧸ N)).toNat : ℚ)) := by
              simpa [Nat.add_sub_cancel_left c n] using hRat
            linarith
          linarith
      have hPNleQ₂ : PN.degree ≤ Q₂.degree := degree_le_of_eventually_nonneg_le hbound
      have hQ₂deg : Q₂.degree = P₂.degree := by
        calc
          Q₂.degree = (P₂.comp (Polynomial.X + Polynomial.C (c : ℚ))).degree := by rfl
          _ = P₂.degree * (Polynomial.X + Polynomial.C (c : ℚ)).degree := by
            rw [Polynomial.degree_comp (p := P₂) (q := Polynomial.X + Polynomial.C (c : ℚ))]
            · rw [Polynomial.degree_X_add_C]
              decide
          _ = P₂.degree := by
            rw [Polynomial.degree_X_add_C, mul_one]
      have hPNle : PN.degree ≤ P₂.degree := by
        rw [← hQ₂deg]
        exact hPNleQ₂
      simpa [hdegEq] using hPNle
    have hUpper : P₂.degree ≤ max P₁.degree P₃.degree := by
      have hErrLe : (P₂ - P₃ - P₁).degree ≤ max P₁.degree P₃.degree := by
        exact le_trans (le_of_lt hErrDeg) (le_max_left _ _)
      have hSumLe : (P₃ + P₁).degree ≤ max P₁.degree P₃.degree := by
        calc
          (P₃ + P₁).degree ≤ max P₃.degree P₁.degree := Polynomial.degree_add_le _ _
          _ = max P₁.degree P₃.degree := by rw [max_comm]
      have hsplit : P₂ = (P₂ - P₃ - P₁) + (P₃ + P₁) := by ring
      rw [hsplit]
      exact le_trans (Polynomial.degree_add_le _ _) (max_le hErrLe hSumLe)
    exact le_antisymm hUpper (max_le hP₁le hP₃le)

-- Proof sketch: apply the preceding degree formula to eventual Hilbert-Samuel polynomial
-- representatives, then use Definition 10.59.8's canonical bridge from any eventual polynomial
-- representative of `χ_{I,-}` to the corresponding `d(-)` invariant.
/-- Lemma 10.59.10 (3): if `S : ShortComplex (ModuleCat R)` is short exact with finite terms over a
Noetherian local ring, then the invariant `d(-)` from Definition 10.59.8 satisfies
`d(S.X₂) = max (d(S.X₁), d(S.X₃))`. -/
@[stacks 00KC]
theorem hilbertSamuelPolynomialDegree_eq_max_of_shortExact
    (hS : S.ShortExact) :
    hilbertSamuelPolynomialDegree R S.X₂ =
      max (hilbertSamuelPolynomialDegree R S.X₁) (hilbertSamuelPolynomialDegree R S.X₃) := by
  have hP₁ := hilbertSamuelChiPolynomial_eventuallyEq R S.X₁
  have hP₂ := hilbertSamuelChiPolynomial_eventuallyEq R S.X₂
  have hP₃ := hilbertSamuelChiPolynomial_eventuallyEq R S.X₃
  -- Use the canonical eventual Hilbert-Samuel polynomials from Definition 10.59.8.
  rw [hilbertSamuelPolynomialDegree_eq_degree R S.X₂ hP₂,
    hilbertSamuelPolynomialDegree_eq_degree R S.X₁ hP₁,
    hilbertSamuelPolynomialDegree_eq_degree R S.X₃ hP₃]
  exact hilbertSamuelChi_degree_eq_max_of_shortExact
    (S := S) (I := maximalIdeal R)
    (P₁ := hilbertSamuelChiPolynomial R S.X₁)
    (P₂ := hilbertSamuelChiPolynomial R S.X₂)
    (P₃ := hilbertSamuelChiPolynomial R S.X₃)
    Ideal.maximalIdeal_isIdealOfDefinition hS hP₁ hP₂ hP₃

end
