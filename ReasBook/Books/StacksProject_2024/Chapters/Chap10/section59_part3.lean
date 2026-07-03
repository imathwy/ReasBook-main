import Mathlib
import Mathlib.RingTheory.Ideal.IsPrimary
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_10_59_6 (from Chap10) -/
universe u v

open Filter
open IsLocalRing
open scoped BigOperators
open scoped Ideal

section

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

open Ideal

private noncomputable def numericalPolynomialCandidate {r : ℕ} (a : Fin (r + 1) → ℚ) :
    Polynomial ℚ :=
  ∑ i : Fin (r + 1), a i • Polynomial.preHilbertPoly ℚ i i

private theorem numericalPolynomialCandidate_spec {r : ℕ} (a : Fin (r + 1) → ℚ) :
    ∀ᶠ n : ℕ in atTop,
      (numericalPolynomialCandidate a).eval (n : ℚ) =
        ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
  filter_upwards [eventually_ge_atTop r] with n hn
  simp only [numericalPolynomialCandidate, Polynomial.eval_finset_sum, Polynomial.eval_smul,
    zsmul_eq_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add]
  · rw [Nat.sub_add_cancel (le_trans (Nat.lt_succ_iff.mp i.2) hn)]
    simp [Ring.choose_natCast, mul_comm]
  · exact le_trans (Nat.lt_succ_iff.mp i.2) hn

/-- A numerical polynomial on `ℤ` with values `f n.toNat` yields an eventual polynomial
representative on `ℕ`. This is the canonical bridge from Definition 10.58.3 to the ordinary
polynomial used in Definition 10.59.6. -/
theorem IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial {f : ℕ → ℚ}
    (hf : IsNumericalPolynomial (fun n : ℤ ↦ f n.toNat)) :
    ∃ P : Polynomial ℚ, ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = f n := by
  rcases hf with ⟨r, a, h⟩
  refine ⟨numericalPolynomialCandidate a, ?_⟩
  have hNat :
      (fun n : ℕ ↦ f n) =ᶠ[atTop]
        fun n ↦ ∑ i : Fin (r + 1), Ring.choose (n : ℤ) (i : ℕ) • a i := by
    simpa using h.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℤ)) atTop atTop)
  filter_upwards [hNat, numericalPolynomialCandidate_spec a] with n hf' hP
  exact hP.trans hf'.symm

/-- A Hilbert polynomial for `M` over `R` exists. -/
private theorem exists_hilbertPolynomial :
    ∃ P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((φ_ (maximalIdeal R) M n).toNat : ℚ) := by
  let 𝔪 : Ideal R := maximalIdeal R
  let phiFun : ℕ → ℚ := fun n ↦ ((φ_ 𝔪 M n).toNat : ℚ)
  have h𝔪 : 𝔪.IsIdealOfDefinition := by
    change (maximalIdeal R).IsIdealOfDefinition
    exact Ideal.maximalIdeal_isIdealOfDefinition
  have hnum' :
      IsNumericalPolynomial fun n : ℤ ↦ ((φ_ 𝔪 M n.toNat).toNat : ℚ) :=
    hilbertSamuelPhiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition 𝔪 h𝔪
  have hnum : IsNumericalPolynomial (fun n : ℤ ↦ phiFun n.toNat) := by
    simpa [phiFun] using
      hnum'
  rcases IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial hnum with ⟨P, hP⟩
  exact ⟨P, by simpa [𝔪] using hP⟩

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem hilbertPolynomial_unique {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ))
    (hP' : ∀ᶠ n : ℕ in atTop,
      P'.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) :
    P = P' := by
  rcases eventually_atTop.mp (hP.and hP') with ⟨N, hN⟩
  let s : Set ℚ := Set.range fun n : ℕ ↦ ((n + N : ℕ) : ℚ)
  have hs : s.Infinite := Set.infinite_range_of_injective fun m n hmn ↦ by
    have hmn' : (m + N : ℚ) = (n + N : ℚ) := by
      simpa using hmn
    have hmn'' : m + N = n + N := by
      exact_mod_cast hmn'
    exact Nat.add_right_cancel hmn''
  refine Polynomial.eq_of_infinite_eval_eq P P' <| Set.Infinite.mono ?_ hs
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    rcases hN (n + N) (Nat.le_add_left N n) with ⟨hPn, hP'n⟩
    simpa [add_comm] using hPn.trans hP'n.symm

/-- There is a unique Hilbert polynomial for `M` over `R`. -/
private theorem existsUnique_hilbertPolynomial :
    ∃! P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ) := by
  rcases exists_hilbertPolynomial R M with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro P' hP'
  exact hilbertPolynomial_unique R M hP' hP

/-- Definition 10.59.6: the Hilbert polynomial of `M` over `R` is the unique polynomial in `ℚ[t]`
whose values agree with the Hilbert-Samuel function `φ_M` for all sufficiently large `n`. -/
noncomputable def hilbertPolynomial : Polynomial ℚ :=
  Classical.choose <| ExistsUnique.exists <| existsUnique_hilbertPolynomial R M

private theorem hilbertPolynomial_spec :
    ∀ᶠ n : ℕ in atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        ((φ_(maximalIdeal R) M n).toNat : ℚ) :=
  Classical.choose_spec <| ExistsUnique.exists <| existsUnique_hilbertPolynomial R M

/-- The Hilbert polynomial eventually agrees with the Hilbert-Samuel function `φ_M`. -/
theorem hilbertPolynomial_eventuallyEq :
    ∀ᶠ n : ℕ in atTop,
      (hilbertPolynomial R M).eval (n : ℚ) =
        ((φ_(maximalIdeal R) M n).toNat : ℚ) :=
  hilbertPolynomial_spec R M

/-- Any Hilbert polynomial for `M` over `R` is the Hilbert polynomial; equivalently, any
eventual polynomial representative of `φ_M` is the Hilbert polynomial. -/
theorem eq_hilbertPolynomial {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) :
    P = hilbertPolynomial R M :=
  ExistsUnique.unique (existsUnique_hilbertPolynomial R M) hP (hilbertPolynomial_spec R M)

/-- A rational polynomial agrees eventually with `φ_M` if and only if it is the Hilbert
polynomial. -/
@[simp] theorem eventuallyEq_hilbertSamuelPhi_iff_eq_hilbertPolynomial
    (P : Polynomial ℚ) :
    (∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((φ_(maximalIdeal R) M n).toNat : ℚ)) ↔
        P = hilbertPolynomial R M := by
  constructor
  · exact eq_hilbertPolynomial R M
  · rintro rfl
    exact hilbertPolynomial_spec R M

end

/-! ### Lemma_10_59_7 (from Chap10) -/
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

/-! ### Definition_10_59_8 (from Chap10) -/
universe u v w

open Filter IsLocalRing
open scoped Ideal

section

variable (R : Type u) (M : Type v)
variable [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M]

open Ideal

/-- For an ideal of definition `I`, the Hilbert-Samuel `χ`-function of `M` is eventually given by
some polynomial with rational coefficients. -/
theorem exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) :
    ∃ P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ) := by
  exact IsNumericalPolynomial.exists_eventuallyEq_ratPolynomial <|
    hilbertSamuelChiFunctionInt_isNumericalPolynomial_of_isIdealOfDefinition I hI

omit [IsNoetherianRing R] [Module.Finite R M] in
private theorem eventuallyEq_polynomial_unique {f : ℕ → ℚ} {P P' : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = f n)
    (hP' : ∀ᶠ n : ℕ in atTop, P'.eval (n : ℚ) = f n) :
    P = P' := by
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

private theorem existsUnique_hilbertSamuelChiPolynomial :
    ∃! P : Polynomial ℚ,
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ) := by
  rcases exists_hilbertSamuelChiPolynomial_of_isIdealOfDefinition R M
      Ideal.maximalIdeal_isIdealOfDefinition with ⟨P, hP⟩
  refine ⟨P, hP, ?_⟩
  intro P' hP'
  exact eventuallyEq_polynomial_unique hP' hP

/-- The canonical eventual Hilbert-Samuel `χ`-polynomial of `M` over `R`, taken with respect to
the maximal ideal. -/
noncomputable def hilbertSamuelChiPolynomial : Polynomial ℚ :=
  Classical.choose <| ExistsUnique.exists <| existsUnique_hilbertSamuelChiPolynomial R M

private theorem hilbertSamuelChiPolynomial_spec :
    ∀ᶠ n : ℕ in atTop,
      (hilbertSamuelChiPolynomial R M).eval (n : ℚ) =
        ((χ_(maximalIdeal R) M n).toNat : ℚ) :=
  Classical.choose_spec <| ExistsUnique.exists <| existsUnique_hilbertSamuelChiPolynomial R M

/-- The canonical Hilbert-Samuel `χ`-polynomial eventually agrees with the Hilbert-Samuel
`χ`-function of `M` over `R`. -/
theorem hilbertSamuelChiPolynomial_eventuallyEq :
    ∀ᶠ n : ℕ in atTop,
      (hilbertSamuelChiPolynomial R M).eval (n : ℚ) =
        ((χ_(maximalIdeal R) M n).toNat : ℚ) :=
  hilbertSamuelChiPolynomial_spec R M

/-- Any eventual polynomial representative of the Hilbert-Samuel `χ`-function with respect to the
maximal ideal is the canonical Hilbert-Samuel `χ`-polynomial. -/
theorem eq_hilbertSamuelChiPolynomial {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ)) :
    P = hilbertSamuelChiPolynomial R M :=
  ExistsUnique.unique (existsUnique_hilbertSamuelChiPolynomial R M) hP
    (hilbertSamuelChiPolynomial_spec R M)

/-- Definition 10.59.8: for a finite module over a local Noetherian ring, `d(M)` is the degree of
any eventual polynomial representative of the Hilbert-Samuel `χ`-function attached to the maximal
ideal; Lemma 10.59.7 shows that this degree is independent of the chosen representative. -/
noncomputable def hilbertSamuelPolynomialDegree : WithBot ℕ :=
  (hilbertSamuelChiPolynomial R M).degree

/-- If `P` is an eventual polynomial representative of `χ_{I,M}` for an ideal of definition `I`,
then Definition 10.59.8 computes `d(M)` as `P.degree`. -/
theorem hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition {I : Ideal R}
    (hI : I.IsIdealOfDefinition) {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop, P.eval (n : ℚ) = ((χ_ I M n).toNat : ℚ)) :
    hilbertSamuelPolynomialDegree R M = P.degree := by
  have hmax : (maximalIdeal R).IsIdealOfDefinition := Ideal.maximalIdeal_isIdealOfDefinition
  simpa [hilbertSamuelPolynomialDegree] using
    Ideal.hilbertSamuelChi_degree_eq_of_isIdealOfDefinition hmax hI
      (hilbertSamuelChiPolynomial_eventuallyEq R M) hP

/-- Any eventual polynomial representative of the Hilbert-Samuel `χ`-function with respect to the
maximal ideal has degree `d(M)`. -/
theorem hilbertSamuelPolynomialDegree_eq_degree {P : Polynomial ℚ}
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ)) :
    hilbertSamuelPolynomialDegree R M = P.degree := by
  simpa using
    hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition R M
      Ideal.maximalIdeal_isIdealOfDefinition hP

/-- The Hilbert-Samuel degree invariant is preserved by `R`-linear equivalences of finite
modules. -/
theorem hilbertSamuelPolynomialDegree_eq_of_linearEquiv
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    (e : M ≃ₗ[R] N) :
    hilbertSamuelPolynomialDegree R M = hilbertSamuelPolynomialDegree R N := by
  let P := hilbertSamuelChiPolynomial R N
  have hP :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) N n).toNat : ℚ) :=
    hilbertSamuelChiPolynomial_eventuallyEq R N
  have hPM :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((χ_(maximalIdeal R) M n).toNat : ℚ) := by
    filter_upwards [hP] with n hn
    have hchi :
        χ_(maximalIdeal R) M n =
          χ_(maximalIdeal R) N n := by
      simp only [hilbertSamuelChi]
      let P' : Submodule R M := maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M)
      let Q : Submodule R N := maximalIdeal R ^ (n + 1) • (⊤ : Submodule R N)
      have hPQ : P'.map (e : M →ₗ[R] N) = Q := by
        simp [P', Q, Submodule.map_smul'']
      exact LinearEquiv.length_eq (Submodule.Quotient.equiv P' Q e hPQ)
    have hchiNat :
        ((χ_(maximalIdeal R) M n).toNat : ℚ) =
          ((χ_(maximalIdeal R) N n).toNat : ℚ) := by
      simpa using congrArg (fun x : ℕ∞ ↦ (x.toNat : ℚ)) hchi
    exact hn.trans hchiNat.symm
  rw [hilbertSamuelPolynomialDegree_eq_degree R M hPM, hilbertSamuelPolynomialDegree]

/-- The zero-module clause in Definition 10.59.8, with `M = 0` expressed in Lean by
`Subsingleton M`. -/
@[simp] theorem hilbertSamuelPolynomialDegree_eq_bot [Subsingleton M] :
    hilbertSamuelPolynomialDegree R M = (⊥ : WithBot ℕ) := by
  have hdeg : hilbertSamuelPolynomialDegree R M = (0 : Polynomial ℚ).degree :=
    hilbertSamuelPolynomialDegree_eq_degree R M <|
      Eventually.of_forall fun n ↦ by
        haveI :
            Subsingleton (M ⧸ (maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M))) := by
          infer_instance
        simp [hilbertSamuelChi, Module.length_eq_zero]
  rw [hdeg]
  simp

end

/-! ### Lemma_10_59_9 (from Chap10) -/
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
