import Mathlib
import StacksProject_2024.stacks_project.Chap10.«10_69_0_1»
import StacksProject_2024.stacks_project.Chap10.Definition_10_59_8
import StacksProject_2024.stacks_project.Chap10.Definition_10_60_10
import StacksProject_2024.stacks_project.Chap10.Lemma_10_52_8
import StacksProject_2024.stacks_project.Chap10.Proposition_10_60_9
import StacksProject_2024.stacks_project.Chap15.Lemma_15_30_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open IsLocalRing
open scoped Ideal

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Lemma 15.126.7: any eventual polynomial representative of the Hilbert-Samuel
`χ`-function for a parameter ideal has degree equal to the ambient dimension. -/
private theorem parameterIdeal_hilbertSamuelChiPolynomial_degree_eq
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ)) :
    P.degree = d := by
  -- Compare the eventual `χ`-polynomial with the canonical Hilbert-Samuel degree invariant.
  have hdim : ringKrullDim R = d := hx.1
  have hIdef : (parameterIdeal x).IsIdealOfDefinition := hx.2
  rw [← hilbertSamuelPolynomialDegree_eq_degree_of_isIdealOfDefinition R R hIdef hP]
  exact (((local_noetherian_ring_dimension_tfae (R := R) d).out 0 1 rfl rfl).mp hdim)

/-- Helper for Lemma 15.126.7: in dimension `0`, the parameter ideal is `⊥`, so the Hilbert-Samuel
`χ`-function is constant and its leading coefficient is the quotient length itself. -/
private theorem zeroDim_hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal
    (x : Fin 0 → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / (Nat.factorial 0)) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := by
  -- In the zero-dimensional case the empty parameter family generates the zero ideal.
  have hparam : parameterIdeal x = ⊥ := by
    rw [parameterIdeal_eq_span]
    simp
  -- Zero-dimensional Noetherian rings are Artinian, hence have finite length over themselves.
  have hzero : ringKrullDim R = 0 := hx.1
  have hfiniteLength : IsFiniteLength R R := by
    have hdimle : Ring.KrullDimLE 0 R := ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
    have hArt : IsArtinianRing R :=
      (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero).2 ⟨inferInstance, hdimle⟩
    exact (isArtinianRing_iff_isFiniteLength R).mp hArt
  have hconst :
      ∀ᶠ n : ℕ in atTop,
        P.eval (n : ℚ) = ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℚ) := by
    -- After rewriting the parameter ideal to `⊥`, the `χ`-function becomes constant.
    filter_upwards [hP] with n hn
    rw [hparam] at hn
    have hchiENat : χ_(⊥ : Ideal R) R n = Module.length R (R ⧸ (⊥ : Ideal R)) := by
      change Module.length R (R ⧸ ((⊥ : Ideal R) ^ (n + 1) • (⊤ : Submodule R R))) =
        Module.length R (R ⧸ (⊥ : Ideal R))
      have hsub : ((⊥ : Ideal R) ^ (n + 1) • (⊤ : Submodule R R)) = (⊥ : Ideal R) := by
        ext r
        simp
      rw [hsub]
    have hchi :
        ((χ_(⊥ : Ideal R) R n).toNat : ℚ) =
          ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℚ) := by
      simpa using congrArg (fun z : ℕ∞ ↦ (z.toNat : ℚ)) hchiENat
    exact hn.trans hchi
  have hPC : P = Polynomial.C ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℚ) := by
    -- A polynomial that agrees eventually with a constant on an infinite set is that constant.
    rcases eventually_atTop.mp hconst with ⟨N, hN⟩
    let s : Set ℚ := Set.range fun n : ℕ ↦ ((n + N : ℕ) : ℚ)
    have hs : s.Infinite := Set.infinite_range_of_injective fun m n hmn ↦ by
      have hmn' : (m + N : ℚ) = (n + N : ℚ) := by
        simpa using hmn
      have hmn'' : m + N = n + N := by
        exact_mod_cast hmn'
      exact Nat.add_right_cancel hmn''
    refine Polynomial.eq_of_infinite_eval_eq P
      (Polynomial.C ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℚ)) ?_
    refine Set.Infinite.mono ?_ hs
    intro y hy
    rcases hy with ⟨n, rfl⟩
    have := hN (n + N) (Nat.le_add_left N n)
    simpa [Polynomial.eval_C, add_comm] using this
  have hleadC := hlead
  rw [hPC] at hleadC
  rw [Polynomial.leadingCoeff_C] at hleadC
  norm_num at hleadC
  have heqNat : e = (Module.length R (R ⧸ (⊥ : Ideal R))).toNat := by
    exact_mod_cast hleadC.symm
  calc
    (e : ℕ∞) = ((Module.length R (R ⧸ (⊥ : Ideal R))).toNat : ℕ∞) := by
      simp [heqNat]
    _ ≤ Module.length R (R ⧸ (⊥ : Ideal R)) := ENat.coe_toNat_le_self _
    _ = Module.length R (R ⧸ parameterIdeal x) := by
      rw [hparam]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.7: for nested submodules `K ≤ L`, the quotient `L / K` identifies with
the image of `L` inside `M / K`. -/
private noncomputable def quotient_submoduleOf_equiv_image
    {M : Type u} [AddCommGroup M] [Module R M]
    (K L : Submodule R M) :
    (L ⧸ K.submoduleOf L) ≃ₗ[R] L.map K.mkQ :=
  let f : L →ₗ[R] M ⧸ K := K.mkQ.comp L.subtype
  let hk : f.ker = K.submoduleOf L := by
    -- The only elements of `L` mapping to zero in `M / K` are those already lying in `K`.
    ext x
    simp [f, Submodule.submoduleOf]
  let hr : f.range = L.map K.mkQ := by
    -- The image of the induced map is exactly the image of `L` in the ambient quotient.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  (Submodule.quotEquivOfEq _ _ hk.symm).trans
    (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.7: if `K ≤ L`, then the quotient `M / K` has length equal to the sum
of the lengths of `M / L` and `L / K`. -/
private theorem length_quotient_eq_add_length_subquotient
    {M : Type u} [AddCommGroup M] [Module R M]
    (K L : Submodule R M) (hKL : K ≤ L) :
    Module.length R (M ⧸ K) =
      Module.length R (M ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) := by
  let π : M ⧸ K →ₗ[R] M ⧸ L := Submodule.mapQ K L (LinearMap.id) hKL
  have hπsurj : Function.Surjective π := by
    -- Every class modulo `L` is represented by the same element modulo `K`.
    intro y
    refine Quotient.inductionOn' y ?_
    intro x
    refine ⟨Submodule.Quotient.mk x, rfl⟩
  have hker : π.ker = L.map K.mkQ := by
    -- The kernel consists precisely of classes represented by elements of `L`.
    ext y
    refine Quotient.inductionOn' y ?_
    intro x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hxL : x ∈ L := by
        simpa [π] using (Submodule.Quotient.mk_eq_zero L).1 hx
      exact ⟨x, hxL, rfl⟩
    · rintro ⟨z, hzL, hz⟩
      rw [LinearMap.mem_ker]
      rw [← hz]
      exact (Submodule.Quotient.mk_eq_zero L).2 hzL
  have hkerLength :
      Module.length R π.ker = Module.length R (L ⧸ K.submoduleOf L) := by
    -- Replace the kernel by the standard subquotient model `L / K`.
    rw [hker]
    symm
    exact (quotient_submoduleOf_equiv_image (R := R) K L).length_eq
  have hlen :
      Module.length R (M ⧸ K) = Module.length R π.ker + Module.length R (M ⧸ L) := by
    -- This is additivity of length on the short exact sequence
    -- `0 → ker π → M / K → M / L → 0`.
    simpa using
      (Module.length_eq_add_of_exact
        (π.ker.subtype)
        π
        (Submodule.subtype_injective _)
        hπsurj
        (LinearMap.exact_subtype_ker_map π))
  calc
    Module.length R (M ⧸ K) = Module.length R π.ker + Module.length R (M ⧸ L) := hlen
    _ = Module.length R (L ⧸ K.submoduleOf L) + Module.length R (M ⧸ L) := by
      rw [hkerLength]
    _ = Module.length R (M ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) := by
      rw [add_comm]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.7: inside the `(n + 1)`-st stage of the `I`-adic filtration,
multiplication by `I` gives exactly the next stage. -/
private theorem smul_top_eq_submoduleOf_pow_succ
    (I : Ideal R) (n : ℕ) :
    ((I • ⊤ : Submodule R ↥((I ^ (n + 1)) • (⊤ : Submodule R R)))) =
      (((I ^ (n + 2)) • (⊤ : Submodule R R)).submoduleOf
        ((I ^ (n + 1)) • (⊤ : Submodule R R))) := by
  -- Unfold the two descriptions and compare membership back in `R`.
  ext x
  rw [Submodule.mem_smul_top_iff]
  change ((x : R) ∈ I • ((I ^ (n + 1)) • (⊤ : Submodule R R))) ↔
    ((x : R) ∈ (I ^ (n + 2)) • (⊤ : Submodule R R))
  rw [← mul_smul]
  rw [show I * I ^ (n + 1) = I ^ (n + 2) by
    rw [Ideal.mul_comm, ← pow_succ]]

/-- Helper for Lemma 15.126.7: successive Hilbert-Samuel `χ`-values differ by the corresponding
Hilbert-Samuel `φ`-value. -/
private theorem hilbertSamuelChi_succ_eq_add_hilbertSamuelPhi
    (I : Ideal R) (n : ℕ) :
    χ_ I R (n + 1) = χ_ I R n + φ_ I R (n + 1) := by
  -- Compare the consecutive filtration stages `I^(n + 2) • ⊤ ≤ I^(n + 1) • ⊤`.
  let K : Submodule R R := (I ^ (n + 2)) • (⊤ : Submodule R R)
  let L : Submodule R R := (I ^ (n + 1)) • (⊤ : Submodule R R)
  have hKL : K ≤ L := by
    -- Higher powers of an ideal give smaller stages in the adic filtration.
    dsimp [K, L]
    exact Submodule.smul_mono (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) le_rfl
  have hlen :
      Module.length R (R ⧸ K) =
        Module.length R (R ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) :=
    length_quotient_eq_add_length_subquotient (R := R) K L hKL
  -- Apply additivity of length to the short exact sequence
  -- `0 → L / K → R / K → R / L → 0`.
  have hden :
      K.submoduleOf L = (I • (⊤ : Submodule R L)) := by
    dsimp [K, L]
    simpa using (smul_top_eq_submoduleOf_pow_succ I n).symm
  calc
    χ_ I R (n + 1) = Module.length R (R ⧸ K) := by
          simpa [K, Ideal.hilbertSamuelChi]
    _ = Module.length R (R ⧸ L) + Module.length R (L ⧸ K.submoduleOf L) := hlen
    _ = Module.length R (R ⧸ L) + Module.length R (L ⧸ (I • (⊤ : Submodule R L))) := by
          rw [hden]
    _ = χ_ I R n + φ_ I R (n + 1) := by
          simp [L, Ideal.hilbertSamuelChi, Ideal.hilbertSamuelPhi]

/-- Helper for Lemma 15.126.7: the quotients governing the Hilbert-Samuel `χ`- and `φ`-functions
of a parameter ideal have finite length, so their lengths are honest natural numbers. -/
private theorem parameterIdeal_hilbertSamuel_lengths_ne_top
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (n : ℕ) :
    χ_(parameterIdeal x) R n ≠ ⊤ ∧ φ_(parameterIdeal x) R (n + 1) ≠ ⊤ := by
  let I : Ideal R := parameterIdeal x
  have hIdef : I.IsIdealOfDefinition := hx.2
  have hmle : maximalIdeal R ≤ I.radical := by
    simpa [Ideal.IsIdealOfDefinition, I] using hIdef.symm.le
  obtain ⟨c, hc⟩ :
      ∃ c : ℕ, maximalIdeal R ^ c ≤ I := by
    exact Ideal.exists_pow_le_of_le_radical_of_fg hmle
      (Ideal.fg_of_isNoetherianRing (maximalIdeal R))
  constructor
  · -- A suitable power of the maximal ideal kills `R / I^(n + 1)`.
    let N : Submodule R R := (I ^ (n + 1)) • (⊤ : Submodule R R)
    have hpow :
        maximalIdeal R ^ (c * (n + 1)) ≤ I ^ (n + 1) := by
      calc
        maximalIdeal R ^ (c * (n + 1)) = (maximalIdeal R ^ c) ^ (n + 1) := by
          rw [pow_mul]
        _ ≤ I ^ (n + 1) := Ideal.pow_right_mono hc (n + 1)
    have hkill :
        (maximalIdeal R ^ (c * (n + 1)) • (⊤ : Submodule R (R ⧸ N))) = ⊥ := by
      have hann : maximalIdeal R ^ (c * (n + 1)) ≤ Module.annihilator R (R ⧸ N) := by
        exact (Module.isTorsionBySet_iff_subset_annihilator R (R ⧸ N)).mp <| by
          rw [Module.isTorsionBySet_quotient_iff]
          intro y r hr
          change r • y ∈ N
          exact Submodule.smul_mem_smul (hpow hr) (show y ∈ (⊤ : Submodule R R) by simp)
      refine (Submodule.le_annihilator_iff).mp ?_
      simpa [Submodule.annihilator_top] using hann
    have hfinite : IsFiniteLength R (R ⧸ N) :=
      isFiniteLength_of_pow_smul_eq_bot (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hkill
    -- Convert finite length into the required `≠ ⊤` statement for `χ`.
    simpa [Ideal.hilbertSamuelChi, I, N] using
      (Module.length_ne_top_iff.mpr hfinite)
  · -- A power of the maximal ideal also kills the graded quotient defining `φ`.
    let S : Submodule R R := (I ^ (n + 1)) • (⊤ : Submodule R R)
    let T : Submodule R S := (I • (⊤ : Submodule R S))
    have hkill :
        (maximalIdeal R ^ c • (⊤ : Submodule R (S ⧸ T))) = ⊥ := by
      have hann : maximalIdeal R ^ c ≤ Module.annihilator R (S ⧸ T) := by
        exact (Module.isTorsionBySet_iff_subset_annihilator R (S ⧸ T)).mp <| by
          rw [Module.isTorsionBySet_quotient_iff]
          intro y r hr
          change r • y ∈ T
          exact Submodule.smul_mem_smul (hc hr) (show y ∈ (⊤ : Submodule R S) by simp)
      refine (Submodule.le_annihilator_iff).mp ?_
      simpa [Submodule.annihilator_top] using hann
    have hfinite : IsFiniteLength R (S ⧸ T) :=
      isFiniteLength_of_pow_smul_eq_bot (maximalIdeal R)
        (Ideal.fg_of_isNoetherianRing (maximalIdeal R)) hkill
    -- Convert finite length into the required `≠ ⊤` statement for `φ`.
    simpa [Ideal.hilbertSamuelPhi, I, S, T] using
      (Module.length_ne_top_iff.mpr hfinite)

/-- Helper for Lemma 15.126.7: the first difference of an eventual Hilbert-Samuel `χ`-polynomial
agrees eventually with the Hilbert-Samuel `φ`-function. -/
private theorem eventually_eval_succ_sub_eval_eq_hilbertSamuelPhi
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ)) :
    ∀ᶠ n : ℕ in atTop,
      (P.comp (Polynomial.X + 1) - P).eval (n : ℚ) =
        ((φ_(parameterIdeal x) R (n + 1)).toNat : ℚ) := by
  rcases eventually_atTop.mp hP with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  have hχn := hN n hn
  have hχsucc := hN (n + 1) (le_trans hn (Nat.le_succ n))
  rcases parameterIdeal_hilbertSamuel_lengths_ne_top x hx n with ⟨hχfinite, hφfinite⟩
  have hrecNat :
      (χ_(parameterIdeal x) R (n + 1)).toNat =
        (χ_(parameterIdeal x) R n).toNat + (φ_(parameterIdeal x) R (n + 1)).toNat := by
    rw [hilbertSamuelChi_succ_eq_add_hilbertSamuelPhi]
    exact ENat.toNat_add hχfinite hφfinite
  have hrec :
      ((χ_(parameterIdeal x) R (n + 1)).toNat : ℚ) =
        ((χ_(parameterIdeal x) R n).toNat : ℚ) +
          ((φ_(parameterIdeal x) R (n + 1)).toNat : ℚ) := by
    exact_mod_cast hrecNat
  -- Route correction: the old route tried to differentiate `toNat` without finiteness.
  -- Here we first establish finiteness of `χ(n)` and `φ(n + 1)`, then rewrite the difference.
  calc
    (P.comp (Polynomial.X + 1) - P).eval (n : ℚ)
        = P.eval ((n : ℚ) + 1) - P.eval (n : ℚ) := by
          simp [Polynomial.eval_sub, Polynomial.eval_comp]
    _ = ((χ_(parameterIdeal x) R (n + 1)).toNat : ℚ) -
          ((χ_(parameterIdeal x) R n).toNat : ℚ) := by
          have hχsucc' :
              P.eval ((n : ℚ) + 1) = ((χ_(parameterIdeal x) R (n + 1)).toNat : ℚ) := by
            simpa using hχsucc
          rw [hχsucc', hχn]
    _ = ((φ_(parameterIdeal x) R (n + 1)).toNat : ℚ) := by
          linarith [hrec]

/-- Helper for Lemma 15.126.7: the Hilbert-Samuel `φ`-function is the length of the degree-`n`
associated graded piece `I^n / I^(n + 1)`. -/
private theorem hilbertSamuelPhi_eq_length_associatedGradedPiece
    (I : Ideal R) (n : ℕ) :
    φ_ I R n = Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R n) := by
  let S : Submodule R R := (I ^ n) • (⊤ : Submodule R R)
  let T : Submodule R S := I • (⊤ : Submodule R S)
  have hT :
      T = (((I ^ (n + 1)) • (⊤ : Submodule R R)).submoduleOf S) := by
    -- Compare the two denominator descriptions inside the ambient ring `R`.
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ I • (⊤ : Submodule R S) := by
        simpa [T] using hx
      rw [Submodule.mem_smul_top_iff] at hx'
      have hx'' : ((x : R) ∈ I • ((I ^ n) • (⊤ : Submodule R R))) := by
        simpa [S] using hx'
      simpa [pow_succ, Ideal.mul_comm, mul_smul] using hx''
    · intro x hx
      have hx' : ((x : R) ∈ (I ^ (n + 1)) • (⊤ : Submodule R R)) := by
        simpa using hx
      have hx'' : ((x : R) ∈ I • ((I ^ n) • (⊤ : Submodule R R))) := by
        simpa [pow_succ, Ideal.mul_comm, mul_smul] using hx'
      have hxS : ((x : R) ∈ I • S) := by
        simpa [S] using hx''
      have hxT : x ∈ I • (⊤ : Submodule R S) := by
        rw [Submodule.mem_smul_top_iff]
        exact hxS
      simpa [T] using hxT
  let e : (S ⧸ T) ≃ₗ[R] RingTheory.Sequence.idealAssociatedGradedPiece I R n :=
    Submodule.quotEquivOfEq _ _ hT
  -- Replace the internal quotient model in `Ideal.hilbertSamuelPhi` by the textbook graded piece.
  simpa [Ideal.hilbertSamuelPhi, S, T] using e.length_eq

/-- Helper for Lemma 15.126.7: for a degree-`d` polynomial, the coefficient of `X^(d - 1)` in the
first difference `P(X + 1) - P(X)` is `d` times the leading coefficient of `P`. -/
private theorem firstDifference_coeff_pred_eq_mul_leadingCoeff
    {d : ℕ} (P : Polynomial ℚ)
    (hdeg : P.degree = d) (hd : 0 < d) :
    (P.comp (Polynomial.X + 1) - P).coeff (d - 1) = (d : ℚ) * P.leadingCoeff := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  have hnat : P.natDegree = k + 1 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hcoeff_nat : P.coeff (k + 1) = P.leadingCoeff := by
    simpa [hnat] using (Polynomial.coeff_natDegree (p := P))
  have hcoeff_nat' : P.coeff (1 + k) = P.leadingCoeff := by
    simpa [add_comm] using hcoeff_nat
  let a : ℚ := ((k : ℚ) + 1) * P.leadingCoeff
  let H : Polynomial ℚ := Polynomial.hasseDeriv k P
  have hH : H = Polynomial.C (P.coeff k) + Polynomial.monomial 1 a := by
    -- The `k`-th Hasse derivative keeps only the top two coefficients of a degree-`k + 1`
    -- polynomial, so it becomes affine.
    apply Polynomial.ext
    intro n
    rcases n with _ | _ | n
    · simp [H, Polynomial.hasseDeriv_coeff, a]
    · have hchooseNat : (1 + k).choose k = k + 1 := by
        simpa [add_comm] using Nat.choose_succ_self_right k
      have hchooseRat : (↑((1 + k).choose k) : ℚ) = (k : ℚ) + 1 := by
        norm_num [hchooseNat]
      simp [H, Polynomial.hasseDeriv_coeff, a, hchooseRat, hcoeff_nat']
    · have hdegH : H.natDegree ≤ 1 := by
        simpa [H, hnat] using Polynomial.natDegree_hasseDeriv_le P k
      have hzero : H.coeff (n + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt <| lt_of_le_of_lt hdegH (by omega)
      have hz : ¬ n + 2 = 0 := by
        omega
      have hone : ¬ 1 = n + 2 := by
        omega
      have hrhszero : (Polynomial.C (P.coeff k) + Polynomial.monomial 1 a).coeff (n + 2) = 0 := by
        simp [Polynomial.coeff_add, Polynomial.coeff_monomial]
      simpa using hzero.trans hrhszero.symm
  have htaylor : (Polynomial.taylor (1 : ℚ)) P = P.comp (Polynomial.X + 1) := by
    simpa using (Polynomial.taylor_apply (1 : ℚ) P)
  have hEvalH : Polynomial.eval 1 H = P.coeff k + a := by
    -- Evaluating the affine Hasse derivative at `1` gives the coefficient of `X^k` in `P(X + 1)`.
    rw [hH]
    simp [Polynomial.eval_add, Polynomial.eval_monomial, a]
  have hcompCoeff : (P.comp (Polynomial.X + 1)).coeff k = P.coeff k + a := by
    rw [← htaylor, Polynomial.taylor_coeff]
    simpa [H] using hEvalH
  have hcoeff : (P.comp (Polynomial.X + 1) - P).coeff k = a := by
    -- Subtracting the original `k`-th coefficient removes the lower-order contribution.
    rw [Polynomial.coeff_sub, hcompCoeff]
    ring
  simpa [a] using hcoeff

/-- Helper for Lemma 15.126.7: the parameter ideal generated by a finite family agrees with the
list-generated ideal obtained from the same family. -/
private theorem parameterIdeal_eq_ofList_ofFn
    {d : ℕ} (x : Fin d → maximalIdeal R) :
    parameterIdeal x = Ideal.ofList (List.ofFn fun i ↦ (x i : R)) := by
  -- Rewrite both ideal presentations as the span of the same finite range.
  rw [parameterIdeal_eq_span, Ideal.ofList_ofFn_eq_span_range]

/-- Helper for Lemma 15.126.7: under `Finsupp.equivFunOnFinite`, the degree condition on a
finitely supported function is the usual sum condition on an honest finite tuple. -/
private theorem degree_n_finsupp_eq_sum_iff
    {d n : ℕ} (e : Fin d →₀ ℕ) :
    e.degree = n ↔ ∑ i, Finsupp.equivFunOnFinite e i = n := by
  -- This is the canonical bridge from total degree to stars-and-bars counting.
  exact Iff.of_eq <| by
    simpa using congrArg (fun m : ℕ ↦ m = n) (Finsupp.degree_eq_sum e)

/-- Helper for Lemma 15.126.7: degree-`n` monomials in `d` variables are canonically indexed by
the `n`-th symmetric power of `Fin d`. -/
private noncomputable def degree_n_finsupp_equiv_sym (d n : ℕ) :
    {e : Fin d →₀ ℕ // e.degree = n} ≃ Sym (Fin d) n :=
  (Finsupp.equivFunOnFinite.subtypeEquiv
    (degree_n_finsupp_eq_sum_iff (d := d) (n := n))).trans
    (Sym.equivNatSumOfFintype (Fin d) n).symm

/-- Helper for Lemma 15.126.7: the degree-`n` monomial index set inherits a canonical finite type
structure from the symmetric-power model. -/
@[reducible]
private noncomputable def degree_n_finsupp_fintype (d n : ℕ) :
    Fintype {e : Fin d →₀ ℕ // e.degree = n} :=
  Fintype.ofEquiv (Sym (Fin d) n) (degree_n_finsupp_equiv_sym d n).symm

/-- Helper for Lemma 15.126.7: the degree-`n` monomials in `d` variables are counted by the
stars-and-bars binomial coefficient. -/
private theorem degree_n_parameter_monomial_count_eq_choose
    {d : ℕ} (hd : 0 < d) (n : ℕ)
    [Fintype {e : Fin d →₀ ℕ // e.degree = n}] :
    Fintype.card {e : Fin d →₀ ℕ // e.degree = n} = Nat.choose (n + d - 1) (d - 1) := by
  classical
  let eS := degree_n_finsupp_equiv_sym d n
  letI : Fintype (Sym (Fin d) n) := inferInstance
  have hle : n ≤ n + d - 1 := by
    omega
  calc
    Fintype.card {e : Fin d →₀ ℕ // e.degree = n}
        = Fintype.card (Sym (Fin d) n) := by
          exact Fintype.card_congr eS
    _ = Nat.choose (Fintype.card (Fin d) + n - 1) n := by
      simpa using Sym.card_sym_eq_choose (α := Fin d) (k := n)
    _ = Nat.choose (n + d - 1) (d - 1) := by
      rw [Fintype.card_fin, Nat.add_comm d n]
      have hsub : n + d - 1 - n = d - 1 := by
        omega
      have hchoose :
          Nat.choose (n + d - 1) n = Nat.choose (n + d - 1) (n + d - 1 - n) := by
        exact (Nat.choose_symm hle).symm
      rw [hchoose, hsub]

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.7: length is additive on binary products. -/
private theorem length_prod_eq_add
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] :
    Module.length R (M × N) = Module.length R M + Module.length R N := by
  -- Apply additivity of length to the split short exact sequence `0 → M → M × N → N → 0`.
  simpa using
    (Module.length_eq_add_of_exact
      (LinearMap.inl R M N)
      (LinearMap.snd R M N)
      LinearMap.inl_injective
      LinearMap.snd_surjective
      (Function.Exact.inl_snd : Function.Exact (LinearMap.inl R M N) (LinearMap.snd R M N)))

omit [IsLocalRing R] [IsNoetherianRing R] in
/-- Helper for Lemma 15.126.7: the length of a finite product of copies of one module is the
cardinality of the index set times the length of a single factor. -/
-- TODO: Reprove this by the existing `Fintype.induction_empty_option` route after repairing the
-- reindexing orientation and the final arithmetic normalization in the `Option` step.
private theorem length_finite_pi_eq_card_mul
    {ι : Type u} [Fintype ι] (M : Type u) [AddCommGroup M] [Module R M] :
    Module.length R (ι → M) = Module.length R M * Fintype.card ι := by
  classical
  let P : ∀ (κ : Type u) [Fintype κ], Prop := fun κ _ =>
    ∀ (N : Type u) [AddCommGroup N] [Module R N],
      Module.length R (κ → N) = Module.length R N * Fintype.card κ
  have hP : P ι := by
    refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ ι
    · intro α β _ e hα
      intro N hAdd hMod
      letI : AddCommGroup N := hAdd
      letI : Module R N := hMod
      letI : Fintype α := Fintype.ofEquiv β e.symm
      -- Reindex the finite product along the equivalence and transport the module length.
      calc
        Module.length R (β → N) = Module.length R (α → N) := by
          simpa using
            (LinearEquiv.piCongrLeft R (fun _ : β ↦ N) e).symm.length_eq
        _ = Module.length R N * Fintype.card α := hα N
        _ = Module.length R N * Fintype.card β := by
          simpa using congrArg (fun n : ℕ ↦ Module.length R N * n) (Fintype.card_congr e)
    · intro N hAdd hMod
      letI : AddCommGroup N := hAdd
      letI : Module R N := hMod
      letI : Subsingleton (PEmpty → N) := inferInstance
      -- The empty product is the zero module, so its length is zero.
      simp
    · intro α _ hα
      intro N hAdd hMod
      letI : AddCommGroup N := hAdd
      letI : Module R N := hMod
      -- Split off the distinguished `none` coordinate and apply the induction hypothesis.
      calc
        Module.length R (Option α → N) = Module.length R (N × (α → N)) := by
          simpa using (LinearEquiv.piOptionEquivProd R (M := fun _ : Option α ↦ N)).length_eq
        _ = Module.length R N + Module.length R (α → N) := length_prod_eq_add (R := R)
        _ = Module.length R N + Module.length R N * Fintype.card α := by
          rw [hα N]
        _ = Module.length R N * 1 + Module.length R N * Fintype.card α := by
          rw [mul_one]
        _ = Module.length R N * Fintype.card (Option α) := by
          rw [Fintype.card_option, Nat.cast_add, mul_add]
          simp [add_comm]
  exact hP M

/-- Helper for Lemma 15.126.7: multiplying a finite `ENat` by a natural number stays finite. -/
-- TODO: Restore the inductive proof by combining `mul_add` with the canonical `ENat` lemma that a
-- sum is finite when both summands are finite.
private theorem enat_mul_nat_ne_top (a : ℕ∞) (ha : a ≠ ⊤) (n : ℕ) :
    a * n ≠ ⊤ := by
  rcases ENat.ne_top_iff_exists.mp ha with ⟨m, rfl⟩
  -- Once `a` is a genuine natural number, the product stays finite.
  simpa using (ENat.coe_ne_top (m * n))

/-- Helper for Lemma 15.126.7: finite `ENat` multiplication by a natural number commutes with
`toNat`. -/
private theorem enat_toNat_mul_nat (a : ℕ∞) (ha : a ≠ ⊤) (n : ℕ) :
    (a * n).toNat = a.toNat * n := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      have hmul : a * n ≠ ⊤ := enat_mul_nat_ne_top a ha n
      -- Expand the successor step as repeated addition and then convert to naturals.
      rw [Nat.cast_succ, mul_add, mul_one, ENat.toNat_add hmul ha, ihn]
      ring

/-- Helper for Lemma 15.126.7: an eventual nonnegative polynomial of degree at most `r` has
nonnegative `X^r`-coefficient. -/
-- TODO: Rework the `atBot` contradiction step using the correct eventual-composition lemma for the
-- nat-cast tail, instead of the currently broken `comp_tendsto` field syntax.
private theorem coeff_nonneg_of_eventually_nonneg
    (S : Polynomial ℚ) (r : ℕ)
    (hdeg : S.degree ≤ r)
    (hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.eval (n : ℚ)) :
    0 ≤ S.coeff r := by
  -- Route correction: follow the sign-at-infinity argument directly on the eventual nat tail.
  by_contra hcoeff
  have hcoeff_lt : S.coeff r < 0 := lt_of_not_ge hcoeff
  by_cases hlt : S.degree < r
  · -- If the degree is already `< r`, the `X^r`-coefficient vanishes.
    rw [Polynomial.coeff_eq_zero_of_degree_lt hlt] at hcoeff_lt
    exact lt_irrefl 0 hcoeff_lt
  have hdegEq : S.degree = r := le_antisymm hdeg (le_of_not_gt hlt)
  by_cases hr : r = 0
  · -- Degree `0` means the polynomial is constant, so eventual nonnegativity reads off that value.
    subst hr
    have hconst : S = Polynomial.C (S.coeff 0) :=
      Polynomial.eq_C_of_degree_le_zero hdeg
    have hconstNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.coeff 0 := by
      filter_upwards [hnonneg] with n hn
      rw [hconst] at hn
      simpa using hn
    rcases eventually_atTop.mp hconstNonneg with ⟨N, hN⟩
    exact hcoeff_lt.not_ge (hN N le_rfl)
  have hdegPos : 0 < S.degree := by
    simpa [hdegEq] using (Nat.pos_iff_ne_zero.mpr hr)
  have hnat : S.natDegree = r :=
    Polynomial.natDegree_eq_of_degree_eq_some hdegEq
  have hlead_lt : S.leadingCoeff < 0 := by
    rw [Polynomial.leadingCoeff, hnat]
    exact hcoeff_lt
  have htoBot :
      Tendsto (fun z : ℚ ↦ S.eval z) atTop atBot :=
    S.tendsto_atBot_of_leadingCoeff_nonpos hdegPos hlead_lt.le
  have hnegRat : ∀ᶠ z : ℚ in atTop, S.eval z ≤ (-1 : ℚ) :=
    (tendsto_atBot.1 htoBot) (-1)
  have hnegNat : ∀ᶠ n : ℕ in atTop, S.eval (n : ℚ) < 0 := by
    have hcomp : ∀ᶠ n : ℕ in atTop, S.eval (n : ℚ) ≤ (-1 : ℚ) :=
      tendsto_natCast_atTop_atTop.eventually hnegRat
    filter_upwards [hcomp] with n hn
    linarith
  rcases eventually_atTop.mp (hnonneg.and hnegNat) with ⟨N, hN⟩
  exact (not_lt_of_ge (hN N le_rfl).1 (hN N le_rfl).2).elim

/-- Helper for Lemma 15.126.7: an eventual upper bound by `c * preHilbertPoly` bounds the top
coefficient by `c / r!`. -/
private theorem eventual_preHilbertPoly_upper_bound_coeff_le
    (Q : Polynomial ℚ) (r : ℕ) (c : ℚ)
    (hdeg : Q.degree ≤ r)
    (hbound : ∀ᶠ n : ℕ in atTop,
      Q.eval (n : ℚ) ≤ (Polynomial.C c * Polynomial.preHilbertPoly ℚ r 0).eval (n : ℚ)) :
    Q.coeff r ≤ c / Nat.factorial r := by
  let B : Polynomial ℚ := Polynomial.C c * Polynomial.preHilbertPoly ℚ r 0
  let S : Polynomial ℚ := B - Q
  have hpre_ne : Polynomial.preHilbertPoly ℚ r 0 ≠ 0 := by
    -- The top coefficient of `preHilbertPoly` is `(r!)⁻¹`, so the polynomial is nonzero.
    intro hzero
    have hcoeff_zero : (Polynomial.preHilbertPoly ℚ r 0).coeff r = 0 := by
      simpa [hzero]
    have hfac_ne : ((Nat.factorial r : ℚ)⁻¹) ≠ 0 := by
      exact inv_ne_zero <| by exact_mod_cast Nat.factorial_ne_zero r
    exact hfac_ne <| by
      simpa [Polynomial.coeff_preHilbertPoly_self] using hcoeff_zero
  have hpre_deg : (Polynomial.preHilbertPoly ℚ r 0).degree ≤ r := by
    rw [Polynomial.degree_eq_natDegree hpre_ne, Polynomial.natDegree_preHilbertPoly]
  have hBdeg : B.degree ≤ r := by
    -- Scalar multiplication by a constant cannot raise the degree above `r`.
    simpa [B] using
      (Polynomial.degree_mul_le_of_le
        (p := Polynomial.C c)
        (q := Polynomial.preHilbertPoly ℚ r 0)
        Polynomial.degree_C_le
        hpre_deg)
  have hSdeg : S.degree ≤ r := by
    -- The difference of two degree-`≤ r` polynomials again has degree `≤ r`.
    simpa [S] using
      (Polynomial.degree_sub_le_of_le
        (p := B)
        (q := Q)
        hBdeg
        hdeg)
  have hSnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.eval (n : ℚ) := by
    -- Rewrite the eventual upper bound as eventual nonnegativity of `B - Q`.
    filter_upwards [hbound] with n hn
    simpa [S, B, Polynomial.eval_sub] using sub_nonneg.mpr hn
  have hScoeff_nonneg : 0 ≤ S.coeff r :=
    coeff_nonneg_of_eventually_nonneg S r hSdeg hSnonneg
  have hBcoeff : B.coeff r = c / Nat.factorial r := by
    -- The top coefficient of `C c * preHilbertPoly` is `c * (r!)⁻¹`.
    change (Polynomial.C c * Polynomial.preHilbertPoly ℚ r 0).coeff r =
      c / Nat.factorial r
    rw [Polynomial.coeff_C_mul]
    simpa [div_eq_mul_inv] using congrArg (c * ·) (Polynomial.coeff_preHilbertPoly_self (F := ℚ) r 0)
  have hScoeff : S.coeff r = c / Nat.factorial r - Q.coeff r := by
    change (B - Q).coeff r = c / Nat.factorial r - Q.coeff r
    rw [Polynomial.coeff_sub, hBcoeff]
  linarith

/-- Helper for Lemma 15.126.7: an eventual upper bound by any degree-`≤ r` polynomial with the
expected top coefficient bounds the `X^r`-coefficient of the target polynomial. -/
private theorem eventual_upper_bound_coeff_le_of_degree_and_top_coeff
    (Q B : Polynomial ℚ) (r : ℕ) (c : ℚ)
    (hQdeg : Q.degree ≤ r)
    (hBdeg : B.degree ≤ r)
    (hBcoeff : B.coeff r = c / Nat.factorial r)
    (hbound : ∀ᶠ n : ℕ in atTop, Q.eval (n : ℚ) ≤ B.eval (n : ℚ)) :
    Q.coeff r ≤ c / Nat.factorial r := by
  let S : Polynomial ℚ := B - Q
  have hSdeg : S.degree ≤ r := by
    -- The difference of two degree-`≤ r` polynomials again has degree `≤ r`.
    simpa [S] using
      (Polynomial.degree_sub_le_of_le
        (p := B)
        (q := Q)
        hBdeg
        hQdeg)
  have hSnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ S.eval (n : ℚ) := by
    -- Rewrite the eventual upper bound as eventual nonnegativity of `B - Q`.
    filter_upwards [hbound] with n hn
    simpa [S, Polynomial.eval_sub] using sub_nonneg.mpr hn
  have hScoeff_nonneg : 0 ≤ S.coeff r :=
    coeff_nonneg_of_eventually_nonneg S r hSdeg hSnonneg
  have hScoeff : S.coeff r = c / Nat.factorial r - Q.coeff r := by
    -- Read the top coefficient of `S` from the prescribed top coefficient of `B`.
    change (B - Q).coeff r = c / Nat.factorial r - Q.coeff r
    rw [Polynomial.coeff_sub, hBcoeff]
  linarith

/-- Helper for Lemma 15.126.7: the `n = 0` Hilbert-Samuel `χ`-value of a parameter ideal is the
ordinary quotient length. -/
private theorem parameterIdeal_hilbertSamuelChi_zero_eq_quotient_length
    {d : ℕ} (x : Fin d → maximalIdeal R) :
    χ_(parameterIdeal x) R 0 = Module.length R (R ⧸ parameterIdeal x) := by
  -- Normalize the `n = 0` Hilbert-Samuel quotient to the ordinary quotient by `I`.
  have hsmul :
      ((parameterIdeal x) ^ 1 • (⊤ : Submodule R R)) = (parameterIdeal x : Submodule R R) := by
    ext r
    simp
  change Module.length R (R ⧸ ((parameterIdeal x) ^ 1 • (⊤ : Submodule R R))) =
    Module.length R (R ⧸ parameterIdeal x)
  rw [hsmul]

/-- Helper for Lemma 15.126.7: the quotient by a parameter ideal has finite length. -/
private theorem parameterIdeal_quotient_length_ne_top
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) :
    Module.length R (R ⧸ parameterIdeal x) ≠ ⊤ := by
  -- This is the `n = 0` case of the Hilbert-Samuel `χ`-finiteness statement.
  rw [← parameterIdeal_hilbertSamuelChi_zero_eq_quotient_length (R := R) x]
  exact (parameterIdeal_hilbertSamuel_lengths_ne_top x hx 0).1

/-- Helper for Lemma 15.126.7: a monomial tensor of total degree different from `n` contributes
nothing to the `n`-th associated graded piece of the parameter ideal. -/
-- TODO: Replace this unused tensor-side helper by the direct quotient-level monomial-cover route;
-- the current proof still depends on a stale list-length/index coercion bridge.
private theorem parameterIdeal_degree_n_component_tmul_monomial_zero_of_ne
    {d n : ℕ} (x : Fin d → maximalIdeal R) (m : R) (e : Fin d →₀ ℕ)
    (hdeg : e.degree ≠ n) :
    DirectSum.component
        (R := R ⧸ parameterIdeal x)
        (ι := ℕ)
        (M := RingTheory.Sequence.idealAssociatedGradedPiece (parameterIdeal x) R)
        n
        (RingTheory.Sequence.quasiRegularSequenceAssociatedGradedMap R
          (List.ofFn fun i ↦ (x i : R))
          (Submodule.Quotient.mk m ⊗ₜ[R ⧸ parameterIdeal x]
            MvPolynomial.monomial e (1 : R ⧸ parameterIdeal x))) = 0 := sorry

/-- Helper for Lemma 15.126.7: the missing source-faithful step is the degreewise length bound on
the associated graded pieces of the parameter ideal. -/
-- TODO: Complete the source-faithful monomial-cover argument by repairing the
-- `quasiRegularSequenceAssociatedGradedMap` scalar-compatibility bridge and then reusing the
-- degree-`n` family-map surjectivity already sketched below.
private theorem parameterIdeal_piece_length_le_choose_mul_length
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (hd : 0 < d) (n : ℕ) :
    Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece (parameterIdeal x) R n) ≤
      Module.length R (R ⧸ parameterIdeal x) * Nat.choose (n + d - 1) (d - 1) := sorry

/-- Helper for Lemma 15.126.7: evaluating the shifted degree-`d - 1` pre-Hilbert polynomial gives
the stars-and-bars binomial coefficient `choose (n + d) (d - 1)`. -/
private theorem shifted_parameter_preHilbertPoly_eval
    {d : ℕ} (c : ℚ) (n : ℕ) :
    (((Polynomial.C c * Polynomial.preHilbertPoly ℚ (d - 1) 0).comp
        (Polynomial.X + 1)).eval (n : ℚ)) =
      c * Nat.choose (n + d) (d - 1) := by
  -- Evaluate the shifted `preHilbertPoly` explicitly to recover the stars-and-bars binomial term.
  rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C]
  have hX : (Polynomial.X + 1).eval (n : ℚ) = n + 1 := by
    simp
  rw [hX]
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) (d := d - 1) (k := 0)
    (n := n + 1) (Nat.zero_le _)]
  norm_num
  ring

/-- Helper for Lemma 15.126.7: the first-difference polynomial is eventually bounded above by the
expected multiple of `preHilbertPoly`. -/
-- TODO: After the graded-piece length bound is repaired, restore this step by converting the
-- `ENat` inequality to `ℚ` via the finite-length lemmas and the shifted `preHilbertPoly` formula.
private theorem eventually_first_difference_eval_le_parameter_preHilbert_bound
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (P.comp (Polynomial.X + 1) - P).eval (n : ℚ) ≤
        ((Polynomial.C ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) *
          Polynomial.preHilbertPoly ℚ (d - 1) 0).comp
          (Polynomial.X + 1)).eval (n : ℚ) := by
  let I : Ideal R := parameterIdeal x
  let c : ℕ := (Module.length R (R ⧸ I)).toNat
  have hΔ := eventually_eval_succ_sub_eval_eq_hilbertSamuelPhi x hx P hP
  filter_upwards [hΔ] with n hn
  have hphi_eq :
      ((φ_ I R (n + 1)).toNat : ℚ) =
        ((Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R (n + 1))).toNat : ℚ) := by
    -- Rewrite the Hilbert-Samuel `φ`-value through the associated-graded quotient model.
    exact congrArg (fun z : ℕ∞ ↦ (z.toNat : ℚ))
      (hilbertSamuelPhi_eq_length_associatedGradedPiece (I := I) (n := n + 1))
  have hindex : (n + 1) + d - 1 = n + d := by
    omega
  have hboundENat :
      Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R (n + 1)) ≤
        Module.length R (R ⧸ I) * Nat.choose (n + d) (d - 1) := by
    -- Apply the degree-`n + 1` graded-piece bound and normalize the binomial index.
    simpa [hindex] using parameterIdeal_piece_length_le_choose_mul_length x hx hd (n + 1)
  have hmul_ne_top :
      Module.length R (R ⧸ I) * Nat.choose (n + d) (d - 1) ≠ ⊤ :=
    enat_mul_nat_ne_top _ (parameterIdeal_quotient_length_ne_top x hx) _
  have hboundNat :
      (Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R (n + 1))).toNat ≤
        (Module.length R (R ⧸ I)).toNat * Nat.choose (n + d) (d - 1) := by
    -- Convert the finite `ENat` inequality to an ordinary natural-number inequality.
    simpa [I, enat_toNat_mul_nat _ (parameterIdeal_quotient_length_ne_top x hx)] using
      ENat.toNat_le_toNat hboundENat hmul_ne_top
  have hboundQ :
      ((Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R (n + 1))).toNat : ℚ) ≤
        ((Module.length R (R ⧸ I)).toNat : ℚ) * Nat.choose (n + d) (d - 1) := by
    exact_mod_cast hboundNat
  -- Route correction: bound the first difference via the graded piece, then identify the
  -- stars-and-bars term with the shifted pre-Hilbert polynomial.
  calc
    (P.comp (Polynomial.X + 1) - P).eval (n : ℚ) = ((φ_ I R (n + 1)).toNat : ℚ) := hn
    _ = ((Module.length R (RingTheory.Sequence.idealAssociatedGradedPiece I R (n + 1))).toNat : ℚ) :=
      hphi_eq
    _ ≤ ((Module.length R (R ⧸ I)).toNat : ℚ) * Nat.choose (n + d) (d - 1) := hboundQ
    _ = (((Polynomial.C ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) *
          Polynomial.preHilbertPoly ℚ (d - 1) 0).comp
          (Polynomial.X + 1)).eval (n : ℚ)) := by
          rw [shifted_parameter_preHilbertPoly_eval]

/-- Helper for Lemma 15.126.7: in positive dimension, the source-faithful proof should compare the
first-difference polynomial with the monomial-count bound on the graded pieces
`I^n / I^(n + 1)` for the parameter ideal `I = parameterIdeal x`. -/
private theorem firstDifference_coeff_bound_implies_multiplicity_le_length_quotient_parameterIdeal
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / d.factorial)
    (hd : 0 < d)
    (hcoeffBound :
      (P.comp (Polynomial.X + 1) - P).coeff (d - 1) ≤
        ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) / (Nat.factorial (d - 1))) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := by
  let ΔP : Polynomial ℚ := P.comp (Polynomial.X + 1) - P
  have hdeg : P.degree = d :=
    parameterIdeal_hilbertSamuelChiPolynomial_degree_eq x hx P hP
  have hΔcoeff :
      ΔP.coeff (d - 1) = (d : ℚ) * P.leadingCoeff := by
    -- Compute the first-difference coefficient from the leading term of `P`.
    simpa [ΔP] using firstDifference_coeff_pred_eq_mul_leadingCoeff P hdeg hd
  have hfactorial :
      (d : ℚ) * ((e : ℚ) / d.factorial) = (e : ℚ) / (Nat.factorial (d - 1)) := by
    -- Rewrite `d / d!` as `1 / (d - 1)!` using `d = k + 1`.
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    simp only [Nat.succ_eq_add_one, Nat.succ_sub_one, Nat.factorial_succ, Nat.cast_mul]
    have hk : (((k + 1 : ℕ) : ℚ)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero k)
    field_simp [hk]
  have hq :
      (e : ℚ) / (Nat.factorial (d - 1)) ≤
        ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) / (Nat.factorial (d - 1)) := by
    -- Substitute the normalized multiplicity formula into the coefficient bound.
    calc
      (e : ℚ) / (Nat.factorial (d - 1))
          = (d : ℚ) * ((e : ℚ) / d.factorial) := by rw [hfactorial]
      _ = ΔP.coeff (d - 1) := by rw [hΔcoeff, hlead]
      _ ≤ ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) / (Nat.factorial (d - 1)) :=
        hcoeffBound
  have hfac_pos : (0 : ℚ) < (Nat.factorial (d - 1) : ℚ) := by
    exact_mod_cast Nat.factorial_pos (d - 1)
  have hnat_le_q :
      (e : ℚ) ≤ ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) := by
    -- Clear the common positive denominator.
    have hq' :
        (e : ℚ) ≤
          (((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) /
            (Nat.factorial (d - 1) : ℚ)) *
              (Nat.factorial (d - 1) : ℚ) := by
      exact (div_le_iff₀ hfac_pos).mp hq
    simpa [hfac_pos.ne', div_eq_mul_inv, mul_assoc] using hq'
  have hnat_le :
      e ≤ (Module.length R (R ⧸ parameterIdeal x)).toNat := by
    exact_mod_cast hnat_le_q
  calc
    (e : ℕ∞) ≤ ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℕ∞) := by
      exact ENat.coe_le_coe.mpr hnat_le
    _ ≤ Module.length R (R ⧸ parameterIdeal x) :=
      ENat.coe_toNat_le_self _

/-- Helper for Lemma 15.126.7: the remaining source-faithful frontier is the coefficient bound on
the first difference coming from the monomial-count estimate on the graded pieces of the parameter
ideal. -/
-- TODO: Once the eventual first-difference bound is restored, finish by comparing the top
-- coefficient of `ΔP` with the shifted stars-and-bars polynomial exactly as in the existing
-- skeleton below.
private theorem parameterIdeal_firstDifference_coeff_le_normalized_quotient_length
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hd : 0 < d) :
    (P.comp (Polynomial.X + 1) - P).coeff (d - 1) ≤
      ((Module.length R (R ⧸ parameterIdeal x)).toNat : ℚ) / (Nat.factorial (d - 1)) := sorry

/-- Helper for Lemma 15.126.7: in positive dimension, the source-faithful proof should compare the
first-difference polynomial with the monomial-count bound on the graded pieces
`I^n / I^(n + 1)` for the parameter ideal `I = parameterIdeal x`. -/
private theorem positiveDim_hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / d.factorial)
    (hd : 0 < d) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) :=
  by
  -- Route correction: the `χ`-to-`φ` first-difference bridge and the coefficient arithmetic are
  -- already isolated. The only remaining source blocker is the monomial-count coefficient bound.
  refine firstDifference_coeff_bound_implies_multiplicity_le_length_quotient_parameterIdeal
    x hx P e hP hlead hd ?_
  exact parameterIdeal_firstDifference_coeff_le_normalized_quotient_length x hx P hP hd

-- Proof sketch: let `I = parameterIdeal x`. Proposition 10.59.5 gives an eventual polynomial
-- representative `P` of the rationalized Hilbert-Samuel `χ`-function
-- `n ↦ ((χ_ I R n).toNat : ℚ)`, while the Hilbert-Samuel degree API together with
-- Proposition 10.60.9 identifies the degree of any such representative with `d` from
-- `hx : IsSystemOfParameters x`.
-- Compare the first difference
-- `length_R (R / I^(n + 1)) - length_R (R / I^n)` with the surjective map
-- `⨁_{i₁ + ··· + i_d = n} R / I ⟶ I^n / I^(n + 1)` induced by the monomials
-- `g₁ ^ i₁ * ··· * g_d ^ i_d`; this bounds the degree-`d - 1` leading term by
-- `length_R (R / I) / (d - 1)!`, which is equivalent to `e ≤ Module.length R (R ⧸ I)`.
/-- Lemma 15.126.7: let `(R, 𝔪)` be a Noetherian local ring, let `x` be a system of parameters of
length `d`, and let `I = parameterIdeal x`. If `P` is an eventual polynomial representative of the
canonical rationalized Hilbert-Samuel `χ`-function
`n ↦ ((χ_ I R n).toNat : ℚ)` and has leading
coefficient
`e / d!`, then `(e : ℕ∞) ≤ Module.length R (R ⧸ I)`. -/
theorem hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal_of_isSystemOfParameters
    {d : ℕ} (x : Fin d → maximalIdeal R) (hx : IsSystemOfParameters x) (P : Polynomial ℚ)
    (e : ℕ)
    (hP : ∀ᶠ n : ℕ in atTop,
      P.eval (n : ℚ) = ((χ_(parameterIdeal x) R n).toNat : ℚ))
    (hlead : P.leadingCoeff = (e : ℚ) / d.factorial) :
    (e : ℕ∞) ≤ Module.length R (R ⧸ parameterIdeal x) := by
  -- First lock in the Hilbert-Samuel degree supplied by the parameter-ideal hypothesis.
  have hdeg : P.degree = d :=
    parameterIdeal_hilbertSamuelChiPolynomial_degree_eq x hx P hP
  by_cases hd0 : d = 0
  · -- The zero-dimensional case collapses to a constant Hilbert-Samuel `χ`-function.
    subst hd0
    exact zeroDim_hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal
      x hx P e hP hlead
  · -- For positive dimension, keep the source-faithful graded-piece comparison as the frontier.
    have hd : 0 < d := Nat.pos_iff_ne_zero.mpr hd0
    have _ := hdeg
    exact positiveDim_hilbertSamuelMultiplicity_le_length_quotient_parameterIdeal
      x hx P e hP hlead hd

end
