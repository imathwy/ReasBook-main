import DifferentialForms_Cartan_1970.cartan.IV.section13.«0001_Definition_IV_1_extra_1»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0003_Definition_IV_1_extra_3»
import DifferentialForms_Cartan_1970.cartan.IV.section13.«0004_Proposition_2_I»
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped MvPowerSeries

universe u

variable {𝕜 : Type u}

/-- Helper for Proposition 3.I: the locally finite product order equips `ℕ × ℕ` with the
antidiagonal structure needed for the two-variable Cauchy product. -/
instance pairNat_hasAntidiagonal : Finset.HasAntidiagonal (ℕ × ℕ) :=
  Finset.antidiagonalOfLocallyFinite

namespace MvPowerSeries

open Finsupp

section coeffXY

/-- The coefficient of `X^p Y^q` in a two-variable formal power series. This is the standard
coefficient map on `𝕜⟦X,Y⟧`, viewed through the source-facing `(p, q)` indexing. -/
noncomputable def coeffXY (S : 𝕜⟦X,Y⟧) (p q : ℕ) : 𝕜 :=
  S (single 0 p + single 1 q)

end coeffXY

section sumXY

variable [Semiring 𝕜] [TopologicalSpace 𝕜]

/-- The explicit double-series expansion of a two-variable formal power series at `(z₁, z₂)`. This
is a bridge from the canonical owner `𝕜⟦X,Y⟧` to the source-facing coefficient-sum notation. -/
noncomputable def sumXY (S : 𝕜⟦X,Y⟧) (z : 𝕜 × 𝕜) : 𝕜 :=
  ∑' n : ℕ × ℕ, coeffXY S n.1 n.2 * z.1 ^ n.1 * z.2 ^ n.2

end sumXY

section evalBridge

private noncomputable def pairToFinsupp : ℕ × ℕ ≃ (Fin 2 →₀ ℕ) :=
  { toFun := fun n ↦ Finsupp.ofSupportFinite ![n.1, n.2] (Set.toFinite _)
    invFun := fun d ↦ (d 0, d 1)
    left_inv := fun _ ↦ rfl
    right_inv := fun d ↦ Finsupp.ofSupportFinite_fin_two_eq d }

private theorem pairToFinsupp_apply (n : ℕ × ℕ) :
    pairToFinsupp n = single 0 n.1 + single 1 n.2 := by
  ext i
  fin_cases i <;> simp [pairToFinsupp, Finsupp.ofSupportFinite_coe]

/-- Helper for Proposition 3.I: the equivalence from pairs to two-variable exponent vectors
respects coordinatewise addition. -/
private theorem pairToFinsupp_add (m n : ℕ × ℕ) :
    pairToFinsupp (m + n) = pairToFinsupp m + pairToFinsupp n := by
  -- Both sides encode the same pair of exponents in the two canonical coordinates.
  ext i
  fin_cases i <;> simp [pairToFinsupp_apply, add_comm, add_left_comm, add_assoc]

/-- Helper for Proposition 3.I: the source-facing coefficient `coeffXY` is the canonical
coefficient indexed by the corresponding finitely supported exponent. -/
private theorem coeffXY_eq_coeff_pairToFinsupp [Semiring 𝕜] (S : 𝕜⟦X,Y⟧) (n : ℕ × ℕ) :
    coeffXY S n.1 n.2 = MvPowerSeries.coeff (pairToFinsupp n) S := by
  rw [coeffXY, pairToFinsupp_apply, coeff_apply]

/-- Helper for Proposition 3.I: mapping the pair antidiagonal through `pairToFinsupp` on each
factor recovers the finsupp antidiagonal used by `MvPowerSeries.coeff_mul`. -/
private theorem pairToFinsupp_antidiagonal_map (n : ℕ × ℕ) :
    (Finset.antidiagonal n).map
        (Equiv.prodCongr pairToFinsupp pairToFinsupp).toEmbedding =
      Finset.antidiagonal (pairToFinsupp n) := by
  -- Reindex the pair antidiagonal by transporting the defining equation through `pairToFinsupp`.
  ext uv
  constructor
  · intro huv
    rcases Finset.mem_map.1 huv with ⟨kl, hkl, rfl⟩
    simpa [Finset.mem_antidiagonal, pairToFinsupp_add] using
      congrArg pairToFinsupp (Finset.mem_antidiagonal.1 hkl)
  · intro huv
    have hsum :
        pairToFinsupp (pairToFinsupp.symm uv.1 + pairToFinsupp.symm uv.2) = pairToFinsupp n := by
      simpa [pairToFinsupp_add] using huv
    have hpre : pairToFinsupp.symm uv.1 + pairToFinsupp.symm uv.2 = n := by
      apply pairToFinsupp.injective
      simpa using hsum
    refine Finset.mem_map.2 ?_
    refine ⟨(pairToFinsupp.symm uv.1, pairToFinsupp.symm uv.2), ?_, ?_⟩
    · simpa [Finset.mem_antidiagonal] using hpre
    · simp

/-- Helper for Proposition 3.I: the coefficient of `X^p Y^q` in a product is the two-variable
Cauchy sum over the pair antidiagonal. -/
theorem coeffXY_mul_eq_sum_antidiagonal [Semiring 𝕜] (S T : 𝕜⟦X,Y⟧) (p q : ℕ) :
    coeffXY (S * T) p q =
      ∑ kl ∈ Finset.antidiagonal (p, q),
        coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2 := by
  classical
  -- Transport the canonical finsupp Cauchy product formula back to the source-facing pair index.
  calc
    coeffXY (S * T) p q = MvPowerSeries.coeff (pairToFinsupp (p, q)) (S * T) := by
      simpa using coeffXY_eq_coeff_pairToFinsupp (S := S * T) (n := (p, q))
    _ =
        ∑ kl ∈ Finset.antidiagonal (p, q),
          coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2 := by
          rw [MvPowerSeries.coeff_mul, ← pairToFinsupp_antidiagonal_map (p, q), Finset.sum_map]
          refine Finset.sum_congr rfl fun kl hkl ↦ ?_
          simp [coeffXY_eq_coeff_pairToFinsupp]

variable [NormedCommRing 𝕜] [CompleteSpace 𝕜] [IsLinearTopology 𝕜 𝕜]

/-- In the coefficient ring itself, the source-facing sum `sumXY` agrees with the canonical
algebra evaluation `MvPowerSeries.aeval` under the corresponding `HasEval` hypothesis. -/
theorem sumXY_eq_aeval (S : 𝕜⟦X,Y⟧) (z : 𝕜 × 𝕜)
    (hz : MvPowerSeries.HasEval ![z.1, z.2]) :
    sumXY S z = MvPowerSeries.aeval hz S := by
  rw [sumXY, MvPowerSeries.aeval_eq_sum hz, ← pairToFinsupp.tsum_eq
    (fun d : Fin 2 →₀ ℕ ↦ (coeff d S) • d.prod fun s e ↦ ![z.1, z.2] s ^ e)]
  refine tsum_congr fun n ↦ ?_
  simp [coeffXY, coeff_apply, pairToFinsupp_apply, Fin.prod_univ_two, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm]

/-- The source-facing coefficient sum `sumXY` is the same evaluation as the canonical
`MvPowerSeries.eval₂`, whenever the point `(z₁,z₂)` satisfies the standard `HasEval` hypothesis. -/
theorem sumXY_eq_eval₂ (S : 𝕜⟦X,Y⟧) (z : 𝕜 × 𝕜)
    (hz : MvPowerSeries.HasEval ![z.1, z.2]) :
    sumXY S z = MvPowerSeries.eval₂ (algebraMap 𝕜 𝕜) ![z.1, z.2] S := by
  rw [← MvPowerSeries.coe_aeval hz, sumXY_eq_aeval S z hz]

end evalBridge

end MvPowerSeries

open MvPowerSeries

/-- Helper for Proposition 3.I: membership in the convergence domain gives absolute summability of
the source-facing double-series term norms. -/
theorem summable_norm_sumXY_term_of_mem_domain
    [NormedRing 𝕜] [CompleteSpace 𝕜]
    (S : 𝕜⟦X,Y⟧) {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S)) :
    Summable (fun n : ℕ × ℕ ↦ ‖coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖) := by
  -- Use Proposition 2.I to replace interior membership by larger radii in the convergence locus.
  rcases
      (mem_formalSeriesConvergenceDomain_iff_exists_gt_mem_formalSeriesConvergenceLocus
        (coeffXY S) ‖z₁‖ ‖z₂‖).1 hz with
    ⟨-, -, R₁, hz₁_lt_R₁, R₂, hz₂_lt_R₂, hR⟩
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) (R₁, R₂)).1 hR with
    ⟨hR₁_nonneg, hR₂_nonneg, hsumR⟩
  let C : ℝ := max ‖(1 : 𝕜)‖ 1
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have hsumRC : Summable (fun n : ℕ × ℕ ↦ C * C * (‖coeffXY S n.1 n.2‖ * R₁ ^ n.1 * R₂ ^ n.2)) := by
    simpa [C, mul_assoc, mul_left_comm, mul_comm] using hsumR.mul_left (C * C)
  refine hsumRC.of_nonneg_of_le (fun n ↦ norm_nonneg _) ?_
  intro n
  have hz₁_le_R₁ : ‖z₁‖ ≤ R₁ := le_of_lt hz₁_lt_R₁
  have hz₂_le_R₂ : ‖z₂‖ ≤ R₂ := le_of_lt hz₂_lt_R₂
  have hpow₁ : ‖z₁‖ ^ n.1 ≤ R₁ ^ n.1 :=
    pow_le_pow_left₀ (norm_nonneg _) hz₁_le_R₁ _
  have hpow₂ : ‖z₂‖ ^ n.2 ≤ R₂ ^ n.2 :=
    pow_le_pow_left₀ (norm_nonneg _) hz₂_le_R₂ _
  have hnorm_pow₁ : ‖z₁ ^ n.1‖ ≤ C * ‖z₁‖ ^ n.1 := by
    cases n.1 with
    | zero =>
        simp [C]
    | succ m =>
        calc
          ‖z₁ ^ (m + 1)‖ ≤ ‖z₁‖ ^ (m + 1) := norm_pow_le' _ (Nat.succ_pos _)
          _ ≤ C * ‖z₁‖ ^ (m + 1) := by
              simpa [one_mul] using
                mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ C by exact le_max_right _ _)
                  (pow_nonneg (norm_nonneg _) _)
  have hnorm_pow₂ : ‖z₂ ^ n.2‖ ≤ C * ‖z₂‖ ^ n.2 := by
    cases n.2 with
    | zero =>
        simp [C]
    | succ m =>
        calc
          ‖z₂ ^ (m + 1)‖ ≤ ‖z₂‖ ^ (m + 1) := norm_pow_le' _ (Nat.succ_pos _)
          _ ≤ C * ‖z₂‖ ^ (m + 1) := by
              simpa [one_mul] using
                mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ C by exact le_max_right _ _)
                  (pow_nonneg (norm_nonneg _) _)
  calc
    ‖coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖
      ≤ ‖coeffXY S n.1 n.2‖ * ‖z₁ ^ n.1‖ * ‖z₂ ^ n.2‖ := by
          calc
            ‖coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2‖
              = ‖(coeffXY S n.1 n.2 * z₁ ^ n.1) * z₂ ^ n.2‖ := by rw [mul_assoc]
            _ ≤ ‖coeffXY S n.1 n.2 * z₁ ^ n.1‖ * ‖z₂ ^ n.2‖ := norm_mul_le _ _
            _ ≤ (‖coeffXY S n.1 n.2‖ * ‖z₁ ^ n.1‖) * ‖z₂ ^ n.2‖ := by
                  gcongr
                  exact norm_mul_le _ _
            _ = ‖coeffXY S n.1 n.2‖ * ‖z₁ ^ n.1‖ * ‖z₂ ^ n.2‖ := by ring
    _ ≤ ‖coeffXY S n.1 n.2‖ * (C * ‖z₁‖ ^ n.1) * (C * ‖z₂‖ ^ n.2) := by
          gcongr
    _ = C * C * (‖coeffXY S n.1 n.2‖ * ‖z₁‖ ^ n.1 * ‖z₂‖ ^ n.2) := by
          ring
    _ ≤ C * C * (‖coeffXY S n.1 n.2‖ * R₁ ^ n.1 * R₂ ^ n.2) := by
          gcongr

/-- Helper for Proposition 3.I: membership in the convergence domain gives summability of the
source-facing double-series itself. -/
theorem summable_sumXY_term_of_mem_domain
    [NormedRing 𝕜] [CompleteSpace 𝕜]
    (S : 𝕜⟦X,Y⟧) {z₁ z₂ : 𝕜}
    (hz : (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S)) :
    Summable (fun n : ℕ × ℕ ↦ coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2) := by
  -- Absolute convergence of the source-facing double series implies ordinary convergence.
  simpa using (summable_norm_sumXY_term_of_mem_domain S hz).of_norm

/-- Helper for Proposition 3.I: the weighted coefficient of a product is bounded by the
corresponding two-variable Cauchy majorant on the pair antidiagonal. -/
theorem norm_coeffXY_mul_le_cauchy_majorant
    [NormedRing 𝕜]
    (S T : 𝕜⟦X,Y⟧) {r₁ r₂ : ℝ} (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (p q : ℕ) :
    ‖coeffXY (S * T) p q‖ * r₁ ^ p * r₂ ^ q ≤
      ∑ kl ∈ Finset.antidiagonal (p, q),
        (‖coeffXY S kl.1.1 kl.1.2‖ * r₁ ^ kl.1.1 * r₂ ^ kl.1.2) *
          (‖coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ kl.2.1 * r₂ ^ kl.2.2) := by
  -- Apply the coefficient Cauchy formula, then rewrite the weights using the antidiagonal data.
  calc
    ‖coeffXY (S * T) p q‖ * r₁ ^ p * r₂ ^ q
      = ‖∑ kl ∈ Finset.antidiagonal (p, q),
            coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ p * r₂ ^ q := by
          rw [coeffXY_mul_eq_sum_antidiagonal]
    _ ≤
        (∑ kl ∈ Finset.antidiagonal (p, q),
          ‖coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖) *
            r₁ ^ p * r₂ ^ q := by
          have hsum :
              ‖∑ kl ∈ Finset.antidiagonal (p, q),
                  coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖ ≤
                ∑ kl ∈ Finset.antidiagonal (p, q),
                  ‖coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖ :=
            norm_sum_le _ _
          have hrpow : 0 ≤ r₁ ^ p * r₂ ^ q :=
            mul_nonneg (pow_nonneg hr₁ _) (pow_nonneg hr₂ _)
          simpa [mul_assoc] using mul_le_mul_of_nonneg_right hsum hrpow
    _ =
        ∑ kl ∈ Finset.antidiagonal (p, q),
          ‖coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ p * r₂ ^ q := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤
        ∑ kl ∈ Finset.antidiagonal (p, q),
          (‖coeffXY S kl.1.1 kl.1.2‖ * r₁ ^ kl.1.1 * r₂ ^ kl.1.2) *
            (‖coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ kl.2.1 * r₂ ^ kl.2.2) := by
          refine Finset.sum_le_sum fun kl hkl ↦ ?_
          have hpair : kl.1 + kl.2 = (p, q) := Finset.mem_antidiagonal.1 hkl
          have hp : kl.1.1 + kl.2.1 = p := by
            simpa using congrArg Prod.fst hpair
          have hq : kl.1.2 + kl.2.2 = q := by
            simpa using congrArg Prod.snd hpair
          calc
            ‖coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ p * r₂ ^ q
              ≤ (‖coeffXY S kl.1.1 kl.1.2‖ * ‖coeffXY T kl.2.1 kl.2.2‖) * r₁ ^ p * r₂ ^ q := by
                  gcongr
                  exact norm_mul_le _ _
            _ =
                (‖coeffXY S kl.1.1 kl.1.2‖ * r₁ ^ kl.1.1 * r₂ ^ kl.1.2) *
                  (‖coeffXY T kl.2.1 kl.2.2‖ * r₁ ^ kl.2.1 * r₂ ^ kl.2.2) := by
                  rw [← hp, ← hq, pow_add, pow_add]
                  ring

/-- Helper for Proposition 3.I: the convergence locus is stable under multiplication of
two-variable formal power series. -/
theorem formalSeriesConvergenceLocus_mul_subset
    [NormedRing 𝕜]
    (S T : 𝕜⟦X,Y⟧) :
    formalSeriesConvergenceLocus (coeffXY S) ∩ formalSeriesConvergenceLocus (coeffXY T) ⊆
      formalSeriesConvergenceLocus (coeffXY (S * T)) := by
  intro r hr
  rcases hr with ⟨hS, hT⟩
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY S) r).1 hS with
    ⟨hr₁, hr₂, hsS⟩
  rcases (mem_formalSeriesConvergenceLocus_iff (coeffXY T) r).1 hT with
    ⟨_, _, hsT⟩
  rw [mem_formalSeriesConvergenceLocus_iff]
  refine ⟨hr₁, hr₂, ?_⟩
  let f : ℕ × ℕ → ℝ := fun n ↦ ‖coeffXY S n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2
  let g : ℕ × ℕ → ℝ := fun n ↦ ‖coeffXY T n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2
  have hf : Summable f := by
    simpa [f] using hsS
  have hg : Summable g := by
    simpa [g] using hsT
  have hfg : Summable (fun x : (ℕ × ℕ) × (ℕ × ℕ) ↦ f x.1 * g x.2) :=
    Summable.mul_of_nonneg hf hg
      (fun _ ↦ mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr₁ _)) (pow_nonneg hr₂ _))
      (fun _ ↦ mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr₁ _)) (pow_nonneg hr₂ _))
  have hmajorant :
      Summable (fun n : ℕ × ℕ ↦ ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2) :=
    summable_sum_mul_antidiagonal_of_summable_mul hfg
  refine hmajorant.of_nonneg_of_le
      (fun n ↦ mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr₁ _)) (pow_nonneg hr₂ _))
      ?_
  intro n
  simpa [f, g] using
    norm_coeffXY_mul_le_cauchy_majorant S T hr₁ hr₂ n.1 n.2

section Add

variable [SeminormedAddCommGroup 𝕜]

/-- Proposition 3.I (1): the common convergence domain of two formal double series is contained in
the convergence domain of their sum. This is the source-facing convergence-domain statement for
the canonical sum on `𝕜⟦X,Y⟧`. -/
theorem formalSeriesConvergenceDomain_add_subset
    (S T : 𝕜⟦X,Y⟧) :
    formalSeriesConvergenceDomain (coeffXY S) ∩ formalSeriesConvergenceDomain (coeffXY T) ⊆
      formalSeriesConvergenceDomain (coeffXY (S + T)) := by
  -- Lift the additive closure from convergence loci to their interiors.
  rw [formalSeriesConvergenceDomain, formalSeriesConvergenceDomain, formalSeriesConvergenceDomain,
    ← interior_inter]
  refine interior_mono ?_
  intro r hr
  rcases hr with ⟨hS, hT⟩
  rcases
      (show 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
          Summable (fun n : ℕ × ℕ ↦ ‖coeffXY S n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2) from
        hS) with
    ⟨hr₁, hr₂, hsS⟩
  rcases
      (show 0 ≤ r.1 ∧ 0 ≤ r.2 ∧
          Summable (fun n : ℕ × ℕ ↦ ‖coeffXY T n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2) from
        hT) with
    ⟨_, _, hsT⟩
  refine ⟨hr₁, hr₂, ?_⟩
  -- The norm of each coefficient of `S + T` is dominated by the sum of the two majorants.
  refine Summable.of_nonneg_of_le ?_ ?_ (hsS.add hsT)
  · intro n
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hr₁ _)) (pow_nonneg hr₂ _)
  · intro n
    calc
      ‖coeffXY (S + T) n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2
        = ‖coeffXY S n.1 n.2 + coeffXY T n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2 := by
            rfl
      _ ≤ (‖coeffXY S n.1 n.2‖ + ‖coeffXY T n.1 n.2‖) * r.1 ^ n.1 * r.2 ^ n.2 := by
            gcongr
            exact norm_add_le _ _
      _ = (‖coeffXY S n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2) +
            (‖coeffXY T n.1 n.2‖ * r.1 ^ n.1 * r.2 ^ n.2) := by
            ring

end Add

section Mul

variable [NormedRing 𝕜]

/-- Proposition 3.I (2): the common convergence domain of two formal double series is contained in
the convergence domain of their product. This uses the canonical multiplication on `𝕜⟦X,Y⟧`
rather than a separate Cauchy-product owner. -/
theorem formalSeriesConvergenceDomain_mul_subset
    (S T : 𝕜⟦X,Y⟧) :
    formalSeriesConvergenceDomain (coeffXY S) ∩ formalSeriesConvergenceDomain (coeffXY T) ⊆
      formalSeriesConvergenceDomain (coeffXY (S * T)) := by
  -- Lift multiplicative closure from the convergence locus to its interior.
  rw [formalSeriesConvergenceDomain, formalSeriesConvergenceDomain, formalSeriesConvergenceDomain,
    ← interior_inter]
  exact interior_mono (formalSeriesConvergenceLocus_mul_subset S T)

end Mul

section SumAdd

variable [NormedRing 𝕜] [CompleteSpace 𝕜]

/-- Proposition 3.I (3): at every point whose coordinatewise absolute values lie in the common
convergence domain, the double-series expansion of the sum equals the sum of the two
double-series expansions. -/
theorem sumXY_add_eq
    (S T : 𝕜⟦X,Y⟧) {z₁ z₂ : 𝕜}
    (hz :
      (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S) ∩
        formalSeriesConvergenceDomain (coeffXY T)) :
    sumXY (S + T) (z₁, z₂) = sumXY S (z₁, z₂) + sumXY T (z₁, z₂) := by
  rcases hz with ⟨hS, hT⟩
  have hsumS := summable_sumXY_term_of_mem_domain S hS
  have hsumT := summable_sumXY_term_of_mem_domain T hT
  -- Rewrite the coefficients pointwise and invoke the additive `tsum` identity.
  calc
    sumXY (S + T) (z₁, z₂)
      = ∑' n : ℕ × ℕ,
          ((coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2) +
            (coeffXY T n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2)) := by
          refine tsum_congr fun n ↦ ?_
          change
            ((S (Finsupp.single 0 n.1 + Finsupp.single 1 n.2) +
                T (Finsupp.single 0 n.1 + Finsupp.single 1 n.2)) *
                z₁ ^ n.1 * z₂ ^ n.2 =
              S (Finsupp.single 0 n.1 + Finsupp.single 1 n.2) * z₁ ^ n.1 * z₂ ^ n.2 +
                T (Finsupp.single 0 n.1 + Finsupp.single 1 n.2) * z₁ ^ n.1 * z₂ ^ n.2)
          rw [add_mul, add_mul]
    _ = (∑' n : ℕ × ℕ, coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2) +
          ∑' n : ℕ × ℕ, coeffXY T n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2 := by
          exact hsumS.tsum_add hsumT
    _ = sumXY S (z₁, z₂) + sumXY T (z₁, z₂) := by
          simp [sumXY]

end SumAdd

section SumMul

variable [NormedCommRing 𝕜] [CompleteSpace 𝕜]

/-- Proposition 3.I (4): at every point whose coordinatewise absolute values lie in the common
convergence domain, the double-series expansion of the product equals the product of the two
double-series expansions. -/
theorem sumXY_mul_eq
    (S T : 𝕜⟦X,Y⟧) {z₁ z₂ : 𝕜}
    (hz :
      (‖z₁‖, ‖z₂‖) ∈ formalSeriesConvergenceDomain (coeffXY S) ∩
        formalSeriesConvergenceDomain (coeffXY T)) :
    sumXY (S * T) (z₁, z₂) = sumXY S (z₁, z₂) * sumXY T (z₁, z₂) := by
  rcases hz with ⟨hS, hT⟩
  let f : ℕ × ℕ → 𝕜 := fun n ↦ coeffXY S n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2
  let g : ℕ × ℕ → 𝕜 := fun n ↦ coeffXY T n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2
  have hfNorm : Summable (fun n : ℕ × ℕ ↦ ‖f n‖) := by
    simpa [f] using summable_norm_sumXY_term_of_mem_domain S hS
  have hgNorm : Summable (fun n : ℕ × ℕ ↦ ‖g n‖) := by
    simpa [g] using summable_norm_sumXY_term_of_mem_domain T hT
  have hf : Summable f := by
    simpa [f] using summable_sumXY_term_of_mem_domain S hS
  have hg : Summable g := by
    simpa [g] using summable_sumXY_term_of_mem_domain T hT
  have hfg : Summable (fun x : (ℕ × ℕ) × (ℕ × ℕ) ↦ f x.1 * g x.2) :=
    summable_mul_of_summable_norm hfNorm hgNorm
  -- Route correction: use the pair-antidiagonal Cauchy product directly, then identify each
  -- inner antidiagonal sum with the source-facing coefficient formula.
  calc
    sumXY (S * T) (z₁, z₂)
      = ∑' n : ℕ × ℕ, ∑ kl ∈ Finset.antidiagonal n, f kl.1 * g kl.2 := by
          refine tsum_congr fun n ↦ ?_
          dsimp [f, g]
          calc
            coeffXY (S * T) n.1 n.2 * z₁ ^ n.1 * z₂ ^ n.2
              = (∑ kl ∈ Finset.antidiagonal n,
                    coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2) *
                  z₁ ^ n.1 * z₂ ^ n.2 := by
                    rw [coeffXY_mul_eq_sum_antidiagonal]
            _ =
                ∑ kl ∈ Finset.antidiagonal n,
                  (coeffXY S kl.1.1 kl.1.2 * coeffXY T kl.2.1 kl.2.2) *
                    z₁ ^ n.1 * z₂ ^ n.2 := by
                  rw [Finset.sum_mul, Finset.sum_mul]
            _ =
                ∑ kl ∈ Finset.antidiagonal n,
                  (coeffXY S kl.1.1 kl.1.2 * z₁ ^ kl.1.1 * z₂ ^ kl.1.2) *
                    (coeffXY T kl.2.1 kl.2.2 * z₁ ^ kl.2.1 * z₂ ^ kl.2.2) := by
                  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
                  have hpair : kl.1 + kl.2 = n := Finset.mem_antidiagonal.1 hkl
                  have hp : kl.1.1 + kl.2.1 = n.1 := by
                    simpa using congrArg Prod.fst hpair
                  have hq : kl.1.2 + kl.2.2 = n.2 := by
                    simpa using congrArg Prod.snd hpair
                  rw [← hp, ← hq, pow_add, pow_add]
                  ring
    _ = (∑' n : ℕ × ℕ, f n) * ∑' n : ℕ × ℕ, g n := by
          symm
          exact hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg
    _ = sumXY S (z₁, z₂) * sumXY T (z₁, z₂) := by
          simp [sumXY, f, g]

end SumMul
