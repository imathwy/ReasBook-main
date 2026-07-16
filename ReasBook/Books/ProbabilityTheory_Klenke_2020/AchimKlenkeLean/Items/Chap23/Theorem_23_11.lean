import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap02.Definition_2_14
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Definition_23_7
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap23.Example_23_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped BigOperators ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

variable [MeasurableSpace Ω]

/-- The `n + 1`st canonical normalized partial-sum law is the pushforward of `P` by the
`0`-based empirical mean `ω ↦ (∑ i ∈ range (n + 1), X i ω) / (n + 1)`. -/
theorem normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (n : ℕ) :
    normalizedPartialSumLaw X P ⟨n + 1, Nat.succ_pos _⟩ =
      Measure.map
        (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  rw [normalizedPartialSumLaw]
  congr 1
  ext ω
  simp [partialRealSum]

private theorem empiricalMean_aemeasurable
    (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    AEMeasurable
      (fun ω ↦ Finset.sum (Finset.range (n + 1)) (fun i ↦ X i ω) / (n + 1 : ℝ)) P := by
  have hsum : AEMeasurable (∑ i ∈ Finset.range (n + 1), X i) P := by
    exact Finset.aemeasurable_sum (Finset.range (n + 1)) fun i _ ↦ hXae i
  simpa [div_eq_mul_inv, mul_comm] using hsum.mul_const ((n + 1 : ℝ)⁻¹)

/-- The empirical-mean law in the `ℕ`-indexed reindexing view of Definition 23.7, obtained from
the `0`-based empirical mean of `X 0, …, X n`. The positive-indexed `normalizedPartialSumLaw`
remains available as the source-facing bridge/view of the same law. -/
noncomputable def empiricalMeanLaw
    (X : ℕ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXae : ∀ n, AEMeasurable (X n) P) :
    ℕ → ProbabilityMeasure ℝ :=
  fun n ↦ ProbabilityMeasure.map ⟨P, inferInstance⟩ (empiricalMean_aemeasurable P X hXae n)

/-- The canonical owner-sequence law `empiricalMeanLaw X P hXae n` agrees, after coercion to a
measure, with the chapter's positive-indexed `normalizedPartialSumLaw X P (n + 1)`. -/
theorem empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hXae : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    (empiricalMeanLaw X P hXae n : Measure ℝ) =
      normalizedPartialSumLaw X P (Nat.succPNat n) := by
  simpa [empiricalMeanLaw] using
    (normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage P X n).symm

private theorem iidAEMeasurable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX_iid : IsIID X P) :
    ∀ n, AEMeasurable (X n) P :=
  fun n ↦ (hX_iid.identDistrib n 0).aemeasurable_fst

local instance integrableExpSetMemDecidable
    (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) :
    Decidable (t ∈ integrableExpSet X P) :=
  Classical.decPred _ t

/-- The extended logarithmic moment-generating function `Λ` of a real random variable, equal to
`cgf` on the exponential-integrability domain and `⊤` outside it. This is the source-facing
version needed for the general form of Cramér's theorem. -/
noncomputable def extendedLogMomentGeneratingFunction
    (X : Ω → ℝ) (P : Measure Ω) (t : ℝ) : EReal :=
  if t ∈ integrableExpSet X P then
    (cgf X P t : EReal)
  else
    ⊤

scoped[ProbabilityTheory] notation "Λ(" X "; " P ")" => extendedLogMomentGeneratingFunction X P

/-- On its effective domain, `Λ(X; P)` agrees with the ordinary cumulant-generating function. -/
theorem extendedLogMomentGeneratingFunction_eq_cgf_of_mem_integrableExpSet
    (X : Ω → ℝ) (P : Measure Ω) {t : ℝ} (ht : t ∈ integrableExpSet X P) :
    Λ(X; P) t = (cgf X P t : EReal) := by
  simp [extendedLogMomentGeneratingFunction, ht]

/-- Outside its effective domain, `Λ(X; P)` takes the value `⊤`. -/
theorem extendedLogMomentGeneratingFunction_eq_top_of_not_mem_integrableExpSet
    (X : Ω → ℝ) (P : Measure Ω) {t : ℝ} (ht : t ∉ integrableExpSet X P) :
    Λ(X; P) t = ⊤ := by
  simp [extendedLogMomentGeneratingFunction, ht]

/-- The Legendre-Fenchel transform of an extended-real logarithmic moment-generating function. -/
noncomputable def legendreFenchelRateFunction (Λ : ℝ → EReal) (x : ℝ) : EReal :=
  sSup (Set.range fun t : ℝ ↦ ((t * x : ℝ) : EReal) - Λ t)

/-- If `exp (t X)` is integrable for every `t`, the source-facing extended rate function collapses
to the finite-exponential-moment Legendre-transform rate function from `Example 23.10`. -/
theorem legendreFenchelRateFunction_extendedLogMomentGeneratingFunction_eq_legendreCgfRateFunction
    (X : Ω → ℝ) (P : Measure Ω)
    (hmgf : ∀ t : ℝ, Integrable (fun ω ↦ Real.exp (t * X ω)) P) :
    legendreFenchelRateFunction (Λ(X; P)) =
      legendreCgfRateFunction X P := by
  funext x
  have hmem : ∀ t : ℝ, t ∈ integrableExpSet X P := fun t ↦ hmgf t
  simp [legendreFenchelRateFunction, legendreCgfRateFunction, extendedLogMomentGeneratingFunction,
    hmem, EReal.coe_sub]

-- Proof sketch: prove the LDP upper bound on closed sets and the lower bound on open sets by the
-- classical Cramér theorem for empirical means, identifying the rate as the Legendre-Fenchel
-- transform of the chapter's extended logarithmic moment-generating function of the common law.
/-- Theorem 23.11: Cramér's theorem. If `X₁, X₂, …` are i.i.d. real random variables, then the
laws of the empirical means `S_n / n` satisfy the large deviations principle with rate function
`Λ*`, where `Λ` is the extended logarithmic moment-generating function of the common law. The
main statement is organized around the chapter's reindexing bridge
`HasLargeDeviationsPrincipleAlong`, applied to the `ℕ`-indexed empirical-mean laws
`empiricalMeanLaw X P (iidAEMeasurable P X hX_iid)` with the positive scale map
`n ↦ (n + 1)⁻¹`; by
`empiricalMeanLaw_toMeasure_eq_normalizedPartialSumLaw`, its `n`th term is exactly the chapter's
positive-indexed law `normalizedPartialSumLaw X P (n + 1)`, and
`normalizedPartialSumLaw_succ_eq_map_zeroBasedAverage` identifies that law with the pushforward of
`P` by `ω ↦ (∑ i ∈ range (n + 1), X i ω) / (n + 1)`. Under the stronger hypothesis of finite
exponential moments for all `t`, the companion lemma
`legendreFenchelRateFunction_extendedLogMomentGeneratingFunction_eq_legendreCgfRateFunction`
identifies this source-facing rate function with `legendreCgfRateFunction (X 0) P`. -/
theorem cramer_empiricalMean_largeDeviationPrinciple
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_iid : IsIID X P) :
    HasLargeDeviationsPrincipleAlong
      (empiricalMeanLaw X P (iidAEMeasurable P X hX_iid))
      (fun n ↦ ⟨((n + 1 : ℝ)⁻¹), by
        have hn : 0 < (n + 1 : ℝ) := by
          positivity
        simpa using inv_pos.mpr hn⟩)
      atTop
      (fun x ↦ (legendreFenchelRateFunction (Λ(X 0; P)) x).toENNReal) :=
  sorry

end ProbabilityTheory
