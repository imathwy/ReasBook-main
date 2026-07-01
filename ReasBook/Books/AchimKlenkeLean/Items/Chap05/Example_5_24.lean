import Mathlib
import AchimKlenkeLean.Items.Chap02.Definition_2_14
import AchimKlenkeLean.Items.Chap05.Definition_5_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u v

variable {Ω : Type u} {E : Type v}

noncomputable section

/-- The Shannon information of a symbol with respect to the source law `p`, valued in `EReal` so
zero-probability symbols have infinite information content. -/
def shannonInformation (p : PMF E) : E → EReal :=
  fun e ↦ -ENNReal.log (p e)

/-- The Shannon information is the negative logarithm of the probability of the observed
symbol in `EReal`. -/
@[simp]
theorem shannonInformation_apply (p : PMF E) (e : E) :
    shannonInformation p e = -ENNReal.log (p e) := rfl

/-- On symbols in the support of `p`, the extended-real information content agrees with the usual
real-valued logarithm. -/
theorem shannonInformation_toReal_eq (p : PMF E) {e : E} (he : e ∈ p.support) :
    (shannonInformation p e).toReal = -Real.log ((p e).toReal) := sorry

/-- The probability of the initial word `X₁(ω), …, Xₙ(ω)` under the i.i.d. source law `p`, valued
in `ENNReal`. -/
def shannonPathProbability (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) : Ω → ENNReal :=
  fun ω ↦ ∏ i : Fin n, p (X (i + 1) ω)

/-- The path probability is the product of the probabilities of the first `n` observed symbols. -/
@[simp]
theorem shannonPathProbability_apply (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    shannonPathProbability p X n ω = ∏ i : Fin n, p (X (i + 1) ω) := rfl

-- Proof sketch: expand `shannonPathProbability` and `shannonInformation`, then use
-- `ENNReal.log_mul_add` to convert the logarithm of the product into a sum of logarithms in
-- `EReal`.
/-- The negative logarithm of the path probability is the sum of the information contents of the
first `n` observed symbols. This remains valid pointwise because zero-probability symbols contribute
`⊤` information content. -/
theorem neg_log_shannonPathProbability_eq_sum_shannonInformation
    (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) :
    -ENNReal.log (shannonPathProbability p X n ω) =
      ∑ i : Fin n, shannonInformation p (X (i + 1) ω) := sorry

-- Proof sketch: apply `EReal.toReal` to
-- `neg_log_shannonPathProbability_eq_sum_shannonInformation`, using the support assumptions to
-- rule out zero-probability symbols and hence `⊤` summands.
/-- On words whose letters all lie in the support of `p`, the extended-real path-information
identity reduces to the usual real-valued logarithmic identity. -/
theorem neg_log_shannonPathProbability_toReal_eq_sum_shannonInformation
    (p : PMF E) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω)
    (hsupport : ∀ i : Fin n, X (i + 1) ω ∈ p.support) :
    -Real.log ((shannonPathProbability p X n ω).toReal) =
      ∑ i : Fin n, (shannonInformation p (X (i + 1) ω)).toReal := sorry

variable [Finite E] [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSingletonClass E]

section ShannonTheorem

variable (P : Measure Ω) [IsProbabilityMeasure P] (p : PMF E) (X : ℕ → Ω → E)
variable (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
variable (hX_law : HasLaw (X 1) p.toMeasure P)

-- Proof sketch: apply `ProbabilityTheory.strong_law_ae_real` to the real-valued sequence
-- `fun n ↦ fun ω ↦ (shannonInformation p (X (n + 1) ω)).toReal`; independence follows from
-- `hX_iid` by composing with the measurable information-content map on the finite alphabet,
-- identical distribution comes from `hX_iid`, the common law `p` is anchored by `hX_law`, and
-- the expectation is computed as `(entropy p).toReal` using `HasLaw.integral_eq` together with a
-- local `Fintype.ofFinite E`, `PMF.integral_eq_sum`, and `entropy_toReal_eq_sum`.
/-- Example 5.24, information-content form: for i.i.d. `E`-valued random variables with common law
`p`, the empirical mean of `-log p(X_n)` converges almost surely to the entropy of `p`
(compare Definition 5.25). -/
theorem shannon_theorem_informationContent_ae_tendsto
    :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ ↦
          (∑ i ∈ Finset.range n, (shannonInformation p (X (i + 1) ω)).toReal) / n)
        atTop (𝓝 ((entropy p).toReal)) := sorry

-- Proof sketch: combine `shannon_theorem_informationContent_ae_tendsto` with
-- `neg_log_shannonPathProbability_toReal_eq_sum_shannonInformation` on the full-measure event where
-- every observed symbol lies in the support of `p`, so the normalized negative log-likelihood of
-- the observed word is the empirical mean of the real-valued information contents.
/-- Example 5.24: Shannon's theorem says that for an i.i.d. `E`-valued source with law `p`, the
normalized negative logarithm of the path probability `pi_n` converges almost surely to the Shannon
entropy of `p` (compare Definition 5.25). -/
theorem shannon_theorem_ae_tendsto
    :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ ↦ (-Real.log ((shannonPathProbability p X n ω).toReal)) / n) atTop
        (𝓝 ((entropy p).toReal)) := sorry

end ShannonTheorem
