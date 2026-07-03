

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_11_20 (from Items/Chap11) -/
open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Theorem 11.20 is `source-facing`: its public content is the Kesten--Stigum criterion for the
canonical limit of the normalized Galton--Watson martingale. Its `core/canonical` owner layer is
the Chapter 3 branching-process owner `IsGaltonWatsonProcess Z μ p`, the offspring mean
`galtonWatsonOffspringMean p`, the normalized process `branchingNormalizedProcess`, and the
canonical limit random variable of the natural filtration `Filtration.natural Z hZ_sm`. The
offspring `x log⁺ x` condition is a source-facing property of the law `p`, not a second owner
wrapper around the normalized process. -/

/-- The offspring law has finite `x log⁺ x` moment. This is the series form of the condition
`𝔼[X₁,₁ log(X₁,₁)^+] < ∞`. -/
def galtonWatsonHasFiniteXLogXMoment (p : PMF ℕ) : Prop :=
  Summable (fun k : ℕ ↦ ((k : ℝ) * Real.log⁺ (k : ℝ)) * (p k).toReal)

section

variable (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
variable (hZ_sm : ∀ n, StronglyMeasurable (Z n))

local notation "m" => ENNReal.toReal (galtonWatsonOffspringMean p)
local notation "ℱZ" => Filtration.natural Z hZ_sm
local notation "W" => branchingNormalizedProcess (fun n ω ↦ (Z n ω : ℝ)) m
local notation "W∞" => Filtration.limitProcess W ℱZ μ

-- Proof sketch: identify `W∞` with the canonical limit process of the normalized Galton--Watson
-- martingale `Z_n / m^n` with `m = E[X₁,₁]`, use the Kesten--Stigum `x log⁺ x` criterion for
-- uniform integrability, and combine it with the identities `𝔼[W_n] = 1` and `𝔼[W∞] ≤ 1` to
-- derive both equivalences.
/-- Theorem 11.20: for a supercritical Galton--Watson process, the canonical normalized process
`W_n = Z_n / m^n`, with `m` the offspring mean, has a canonical limit random variable `W∞` whose
expectation equals `1` exactly when its expectation is positive, and this is equivalent to
finiteness of the offspring `x log⁺ x` moment. -/
theorem branchingProcess_limit_expectation_eq_one_iff_pos_iff_finite_xlogx_moment
    (Z : ℕ → Ω → ℕ) (p : PMF ℕ)
    (hZ : IsGaltonWatsonProcess Z μ p)
    (hZ_sm : ∀ n, StronglyMeasurable (Z n))
    (hm : 1 < m) :
    (μ[W∞] = 1 ↔ 0 < μ[W∞]) ∧
      (0 < μ[W∞] ↔ galtonWatsonHasFiniteXLogXMoment p) := sorry

end
