import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Items.Chap25.Corollary_25_19
import ProbabilityTheory_Klenke_2020.Items.Chap25.StandardBrownianMotionVector
import ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30

open MeasureTheory ProbabilityTheory Laplacian InnerProductSpace
open scoped BigOperators ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

variable {d : ℕ} {ℱ : TimeFiltration}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "VectorProcess" => NNReal → Ω → State
local notation "CoordinateProcessFamily" => Fin d → Process

/-- The time derivative `∂ₜ F` of a function on `ℝ^d × ℝ`, taken in the last coordinate. -/
noncomputable def timePartialDeriv (F : State × ℝ → ℝ) : State × ℝ → ℝ :=
  fun xt ↦ deriv (fun s : ℝ ↦ F (xt.1, s)) xt.2

notation:max "∂ₜ " F:arg => timePartialDeriv F

-- Proof sketch: unfold `timePartialDeriv`; it is the one-variable derivative in the time slot
-- with the spatial variable frozen.
/-- Evaluating `(∂ₜ F)` at `(x,t)` gives the derivative of `s ↦ F(x,s)` at `t`. -/
theorem timePartialDeriv_def
    (F : State × ℝ → ℝ) (xt : State × ℝ) :
    (∂ₜ F) xt =
      deriv (fun s : ℝ ↦ F (xt.1, s)) xt.2 := rfl

/-- The source-facing `C^{2,1}` regularity assumption on `F : ℝ^d × ℝ → ℝ`: the named time and
spatial derivatives are genuine derivatives of the corresponding one-variable slices, and these
derivatives are continuous. The spatial derivatives are expressed through the chapter’s canonical
coordinate-derivative owners `∂ₜ`, `∂[i]`, and `∂²[i,j]` applied to the relevant frozen slices
`x ↦ F (x, t)`. Continuity of `F` itself is derived from this first-order regularity data, so it
is not stored as a primitive field. -/
@[mk_iff isTimeSpaceC21_iff]
class IsTimeSpaceC21 (F : State × ℝ → ℝ) : Prop where
  hasDerivAt_time (xt : State × ℝ) :
    HasDerivAt (fun s : ℝ ↦ F (xt.1, s)) ((∂ₜ F) xt) xt.2
  continuous_timePartialDeriv : Continuous (∂ₜ F)
  hasDerivAt_space (i : Fin d) (xt : State × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ F (xt.1 + EuclideanSpace.single i (s - xt.1 i), xt.2))
      ((∂[i] fun x : State ↦ F (x, xt.2)) xt.1)
      (xt.1 i)
  continuous_spacePartialDeriv (i : Fin d) :
    Continuous (fun xt : State × ℝ ↦ (∂[i] fun x : State ↦ F (x, xt.2)) xt.1)
  hasDerivAt_spaceSecond (i j : Fin d) (xt : State × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        (∂[i] fun x : State ↦ F (x, xt.2))
          (xt.1 + EuclideanSpace.single j (s - xt.1 j)))
      ((∂²[i, j] fun x : State ↦ F (x, xt.2)) xt.1)
      (xt.1 j)
  continuous_spaceSecondPartialDeriv (i j : Fin d) :
    Continuous (fun xt : State × ℝ ↦ (∂²[i, j] fun x : State ↦ F (x, xt.2)) xt.1)

-- Proof sketch: apply the multidimensional Itô formula to the space-time process
-- `Y_t = (W_t, t)`. The Brownian coordinates contribute the stochastic terms
-- `∫₀ᵀ ∂ₖF(W_s,s) dWₛᵏ`, the deterministic time coordinate contributes `∫₀ᵀ ∂_{d+1}F(W_s,s) ds`,
-- and independence of the Brownian coordinates removes the mixed second-order terms. Since the
-- stochastic terms are given only via the realization predicate `IsBrownianLocalItoIntegral`,
-- the conclusion is stated canonically as an equality of modifications rather than a pointwise
-- identity for every `ω`. Following Theorem 25.33, the second-order drift is expressed by the
-- canonical Laplacian `Δ` on the frozen spatial slice `x ↦ F (x, s)`, with the coordinate sum
-- `∑ i ∂²[i,i]` available only as a bridge.
/-- Corollary 25.35: if `F ∈ C^{2,1}(ℝ^d × ℝ)`, `W` is a standard `d`-dimensional Brownian
motion, and `N k` realizes the Brownian local Itô integral of the spatial derivative
`∂ₖ F(W_s,s)` against the `k`-th coordinate of `W`, then the time-dependent Itô formula holds as
an equality of modifications. Equivalently, for each deterministic time `T`, the random variables
`F(W_T,T) - F(W_0,0)` and
`∑ₖ Nₖ(T) + ∫₀ᵀ (∂ₜF(W_s,s) + 1/2 Δ (fun x ↦ F (x,s)) (W_s)) ds`
agree almost surely. -/
theorem brownian_time_dependent_ito_formula
    (F : State × ℝ → ℝ) {W : VectorProcess} (N : CoordinateProcessFamily)
    (hF : IsTimeSpaceC21 F) (hW : IsStandardBrownianMotionVector μ W)
    (hN : ∀ i : Fin d,
      IsBrownianLocalItoIntegral
        ℱ
        μ
        (fun t ω ↦ W t ω i)
        (fun t ω ↦ (∂[i] fun x : State ↦ F (x, t)) (W t ω))
        (N i))
    :
    AreModifications μ
      (fun T ω ↦
        F (W T ω, T) - F (W 0 ω, 0))
      (fun T ω ↦
        (∑ i : Fin d, N i T ω) +
          ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
            (∂ₜ F) (W s.toNNReal ω, s) +
              ((1 : ℝ) / 2) *
                Δ (fun x : State ↦ F (x, s)) (W s.toNNReal ω)) := sorry

set_option linter.unusedVariables false in
/-- The fixed-time almost-sure form of Corollary 25.35. -/
theorem brownian_time_dependent_ito_formula_ae_eq
    (F : State × ℝ → ℝ) {W : VectorProcess} (N : CoordinateProcessFamily)
    (hF : IsTimeSpaceC21 F) (hW : IsStandardBrownianMotionVector μ W)
    (hN : ∀ i : Fin d,
      IsBrownianLocalItoIntegral
        ℱ
        μ
        (fun t ω ↦ W t ω i)
        (fun t ω ↦ (∂[i] fun x : State ↦ F (x, t)) (W t ω))
        (N i))
    (T : NNReal) :
    (fun ω ↦ F (W T ω, T) - F (W 0 ω, 0))
      =ᵐ[μ]
        (fun ω ↦
          (∑ i : Fin d, N i T ω) +
            ∫ s in Set.Icc (0 : ℝ) (T : ℝ),
              (∂ₜ F) (W s.toNNReal ω, s) +
                ((1 : ℝ) / 2) *
                  Δ (fun x : State ↦ F (x, s)) (W s.toNNReal ω)) :=
  brownian_time_dependent_ito_formula F N hF hW hN T

end ProbabilityTheory
