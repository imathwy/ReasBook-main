import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v w

variable {T : Type u} {Ω : Type v} {Ω' : Type w}
variable [MeasurableSpace Ω] [MeasurableSpace Ω']

-- Proof sketch: for a finite index set `I`, the owner finite-dimensional laws
-- `P.map (fun ω ↦ I.restrict (X · ω))` and `Q.map (fun ω ↦ I.restrict (Y · ω))` are Gaussian by
-- `IsGaussianProcess.hasGaussianLaw`; centeredness identifies their means with `0`, and the
-- covariance-function hypothesis identifies their covariance bilinear forms, so equality follows
-- from the finite-dimensional uniqueness of Gaussian laws by mean and covariance.
/-- Remark 21.10: the covariance function determines each finite-dimensional law of a centered
Gaussian process. Concretely, two centered Gaussian processes with the same covariance function
have the same finite-dimensional laws. -/
theorem finiteDimensionalDistributions_eq_of_centered_gaussian_covariance
    {P : Measure Ω} {Q : Measure Ω'}
    {X : T → Ω → ℝ} {Y : T → Ω' → ℝ}
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hX_centered : ∀ t, P[X t] = 0)
    (hY_centered : ∀ t, Q[Y t] = 0)
    (hcov : ∀ s t, cov[X s, X t; P] = cov[Y s, Y t; Q])
    (I : Finset T) :
    P.map (fun ω ↦ I.restrict (X · ω)) = Q.map (fun ω ↦ I.restrict (Y · ω)) := sorry
