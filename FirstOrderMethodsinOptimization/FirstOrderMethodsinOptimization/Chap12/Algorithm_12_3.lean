import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsinOptimization.Chap12.Algorithm_12_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

noncomputable section

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/- Algorithm 12.3 supplies the chapter's `core/canonical` accelerated dual-trajectory owner: the
textbook objects are the dual iterates `y^k` and the extrapolated points `w^k`, while the
acceleration scalars are already owned upstream by the canonical Chapter 10 sequence
`fista_momentum_sequence`.

Domain sampling against nearby project owners identifies:
- `dual_based_proximal_gradient_dual_step` from Algorithm 12.1 as the canonical owner for the
  set-valued dual proximal step `y^(k+1) ∈ prox[(1 / L) G] (w^k - (1 / L) ∇F(w^k))`;
- `fista_momentum_sequence` from Algorithm 10.13 as the canonical owner for the scalar recursion
  `t₀ = 1`, `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `is_mfista_trajectory` from Algorithm 10.11 as the chapter's trajectory-owner pattern for
  accelerated methods stated directly on named iterate families rather than through a chosen
  recursive implementation package.

There is no exact upstream owner for the accelerated dual recursion based at the extrapolated
points `w^k`, so the local class below is still the right owner level. Its primitive data are only
the explicit sequences `y` and `w`; the scalar momentum data are derived API, already determined
by `fista_momentum_sequence`, and any hidden bookkeeping for `t_(-1)` should not be a public
owner. -/

/- The acceleration scalars are reused from the canonical Chapter 10 FISTA momentum sequence. -/
recall fista_momentum_sequence

local notation "t[" k "]" => fista_momentum_sequence k

/-- Algorithm 12.3: the sequences `(y^k, w^k, t_k)` follow the fast dual proximal-gradient
method in dual representation when `L` is an admissible constant stepsize parameter, the initial
conditions are `y⁰ = w⁰ = y0`, each `y^(k+1)` lies in the Chapter 12 dual proximal step set based
at `w^k`, the acceleration scalars are the canonical values `t_k = fista_momentum_sequence k`,
and the textbook extrapolation step
`w^(k+1) = y^(k+1) + (t_(k-1) / t_(k+1)) (y^(k+1) - y^k)` is recorded by the equivalent public
pair `w¹ = y¹` and
`w^(k+2) = y^(k+2) + (t_k / t_(k+2)) (y^(k+2) - y^(k+1))`. -/
class IsFastDualProximalGradientDualTrajectory
    (A : E →L[ℝ] V) (σ : PosReal) (G : V → EReal) (gradF : V → V)
    (L : DualBasedProximalGradientDualStepsizeParameter A σ) (y0 : V) (y w : ℕ → V) : Prop where
  /-- The initial dual iterate is the prescribed point `y0`. -/
  y_zero : y 0 = y0
  /-- The extrapolated sequence starts from the same prescribed point `y0`. -/
  w_zero : w 0 = y0
  /-- At each step, the next dual iterate lies in the Chapter 12 dual proximal update set based
  at `w^k`. -/
  dual_step (k : ℕ) :
    y (k + 1) ∈ dual_based_proximal_gradient_dual_step G gradF L (w k)
  /-- The first extrapolated iterate is recorded explicitly as `w¹ = y¹`. -/
  first_momentum_step : w 1 = y 1
  /-- For every `k`, the later extrapolated iterates satisfy the shifted textbook momentum
  recursion. -/
  momentum_step (k : ℕ) :
    w (k + 2) =
      y (k + 2) +
        (t[k] / t[k + 2]) •
          (y (k + 2) - y (k + 1))

end
