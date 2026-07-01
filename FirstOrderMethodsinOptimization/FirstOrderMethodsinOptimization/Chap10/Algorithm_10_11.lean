import Mathlib
import FirstOrderMethodsinOptimization.Chap10.Algorithm_10_13
import FirstOrderMethodsinOptimization.Chap10.Assumption_10_31
import FirstOrderMethodsinOptimization.Chap10.Definition_10_2
import FirstOrderMethodsinOptimization.Chap09.Definition_9_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Algorithm 10.11 is `source-facing` in the chapter's fast proximal-gradient API.

Domain sampling:
- `T[...]` from Definition 10.9 is the canonical owner for the prox-gradient point
  `z^k = T_(L_k)(y^k)` attached to a real-valued smooth term and an extended-real-valued
  regularizer;
- `fista_momentum_update` from Algorithm 10.13 is already the local owner for the textbook
  momentum recursion `t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`;
- `composite_model_objective` from Definition 10.2 is the chapter owner for the composite value
  `F = f + g`, and the project already uses the bridge `f.toEReal` for real-valued smooth terms.

The genuinely new source content is the monotone acceptance clause choosing `x^(k+1)` from the
two displayed candidates `z^k` and `x^k`. Because this step is a noncanonical choice, the
faithful public API is a trajectory predicate on the sequences `(x^k, y^k, z^k, t_k, L_k)`
rather than a recursively chosen iterate map. The primitive regularity data are the same
proper/closed/convex instances on `g` already used by `T[...]`; the problem-owned bridge
`IsFastProximalGradientProblem.IsMfistaTrajectory` below is derived API.

The last update formula in the source uses `t_(k-1) - 1` at step `k`. To make the boundary case
`k = 0` explicit, the formalization uses the standard initial convention `t_(-1) = 0` and then
forms the coefficient `(t_(k-1) - 1) / t_(k+1)`. -/

/-- The previous MFISTA momentum coefficient, encoding the boundary convention `t_(-1) = 0` and
`t_(k-1)` for later indices. -/
def mfista_previous_momentum (t : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => t k

-- Proof sketch: unfold the recursive definition of `mfista_previous_momentum` at `0`.
/-- The initial previous MFISTA momentum coefficient is `0`, corresponding to the convention
`t_(-1) = 0`. -/
@[simp] theorem mfista_previous_momentum_zero (t : ℕ → ℝ) :
    mfista_previous_momentum t 0 = 0 := rfl

-- Proof sketch: unfold the recursive definition of `mfista_previous_momentum` at `k + 1`.
/-- For `k ≥ 0`, the previous MFISTA momentum coefficient at index `k + 1` is `t_k`. -/
@[simp] theorem mfista_previous_momentum_succ (t : ℕ → ℝ) (k : ℕ) :
    mfista_previous_momentum t (k + 1) = t k := rfl

/-- Algorithm 10.11: a tuple of sequences `(x^k, y^k, z^k, t_k, L_k)` is an MFISTA trajectory
for `f` and `g` when `y^0 = x^0`, `t_0 = 1`, each `z^k` is the prox-gradient point
`T_(L_k)(y^k)`, the chosen iterate `x^(k+1)` is one of the two textbook candidates `z^k` or
`x^k` and minimizes the composite objective on that two-point set, the momentum update is
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`, and `y^(k+1)` is given by the MFISTA extrapolation
formula with coefficient `(t_(k-1) - 1) / t_(k+1)` and the boundary convention `t_(-1) = 0`. -/
class is_mfista_trajectory
    (f : E → ℝ) (g : E → EReal) [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]
    (x y z : ℕ → E) (t : ℕ → ℝ) (L : ℕ → PosReal) : Prop where
  y_zero : y 0 = x 0
  t_zero : t 0 = 1
  z_eq (k : ℕ) :
    z k = T[L k; f, g] (y k)
  x_next_mem (k : ℕ) :
    x (k + 1) ∈ ({z k, x k} : Set E)
  x_next_isMinOn (k : ℕ) :
    IsMinOn (composite_model_objective f.toEReal g) ({z k, x k} : Set E) (x (k + 1))
  t_succ (k : ℕ) : t (k + 1) = fista_momentum_update (t k)
  y_succ (k : ℕ) :
    y (k + 1) =
      x (k + 1) +
        (t k / t (k + 1)) • (z k - x (k + 1)) +
        ((mfista_previous_momentum t k - 1) / t (k + 1)) • (x (k + 1) - x k)

variable {f : E → ℝ} {g : E → EReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]
variable {x y z : ℕ → E} {t : ℕ → ℝ} {L : ℕ → PosReal}

-- Proof sketch: project the `y_zero` field of `is_mfista_trajectory`.
/-- An MFISTA trajectory starts from `y^0 = x^0`. -/
theorem is_mfista_trajectory_y_zero
    (htraj : is_mfista_trajectory f g x y z t L) :
    y 0 = x 0 :=
  htraj.y_zero

-- Proof sketch: project the `t_zero` field of `is_mfista_trajectory`.
/-- An MFISTA trajectory starts from the initial momentum parameter `t_0 = 1`. -/
theorem is_mfista_trajectory_t_zero
    (htraj : is_mfista_trajectory f g x y z t L) :
    t 0 = 1 :=
  htraj.t_zero

/-- At each iteration `k`, the auxiliary MFISTA point `z^k` is the canonical prox-gradient point
`T_(L_k)(y^k)`. -/
theorem is_mfista_trajectory_z_eq
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    z k = T[L k; f, g] (y k) :=
  htraj.z_eq k

/-- At each iteration `k`, the chosen MFISTA iterate `x^(k+1)` is one of the two displayed
candidates `z^k` or `x^k`. -/
theorem is_mfista_trajectory_x_next_mem
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    x (k + 1) ∈ ({z k, x k} : Set E) :=
  htraj.x_next_mem k

/-- At each iteration `k`, the chosen MFISTA iterate `x^(k+1)` minimizes the composite objective
on the two-point candidate set `{z^k, x^k}`. -/
theorem is_mfista_trajectory_x_next_isMinOn
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    IsMinOn (composite_model_objective f.toEReal g) ({z k, x k} : Set E) (x (k + 1)) :=
  htraj.x_next_isMinOn k

/-- At each iteration `k`, the chosen MFISTA iterate `x^(k+1)` is either `z^k` or `x^k`. -/
theorem is_mfista_trajectory_x_next_eq_or_eq
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    x (k + 1) = z k ∨ x (k + 1) = x k := by
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm, or_left_comm, or_assoc] using
    htraj.x_next_mem k

/-- At each iteration `k`, the chosen MFISTA iterate `x^(k+1)` satisfies the monotonicity clause
`F(x^(k+1)) ≤ min {F(z^k), F(x^k)}`. -/
theorem is_mfista_trajectory_objective_le_min
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    composite_model_objective f.toEReal g (x (k + 1)) ≤
      min (composite_model_objective f.toEReal g (z k))
        (composite_model_objective f.toEReal g (x k)) := by
  have hmin := htraj.x_next_isMinOn k
  rw [isMinOn_iff] at hmin
  exact le_min (hmin (z k) (by simp)) (hmin (x k) (by simp))

/-- At each iteration `k`, the MFISTA momentum sequence satisfies
`t_(k+1) = (1 + √(1 + 4 t_k^2)) / 2`. -/
theorem is_mfista_trajectory_t_succ
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    t (k + 1) = fista_momentum_update (t k) :=
  htraj.t_succ k

/-- At each iteration `k`, the extrapolated point `y^(k+1)` is obtained from `x^(k+1)`, `z^k`,
`x^k`, `t_k`, and the source coefficient `(t_(k-1) - 1) / t_(k+1)`. -/
theorem is_mfista_trajectory_y_succ
    (htraj : is_mfista_trajectory f g x y z t L) (k : ℕ) :
    y (k + 1) =
      x (k + 1) +
        (t k / t (k + 1)) • (z k - x (k + 1)) +
        ((mfista_previous_momentum t k - 1) / t (k + 1)) • (x (k + 1) - x k) :=
  htraj.y_succ k

variable {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

namespace IsFastProximalGradientProblem

/-- Bridge/view layer: Assumption 10.31 canonically supplies the regularity data required by the
MFISTA trajectory predicate. -/
abbrev IsMfistaTrajectory
    (hproblem : IsFastProximalGradientProblem f g XStar FOpt Lf)
    (x y z : ℕ → E) (t : ℕ → ℝ) (L : ℕ → PosReal) : Prop :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  is_mfista_trajectory f g x y z t L

end IsFastProximalGradientProblem

end
