import Mathlib
import FirstOrderMethodsinOptimization.Chap03.Proposition_3_12
import FirstOrderMethodsinOptimization.Chap06.Definition_6_7
import FirstOrderMethodsinOptimization.Chap12.Proposition_12_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

/- Algorithm 12.7 is `source-facing`: it names the dual iterates `y^k ∈ E^p` and the derived
primal points `x^k = ∑ i, y_i^k + d` for the orthogonal-projection problem over a finite family of
closed convex sets.

Domain sampling against the nearby Chapter 12 owners identifies:
- `projectionPoint` from Proposition 3.12 as the canonical owner of each component projection
  `P_{C_i}`;
- `DualBasedProximalGradientDualStepsizeParameter` from Algorithm 12.1 as the canonical admissible
  constant-stepsize owner;
- `dual_block_duplication` and
  `dual_block_duplication_fdpg_lipschitz_constant_eq` from Proposition 12.8 as the specialization
  computing the finite-intersection lower bound `‖𝒜‖² = p` for the diagonal duplication operator;
- `polyhedral_projection_primal_point` and `polyhedral_projection_dual_update` from Algorithm 12.5
  as the chapter pattern of separating the shared step-(a) / step-(b) owners from the recursive
  iterate families.

The owner abstraction for this file is therefore the finite-intersection primal point
`∑ i, y_i + d`, the componentwise projection-gradient update, and the Chapter 12.1 stepsize owner
specialized to the diagonal duplication map with `σ = 1`. The DPG dual and primal iterate
families are derived from those owners. -/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {p : ℕ}

/-- For the diagonal duplication map from Proposition 12.8, every admissible Chapter 12.1
stepsize parameter satisfies the textbook lower bound `p ≤ L`. -/
theorem finite_intersection_projection_stepsize_lower_bound
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1) :
    (p : ℝ) ≤ (L : ℝ) := by
  simpa using DualBasedProximalGradientDualStepsizeParameter.lower_bound L

end

section

variable {E : Type u} [AddCommMonoid E] {p : ℕ}

/-- The shared step-(a) primal point `x = ∑ i, y_i + d` attached to the current block vector
`y ∈ E^p`. -/
def finite_intersection_projection_primal_point
    (d : E) (y : Fin p → E) : E :=
  (∑ i, y i) + d

/-- Expanding the shared primal point gives the textbook affine sum `∑ i, y_i + d`. -/
@[simp] theorem finite_intersection_projection_primal_point_eq
    (d : E) (y : Fin p → E) :
    finite_intersection_projection_primal_point d y = (∑ i, y i) + d :=
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {p : ℕ}

/-- The shared componentwise projection-gradient update from a primal point `x` and current block
vector `y`. Its `i`th coordinate is
`y_i - (1 / L) x + (1 / L) P_{C_i}(x - L y_i)`. -/
def finite_intersection_projection_dual_update
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (L : PosReal) (x : E) (y : Fin p → E) :
    Fin p → E :=
  fun i ↦
    y i - (1 / L : ℝ) • x +
      (1 / L : ℝ) •
        Pp[C i, hC_nonempty i, hC_closed i, hC_convex i] (x - (L : ℝ) • y i)

/-- Evaluating the shared projection-gradient update at index `i` gives the textbook coordinate
formula `y_i - (1 / L) x + (1 / L) P_{C_i}(x - L y_i)`. -/
@[simp] theorem finite_intersection_projection_dual_update_apply
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i)) (L : PosReal) (x : E) (y : Fin p → E) (i : Fin p) :
    finite_intersection_projection_dual_update C hC_nonempty hC_closed hC_convex L x y i =
      y i - (1 / L : ℝ) • x +
        (1 / L : ℝ) •
          Pp[C i, hC_nonempty i, hC_closed i, hC_convex i] (x - (L : ℝ) • y i) :=
  rfl

/-- Algorithm 12.7: for a finite family of nonempty closed convex sets `C₁, …, C_p`, a point
`d`, an admissible constant parameter `L ≥ p`, and an initialization `y⁰ ∈ E^p`, the dual
projection-gradient method
generates dual iterates by
`y_i^(k+1) = y_i^k - (1 / L) x^k + (1 / L) P_{C_i}(x^k - L y_i^k)`,
where `x^k = ∑ i, y_i^k + d`. -/
def finite_intersection_dual_projection_gradient_method
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i))
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
    (d : E) (y0 : Fin p → E) :
    ℕ → Fin p → E
  | 0 => y0
  | k + 1 =>
      let yk :=
        finite_intersection_dual_projection_gradient_method
          C hC_nonempty hC_closed hC_convex L d y0 k
      finite_intersection_projection_dual_update C hC_nonempty hC_closed hC_convex L
        (finite_intersection_projection_primal_point d yk) yk

/-- The primal iterate `x^k` attached to the dual projection-gradient method is the affine sum
`x^k = ∑ i, y_i^k + d` of the current dual block vector and the data point `d`. -/
def finite_intersection_dual_projection_gradient_primal_iterates
    (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
    (hC_convex : ∀ i, Convex ℝ (C i))
    (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
    (d : E) (y0 : Fin p → E) :
    ℕ → E :=
  fun k ↦
    finite_intersection_projection_primal_point d
      (finite_intersection_dual_projection_gradient_method
        C hC_nonempty hC_closed hC_convex L d y0 k)

section

variable (C : Fin p → Set E) (hC_nonempty : ∀ i, (C i).Nonempty) (hC_closed : ∀ i, IsClosed (C i))
variable (hC_convex : ∀ i, Convex ℝ (C i))
variable (L : DualBasedProximalGradientDualStepsizeParameter (dual_block_duplication E p) 1)
variable (d : E) (y0 : Fin p → E)

local notation "y[" k "]" =>
  finite_intersection_dual_projection_gradient_method
    C hC_nonempty hC_closed hC_convex L d y0 k

local notation "x[" k "]" =>
  finite_intersection_dual_projection_gradient_primal_iterates
    C hC_nonempty hC_closed hC_convex L d y0 k

/-- The dual projection-gradient sequence starts at the prescribed initialization `y⁰`. -/
@[simp] theorem finite_intersection_dual_projection_gradient_method_zero :
    y[0] = y0 :=
  rfl

-- Proof sketch: unfold `finite_intersection_dual_projection_gradient_primal_iterates`; by
-- definition `x^k` is the shared primal-point owner applied to the current dual iterate `y^k`.
/-- The primal iterates are obtained by applying the shared finite-intersection primal-point owner
to the current dual iterate. -/
theorem finite_intersection_dual_projection_gradient_primal_iterates_eq (k : ℕ) :
    x[k] = finite_intersection_projection_primal_point d y[k] :=
  rfl

/-- Each successor dual iterate is obtained by applying the shared finite-intersection
projection-gradient update to `x^k` and `y^k`. -/
theorem finite_intersection_dual_projection_gradient_method_succ (k : ℕ) :
    y[k + 1] =
      finite_intersection_projection_dual_update C hC_nonempty hC_closed hC_convex L x[k] y[k] := by
  rfl

end

end
