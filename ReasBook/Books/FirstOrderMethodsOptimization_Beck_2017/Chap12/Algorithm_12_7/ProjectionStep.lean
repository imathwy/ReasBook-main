import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

open scoped BigOperators

noncomputable section

universe u

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

end
