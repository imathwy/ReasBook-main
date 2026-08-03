import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

-- Semantic recall: `lean_leansearch` did not return a direct variational-inequality owner, so
-- this file follows Chapter 20's maximal-monotonicity owner `Maximal IsMonotone B` and the
-- inequality surface used in Example 26.20.

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 26.19: for `f ∈ Γ₀(H)` and a maximally monotone operator `B : H → 2^H`, the
associated variational inequality problem is the set of points `x` for which there exists
`u ∈ B x` such that `∀ y ∈ H, ⟪x - y, u⟫ + f(x) ≤ f(y)`. -/
def variationalInequalityProblem
    (f : H → Set.Ioi (⊥ : EReal)) (B : SetValuedOperator H H) :
    Set H :=
  {x | ∃ u ∈ B x, ∀ y : H, (⟪x - y, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)}

/-- Membership in `variationalInequalityProblem f B` is exactly the textbook existence of a
pointwise `B x` certificate satisfying the variational inequality against every `y`. -/
@[simp] theorem mem_variationalInequalityProblem_iff
    (f : H → Set.Ioi (⊥ : EReal)) (B : SetValuedOperator H H) (x : H) :
    x ∈ variationalInequalityProblem f B ↔
      ∃ u ∈ B x, ∀ y : H, (⟪x - y, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := Iff.rfl

/-- `variationalInequalityProblem f B` is exactly the set of points admitting a witness
`u ∈ B x` that satisfies the source variational inequality against every `y`. -/
theorem variationalInequalityProblem_eq
    (f : H → Set.Ioi (⊥ : EReal)) (B : SetValuedOperator H H) :
    variationalInequalityProblem f B =
      {x | ∃ u ∈ B x, ∀ y : H, (⟪x - y, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)} := rfl

end ERealFunction
