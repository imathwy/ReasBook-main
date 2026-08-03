import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap20.Definition_20_51

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace Pointwise SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 25.21: every concrete graph-point contribution is bounded by the
Fitzpatrick supremum of the operator. -/
private theorem fitzpatrickSupremand_le_of_mem
    (A : SetValuedOperator H H) (x u y v : H) (hv : v ∈ A y) :
    (((⟪y, u⟫_ℝ + ⟪x, v⟫_ℝ - ⟪y, v⟫_ℝ : ℝ) : EReal)) ≤ F[A] (x, u) := by
  -- Insert the concrete graph point `(y, v)` into the defining supremum of `F[A]`.
  rw [SetValuedOperator.fitzpatrickFunction]
  exact le_iSup_of_le ⟨(y, v), by simpa [SetValuedOperator.mem_graph] using hv⟩ (le_of_eq rfl)

/-- Helper for Proposition 25.21: the Fitzpatrick supremand of `A + B` splits into the two
fiberwise summands used by the infimal convolution. -/
private theorem fitzpatrickSupremand_add_split
    (x y u u₁ v₁ v₂ : H) :
    (((⟪y, u⟫_ℝ + ⟪x, v₁ + v₂⟫_ℝ - ⟪y, v₁ + v₂⟫_ℝ : ℝ) : EReal)) =
      (((⟪y, u₁⟫_ℝ + ⟪x, v₁⟫_ℝ - ⟪y, v₁⟫_ℝ : ℝ) : EReal)) +
        (((⟪y, u - u₁⟫_ℝ + ⟪x, v₂⟫_ℝ - ⟪y, v₂⟫_ℝ : ℝ) : EReal)) := by
  -- Expand the pairings and normalize the real identity before coercing to `EReal`.
  exact_mod_cast (show
    ⟪y, u⟫_ℝ + ⟪x, v₁ + v₂⟫_ℝ - ⟪y, v₁ + v₂⟫_ℝ =
      (⟪y, u₁⟫_ℝ + ⟪x, v₁⟫_ℝ - ⟪y, v₁⟫_ℝ) +
        (⟪y, u - u₁⟫_ℝ + ⟪x, v₂⟫_ℝ - ⟪y, v₂⟫_ℝ) by
    rw [inner_add_right, inner_add_right, inner_sub_right]
    ring)

/-- Helper for Proposition 25.21: after splitting a graph point of `A + B`, its Fitzpatrick
supremand is bounded by the corresponding fiber sum of `F[A]` and `F[B]`. -/
private theorem fitzpatrickAddSupremand_le_fiberSum
    {A B : SetValuedOperator H H} (x u u₁ y v₁ v₂ : H)
    (hv₁ : v₁ ∈ A y) (hv₂ : v₂ ∈ B y) :
    (((⟪y, u⟫_ℝ + ⟪x, v₁ + v₂⟫_ℝ - ⟪y, v₁ + v₂⟫_ℝ : ℝ) : EReal)) ≤
      F[A] (x, u₁) + F[B] (x, u - u₁) := by
  -- Rewrite the `A + B` contribution into the two fiberwise Fitzpatrick contributions.
  rw [fitzpatrickSupremand_add_split]
  -- Each split summand is bounded by the corresponding Fitzpatrick supremum.
  exact add_le_add
    (fitzpatrickSupremand_le_of_mem A x u₁ y v₁ hv₁)
    (fitzpatrickSupremand_le_of_mem B x (u - u₁) y v₂ hv₂)

-- Proof sketch: fix `x` and `u`, and take any decomposition `u = u₁ + u₂`. For graph points
-- `(y, v₁) ∈ gra A` and `(y, v₂) ∈ gra B`, the Fitzpatrick supremand of `A + B` at `(x, u)`
-- splits as the sum of the corresponding Fitzpatrick supremands of `A` at `(x, u₁)` and `B` at
-- `(x, u₂)`. Taking suprema over graph points gives
-- `F[A + B] (x, u) ≤ F[A] (x, u₁) + F[B] (x, u₂)`, and then infimizing over all decompositions
-- yields the infimal-convolution bound.
/-- Proposition 25.21: if `A` and `B` are monotone operators on a real Hilbert space, then for
every `x` and `u`, the Fitzpatrick value of the sum operator `A + B` at `(x, u)` is bounded above
by the infimal convolution, in the second variable, of the fixed-`x` fibers of `F[A]` and `F[B]`.
-/
theorem fitzpatrickFunction_add_le_infimalConvolution_fibers
    {A B : SetValuedOperator H H} (hA : A.IsMonotone) (hB : B.IsMonotone) (x u : H) :
    F[(A + B)] (x, u) ≤
      (((fun v : H ↦ F[A] (x, v)) □ (fun v : H ↦ F[B] (x, v))) u) := by
  let _ := hA
  let _ := hB
  -- Rewrite the infimal convolution target into its defining infimum over decompositions.
  rw [ERealFunction.infimalConvolution_apply]
  refine le_iInf fun u₁ ↦ ?_
  -- Unfold `F[A + B]` and control each graph-point summand separately.
  rw [SetValuedOperator.fitzpatrickFunction]
  refine iSup_le fun p ↦ ?_
  rcases p with ⟨⟨y, w⟩, hp⟩
  rw [SetValuedOperator.mem_graph] at hp
  rcases Set.mem_add.mp hp with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
  -- Split the graph point of `A + B` and bound the two pieces by the Fitzpatrick suprema.
  simpa using fitzpatrickAddSupremand_le_fiberSum
    (A := A) (B := B) (x := x) (u := u) (u₁ := u₁) (y := y) (v₁ := v₁) (v₂ := v₂) hv₁ hv₂

end SetValuedOperator
