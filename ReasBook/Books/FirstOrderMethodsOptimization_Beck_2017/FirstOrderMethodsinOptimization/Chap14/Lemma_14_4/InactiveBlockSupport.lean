import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap14.Algorithm_14_8

-- Theorem-local helpers for Lemma 14.4.

noncomputable section

universe u

open scoped Gradient

section

variable {E1 : Type u} {E2 : Type u}
variable [NormedAddCommGroup E1] [NormedAddCommGroup E2]

section X1

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E1] [ProperSpace E1]
variable [NormedSpace ℝ E2]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ)

local notation "F" => two_block_alternating_minimization_objective f.toExtendedReal g1 g2
local notation "Fblocks" => two_block_alternating_minimization_objective_blocks f.toExtendedReal g1 g2
local notation "xkState" => two_block_alternating_minimization_state (x1 k) (x2 k)
local notation "f1" => fun y1 ↦ f (y1, x2 k)
local notation "Fx2" => two_block_alternating_minimization_x2_objective f.toExtendedReal g1 g2 (x1 k)

/-- Helper for Lemma 14.4: the current `x₂`-slice objective is exactly the canonical owner
block-`1` objective at the current two-block state. -/
lemma current_x2_slice_eq_owner_block_objective :
    alternating_minimization_block_objective Fblocks xkState xkState 1 = Fx2 := by
  -- Normalize the owner block objective back to the pair-valued frozen-slice objective.
  funext y2
  simp

/-- Helper for Lemma 14.4: an exact minimizer of the current `x₂`-slice is the same object as an
exact minimizer of the canonical owner block-`1` objective. -/
lemma x2_slice_isMinOn_iff_owner_block_one :
    IsMinOn Fx2 Set.univ (x2 k) ↔
      IsMinOn
        (alternating_minimization_block_objective Fblocks xkState xkState 1)
        Set.univ
        (x2 k) := by
  -- Rewrite the owner block objective through the current two-block state normalization on both
  -- directions of the `IsMinOn` equivalence.
  constructor <;> intro h
  · simpa [current_x2_slice_eq_owner_block_objective] using h
  · simpa [current_x2_slice_eq_owner_block_objective] using h

/-- Helper for Lemma 14.4: the exact inactive `x₂`-minimizer should induce the active-block
support inequality against any competitor. This file isolates the canonical owner-level blocker so
the main file no longer duplicates it in two pair-local proofs. -/
lemma x1_support_of_exact_x2_slice_minimizer_against_any_competitor
    (hF_convex : is_convex_function F)
    (hf_x1_convex : ConvexOn ℝ Set.univ f1)
    (hx2k : IsMinOn Fx2 Set.univ (x2 k))
    (y : E1 × E2) :
    F (x1 k, x2 k) ≤
      (((inner ℝ (∇ f1 (x1 k)) ((x1 k) - y.1) : ℝ) : EReal)) +
        (g1 (x1 k) - g1 y.1) + F y := by
  have hx2_owner :
      IsMinOn
        (alternating_minimization_block_objective Fblocks xkState xkState 1)
        Set.univ
        (x2 k) :=
    (x2_slice_isMinOn_iff_owner_block_one
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (k := k)).mp hx2k
  -- Route correction: the blocker is now isolated at the canonical owner level rather than
  -- repeated as a pair-local `xStar` proof. The missing step is to turn `hx2_owner` together with
  -- convexity of `F` into a full support inequality whose inactive component is zero.
  -- TODO: prove the owner theorem that exact block-`1` minimality for `Fblocks` yields the stated
  -- active-block support inequality after rewriting back through `xkState`.
  let _ := hF_convex
  let _ := hf_x1_convex
  let _ := hx2_owner
  let _ := y
  sorry

end X1

section X2

variable (f : E1 × E2 → ℝ) (g1 : E1 → EReal) (g2 : E2 → EReal)
variable [InnerProductSpace ℝ E2] [ProperSpace E2]
variable [NormedSpace ℝ E1]
variable (x1 : ℕ → E1) (x2 : ℕ → E2) (k : ℕ)

local notation "F" => two_block_alternating_minimization_objective f.toExtendedReal g1 g2
local notation "Fblocks" => two_block_alternating_minimization_objective_blocks f.toExtendedReal g1 g2
local notation "xHalfState" => two_block_alternating_minimization_state (x1 (k + 1)) (x2 k)
local notation "f2" => fun y2 ↦ f (x1 (k + 1), y2)
local notation "Fx1" => two_block_alternating_minimization_x1_objective f.toExtendedReal g1 g2 (x2 k)

/-- Helper for Lemma 14.4: the current `x₁`-slice objective at the half-step is exactly the
canonical owner block-`0` objective. -/
lemma current_x1_slice_eq_owner_block_objective :
    alternating_minimization_block_objective Fblocks xHalfState xHalfState 0 = Fx1 := by
  -- Normalize the owner block objective back to the pair-valued frozen-slice objective.
  funext y1
  simp

/-- Helper for Lemma 14.4: an exact minimizer of the current `x₁`-slice is the same object as an
exact minimizer of the canonical owner block-`0` objective. -/
lemma x1_slice_isMinOn_iff_owner_block_zero :
    IsMinOn Fx1 Set.univ (x1 (k + 1)) ↔
      IsMinOn
        (alternating_minimization_block_objective Fblocks xHalfState xHalfState 0)
        Set.univ
        (x1 (k + 1)) := by
  -- Rewrite the owner block objective through the half-step state normalization on both
  -- directions of the `IsMinOn` equivalence.
  constructor <;> intro h
  · simpa [current_x1_slice_eq_owner_block_objective] using h
  · simpa [current_x1_slice_eq_owner_block_objective] using h

/-- Helper for Lemma 14.4: the exact inactive `x₁`-minimizer should induce the active-block
support inequality against any competitor. This is the symmetric owner-level blocker. -/
lemma x2_support_of_exact_x1_slice_minimizer_against_any_competitor
    (hF_convex : is_convex_function F)
    (hf_x2_convex : ConvexOn ℝ Set.univ f2)
    (hstep1 : IsMinOn Fx1 Set.univ (x1 (k + 1)))
    (y : E1 × E2) :
    F (x1 (k + 1), x2 k) ≤
      (((inner ℝ (∇ f2 (x2 k)) ((x2 k) - y.2) : ℝ) : EReal)) +
        (g2 (x2 k) - g2 y.2) + F y := by
  have hx1_owner :
      IsMinOn
        (alternating_minimization_block_objective Fblocks xHalfState xHalfState 0)
        Set.univ
        (x1 (k + 1)) :=
    (x1_slice_isMinOn_iff_owner_block_zero
      (f := f) (g1 := g1) (g2 := g2) (x1 := x1) (x2 := x2) (k := k)).mp hstep1
  -- Route correction: the symmetric blocker is also reduced to the owner theorem with block `0`
  -- active and block `1` inactive.
  -- TODO: prove the owner theorem that exact block-`0` minimality for `Fblocks` yields the
  -- stated active-block support inequality after rewriting back through `xHalfState`.
  let _ := hF_convex
  let _ := hf_x2_convex
  let _ := hx1_owner
  let _ := y
  sorry

end X2

end

end
