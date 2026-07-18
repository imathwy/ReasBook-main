import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_5
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap03.Theorem_3_27
import FirstOrderMethodsOptimization_Beck_2017.FirstOrderMethodsinOptimization.Chap08.Assumption_8_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric
open Bornology

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 8.1: a packaged subgradient norm bound places every subgradient over `C`
in the dual closed ball centered at `0` with radius `Real.toNNReal hbound.L_f`. -/
lemma subgradientNormBoundOn_closedBall_inclusion
    (f : E → EReal) (C : Set E) (hbound : SubgradientNormBoundOn f C) :
    ∀ ⦃x : E⦄, x ∈ C →
      strongDualSubdifferential f x ⊆
        closedBall (0 : StrongDual ℝ E) (Real.toNNReal hbound.L_f) := by
  intro x hx g hg
  -- Rewrite closed-ball membership into the norm inequality supplied by `hbound`.
  simpa [mem_closedBall_iff_norm'', Real.toNNReal_of_nonneg hbound.L_f_pos.le] using
    hbound.norm_le hx hg

/-- Helper for Theorem 8.1: compactness of `C` gives one closed ball that contains the union of all
continuous-dual subdifferentials over `C`. -/
lemma subgradient_biUnion_subset_closedBall_of_isCompact
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_subset : C ⊆ interior (effective_domain f)) :
    ∃ R : ℝ,
      (⋃ x ∈ C, strongDualSubdifferential f x) ⊆ closedBall (0 : StrongDual ℝ E) R := by
  -- Apply the Chapter 3 compact-union theorem to the global extendedRealSubdifferential union.
  rcases subdifferential_biUnion_nonempty_and_isBounded_of_isCompact_subset_interior
      (f := f) (X := C) hf_proper.ne_bot hf_convex hC_nonempty hC_compact hC_subset with
    ⟨_, hYbounded⟩
  -- Convert boundedness into containment in a single closed ball.
  exact hYbounded.subset_closedBall (0 : StrongDual ℝ E)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 8.1: a closed-ball bound on the union of subdifferentials yields the
pointwise norm estimate needed for the Chapter 8 packaged hypothesis. -/
lemma norm_le_of_mem_subgradient_biUnion_closedBall
    (f : E → EReal) (C : Set E) {R : ℝ}
    (hR : (⋃ x ∈ C, strongDualSubdifferential f x) ⊆ closedBall (0 : StrongDual ℝ E) R) :
    ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential f x → ‖g‖ ≤ max R 1 := by
  intro x g hx hg
  have hg_union : g ∈ ⋃ x ∈ C, strongDualSubdifferential f x := by
    -- Place `g` into the global union using its base point `x ∈ C`.
    simp only [Set.mem_iUnion]
    exact ⟨x, hx, hg⟩
  have hg_ball : g ∈ closedBall (0 : StrongDual ℝ E) R := hR hg_union
  have hnorm : ‖g‖ ≤ R := by
    -- Read closed-ball membership back as a norm bound at the origin.
    simpa [mem_closedBall_iff_norm''] using hg_ball
  exact hnorm.trans (le_max_left R 1)

/- Theorem 8.1 is a `bridge/view` item. Its first clause is the Chapter 8 specialization of the
canonical Chapter 3 owner theorem `lipschitzOnWith_toReal_of_subdifferential_norm_le_on`, with the
bounded-subgradient hypothesis packaged by `SubgradientNormBoundOn`. Its compactness clause is the
converse existence bridge from the compact-union boundedness theorem of Chapter 3 back to the
Chapter 8 assumption package. -/

-- Proof sketch: apply `lipschitzOnWith_toReal_of_subdifferential_norm_le_on` to `f` and `C`.
-- The properness hypothesis supplies the no-`⊥` condition on the effective domain, the convexity
-- hypothesis is exactly the owner convexity assumption, and `hbound` converts the Chapter 8
-- subgradient norm bound into the closed-ball inclusion required by Theorem 3.27.
/-- Theorem 8.1: if a proper convex extended-real-valued function has uniformly bounded
subgradients on a set `C` contained in `interior (effective_domain f)`, then `x ↦ (f x).toReal`
is Lipschitz on `C` with Lipschitz constant `L_f`. -/
theorem lipschitzOnWith_toReal_of_subgradientNormBoundOn
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f)
    (hC_subset : C ⊆ interior (effective_domain f))
    (hbound : SubgradientNormBoundOn f C) :
    LipschitzOnWith (Real.toNNReal hbound.L_f) (fun x ↦ (f x).toReal) C := by
  -- Keep the textbook hypotheses visible in this Chapter 8 bridge theorem.
  let _ := hf_proper
  let _ := hf_convex
  -- Specialize the Chapter 3 owner theorem with the closed-ball inclusion induced by `hbound`.
  refine lipschitzOnWith_toReal_of_subdifferential_norm_le_on
      (f := f) (X := C) (L := Real.toNNReal hbound.L_f) hC_subset ?_
  -- The packaged Chapter 8 hypothesis already gives the required pointwise closed-ball control.
  exact subgradientNormBoundOn_closedBall_inclusion f C hbound

-- Proof sketch: apply
-- `subdifferential_biUnion_nonempty_and_isBounded_of_isCompact_subset_interior` to the compact
-- feasible set `C`. Use the resulting boundedness of `⋃ x ∈ C, strongDualSubdifferential f x` to
-- obtain a common radius controlling all subgradients over `C`, and then enlarge that radius if
-- necessary so the final bound constant is strictly positive.
/-- A compact set contained in `interior (effective_domain f)` admits a uniform positive bound on
the norms of all subgradients of a proper convex extended-real-valued function. -/
theorem exists_pos_subgradient_norm_bound_of_isCompact_subset_interior
    (f : E → EReal) (C : Set E) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) (hC_nonempty : C.Nonempty) (hC_compact : IsCompact C)
    (hC_subset : C ⊆ interior (effective_domain f)) :
    ∃ L_f : ℝ, 0 < L_f ∧
      ∀ ⦃x : E⦄ ⦃g : StrongDual ℝ E⦄,
        x ∈ C → g ∈ strongDualSubdifferential f x → ‖g‖ ≤ L_f := by
  -- First control the global union of subdifferentials over the compact feasible set.
  rcases subgradient_biUnion_subset_closedBall_of_isCompact
      f C hf_proper hf_convex hC_nonempty hC_compact hC_subset with ⟨R, hR⟩
  refine ⟨max R 1, ?_, ?_⟩
  · -- Enlarge the radius to `max R 1` so the final bound is automatically strictly positive.
    exact lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  · -- Convert the global closed-ball control back into the desired pointwise norm estimate.
    exact norm_le_of_mem_subgradient_biUnion_closedBall f C hR

end
