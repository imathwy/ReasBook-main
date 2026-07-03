import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_8_1 (from Chap08) -/
universe u

open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 8.1: in this chapter, an abstract Euclidean space is modeled by the canonical real
inner-product-space owner `InnerProductSpace ℝ E`; the finite-dimensionality hypothesis and the
derived Euclidean norm formula are recalled below as companion views. -/
#check InnerProductSpace ℝ E

/- Finite-dimensionality is the remaining Euclidean-space hypothesis, encoded by the canonical
typeclass `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- The Euclidean norm is canonically derived from the ambient real inner product, identified with
`√⟪x, x⟫_ℝ` by `norm_eq_sqrt_real_inner`. -/
#check norm_eq_sqrt_real_inner

end

/-! ### Proposition_8_1 (from Chap08) -/
universe u v

section

variable {E : Type u} {ι : Type v} [PseudoMetricSpace E] [Fintype ι] [Nonempty ι]

/-- The pointwise maximum of the distances to the sets in a finite family. -/
noncomputable def max_infDist_to_family (S : ι → Set E) : E → ℝ :=
  fun x ↦ Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i))

/-- Helper for Proposition 8.1: the local max-distance objective is exactly the Chapter 8 owner
`convex_feasibility_max_distance`. -/
theorem max_infDist_to_family_eq_convex_feasibility_max_distance (S : ι → Set E) :
    max_infDist_to_family S = convex_feasibility_max_distance S := by
  -- Both source-facing objectives are the same finite maximum of point-to-set distances.
  rfl

-- Proof sketch: unfold `max_infDist_to_family`.
/-- Evaluating `max_infDist_to_family S` at `x` gives the finite maximum of the distances from
`x` to the sets `S i`. -/
@[simp] theorem max_infDist_to_family_apply (S : ι → Set E) (x : E) :
    max_infDist_to_family S x =
      Finset.univ.sup' Finset.univ_nonempty (fun i ↦ Metric.infDist x (S i)) := by
  -- Unfold the local source-facing definition to read off its value at `x`.
  rfl

/-- Helper for Proposition 8.1: the max-distance objective is everywhere nonnegative. -/
theorem max_infDist_to_family_nonneg (S : ι → Set E) (x : E) :
    0 ≤ max_infDist_to_family S x := by
  -- Rewrite to the finite maximum and compare `0` with one coordinate distance first.
  rw [max_infDist_to_family_apply]
  obtain ⟨i, hi⟩ := (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  exact le_trans
    (Metric.infDist_nonneg (x := x) (s := S i))
    (Finset.le_sup' (s := (Finset.univ : Finset ι))
      (f := fun j ↦ Metric.infDist x (S j)) hi)

-- Proof sketch: each term `Metric.infDist x (S i)` vanishes because `x ∈ S i`, so the finite
-- maximum of these distances is `0`.
/-- A point in the total intersection has zero maximum distance to the family. -/
theorem max_infDist_to_family_eq_zero_of_mem_iInter
    (S : ι → Set E) {x : E} (hx : x ∈ ⋂ i, S i) :
    max_infDist_to_family S x = 0 := by
  -- Rewrite to the finite maximum and show that each coordinate distance vanishes.
  rw [max_infDist_to_family_apply]
  refine Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset ι))
    (H := Finset.univ_nonempty)
    (f := fun i ↦ Metric.infDist x (S i))
    (a := 0) ?_
  intro i hi
  -- Membership in each set collapses each point-to-set distance to zero.
  exact Metric.infDist_zero_of_mem ((Set.mem_iInter.mp hx) i)

-- Proof sketch: if `x` minimizes the objective, then the value must be `0` by the nonempty
-- intersection hypothesis. Since each set is closed, `Metric.infDist x (S i) = 0` implies
-- `x ∈ S i`, so every minimizer lies in `⋂ i, S i`. Conversely, every point of `⋂ i, S i` has
-- objective value `0`, hence is optimal.
/-- Proposition 8.1 (1): if a finite family of closed sets has nonempty intersection, then the
global minimizer set of the pointwise maximum of the distance functions is exactly that
intersection. -/
theorem global_minimizers_max_infDist_to_family
    (S : ι → Set E) (hclosed : ∀ i, IsClosed (S i))
    (hnonempty : (⋂ i, S i).Nonempty) :
    {x | IsMinOn (max_infDist_to_family S) Set.univ x} = ⋂ i, S i := by
  ext x
  -- Rewrite the minimization problem to the canonical owner and use its exact characterization.
  simpa [max_infDist_to_family_eq_convex_feasibility_max_distance S] using
    (isMinOn_convex_feasibility_max_distance_iff_mem_iInter
      (S := S) hclosed hnonempty (x := x))

-- Proof sketch: the nonempty intersection provides a point where the objective equals `0`, so the
-- infimum is at most `0`. Every distance is nonnegative, hence the objective is nonnegative
-- everywhere, giving the reverse inequality and therefore optimal value `0`.
/-- Proposition 8.1 (2): if the total intersection is nonempty, then the optimal value of the
pointwise maximum of the distance functions is `0`. -/
theorem sInf_range_max_infDist_to_family_eq_zero
    (S : ι → Set E) (hnonempty : (⋂ i, S i).Nonempty) :
    sInf (Set.range (max_infDist_to_family S)) = 0 := by
  rcases hnonempty with ⟨x, hx⟩
  have hzero_mem : 0 ∈ Set.range (max_infDist_to_family S) := by
    -- A feasible point from the total intersection realizes the value `0`.
    exact ⟨x, max_infDist_to_family_eq_zero_of_mem_iInter S hx⟩
  have hbounded : BddBelow (Set.range (max_infDist_to_family S)) := by
    -- Nonnegativity of each distance term makes `0` a global lower bound for the range.
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨z, rfl⟩
    exact max_infDist_to_family_nonneg S z
  refine le_antisymm ?_ ?_
  · -- The feasible witness places `0` inside the range, so the infimum is at most `0`.
    exact csInf_le hbounded hzero_mem
  · -- The lower bound `0` on the whole range pushes the infimum back above `0`.
    refine le_csInf ?_ ?_
    · exact ⟨0, hzero_mem⟩
    · intro y hy
      rcases hy with ⟨z, rfl⟩
      exact max_infDist_to_family_nonneg S z

-- Proof sketch: each function `x ↦ Metric.infDist x (S i)` is `1`-Lipschitz by
-- `Metric.lipschitz_infDist_pt`. Repeatedly combine these bounds using the fact that the maximum
-- of finitely many `1`-Lipschitz real-valued functions is again `1`-Lipschitz.
/-- Proposition 8.1 (3): the pointwise maximum of the distance functions is Lipschitz continuous
with constant `1`. -/
theorem lipschitzWith_max_infDist_to_family (S : ι → Set E) :
    LipschitzWith 1 (max_infDist_to_family S) := by
  -- Control the finite maximum by the coordinatewise inf-distance estimate from mathlib.
  refine LipschitzWith.of_le_add fun x y ↦ ?_
  rw [max_infDist_to_family_apply, max_infDist_to_family_apply]
  refine Finset.sup'_le _ _ fun i hi ↦ ?_
  -- Each coordinate distance changes by at most `dist x y`, so the same is true for the maximum.
  exact le_trans
    (Metric.infDist_le_infDist_add_dist (x := x) (y := y) (s := S i))
    (add_le_add_left
      (Finset.le_sup' (s := (Finset.univ : Finset ι))
        (f := fun j ↦ Metric.infDist y (S j)) hi)
      _)

end

/-! ### Theorem_8_1 (from Chap08) -/
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
  -- Apply the Chapter 3 compact-union theorem to the global subdifferential union.
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
