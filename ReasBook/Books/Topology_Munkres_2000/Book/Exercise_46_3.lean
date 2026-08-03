module

public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.UniformSpace.CompactConvergence

public section

open Set
open scoped UniformConvergence

/-- Helper for Exercise 46.3: a uniformly bounded perturbation of a function with bounded range
also has bounded range. -/
lemma isBounded_range_of_pointwise_dist_le {α β : Type*} [PseudoMetricSpace β]
    (f g : α → β) (C : ℝ) (hfg : ∀ x, dist (f x) (g x) ≤ C)
    (hf : Bornology.IsBounded (range f)) : Bornology.IsBounded (range g) := by
  -- Convert boundedness of each range into a uniform bound on pairwise distances.
  rw [Metric.isBounded_range_iff] at hf ⊢
  obtain ⟨D, hD⟩ := hf
  refine ⟨D + C + C, fun x y ↦ ?_⟩
  -- Compare two values of `g` through the corresponding values of `f`.
  calc
    dist (g x) (g y) ≤ dist (g x) (f x) + dist (f x) (f y) + dist (f y) (g y) :=
      dist_triangle4 (g x) (f x) (f y) (g y)
    _ ≤ C + D + C := by
      gcongr
      · simpa [dist_comm] using hfg x
      · exact hD x y
      · exact hfg y
    _ = D + C + C := by ring

/-- Helper for Exercise 46.3: truncating the identity to zero outside a bounded set has bounded
range. -/
lemma isBounded_range_compactTruncation (K : Set ℝ) [DecidablePred (· ∈ K)]
    (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (range fun x : ℝ ↦ if x ∈ K then x else 0) := by
  -- The truncated range is contained in the bounded set obtained by adjoining zero to `K`.
  refine (hK.insert 0).subset ?_
  rintro y ⟨x, rfl⟩
  by_cases hx : x ∈ K
  · change (if x ∈ K then x else 0) ∈ insert 0 K
    rw [if_pos hx]
    exact Or.inr hx
  · change (if x ∈ K then x else 0) ∈ insert 0 K
    rw [if_neg hx]
    exact Or.inl rfl

/-- Helper for Exercise 46.3: the bounded functions `ℝ → ℝ` form a closed subset in the topology
of uniform convergence. -/
theorem isClosed_boundedFunctions_uniform :
    IsClosed {f : ℝ →ᵤ ℝ | Bornology.IsBounded (range f)} := by
  -- Around an unbounded function, the radius-one uniform neighborhood contains only
  -- unbounded functions, so the complement is open.
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro f hf
  refine (UniformFun.hasBasis_nhds_of_basis ℝ ℝ f Metric.uniformity_basis_dist).mem_iff.mpr ?_
  refine ⟨1, zero_lt_one, ?_⟩
  intro g hg
  simp only [mem_compl_iff, mem_setOf_eq] at hf ⊢
  intro hgBounded
  apply hf
  -- Reverse the radius-one pointwise estimate and transfer boundedness from `g` to `f`.
  refine isBounded_range_of_pointwise_dist_le (UniformFun.toFun g) (UniformFun.toFun f) 1 ?_ ?_
  · intro x
    have hx := hg x
    change dist (UniformFun.toFun f x) (UniformFun.toFun g x) < 1 at hx
    simpa only [dist_comm] using hx.le
  · exact hgBounded

/-- Helper for Exercise 46.3: the identity function belongs to the compact-convergence closure of
the functions with bounded range. -/
lemma identity_mem_closure_boundedFunctions_compactConvergence :
    UniformOnFun.ofFun {K : Set ℝ | IsCompact K} (fun x : ℝ ↦ x) ∈
      closure {f : ℝ →ᵤ[{K : Set ℝ | IsCompact K}] ℝ |
        Bornology.IsBounded (range f)} := by
  classical
  have hNonempty : ({K : Set ℝ | IsCompact K} : Set (Set ℝ)).Nonempty :=
    ⟨∅, isCompact_empty⟩
  have hDirected : DirectedOn (· ⊆ ·) ({K : Set ℝ | IsCompact K} : Set (Set ℝ)) :=
    directedOn_of_sup_mem fun _ _ ↦ IsCompact.union
  -- It suffices to meet every basic neighborhood of the identity.
  rw [mem_closure_iff_nhds_basis
    (UniformOnFun.hasBasis_nhds ℝ ℝ {K : Set ℝ | IsCompact K} _ hNonempty hDirected)]
  intro SV hSV
  obtain ⟨hK, hV⟩ := hSV
  let truncation : ℝ → ℝ := fun x ↦ if x ∈ SV.1 then x else 0
  refine ⟨UniformOnFun.ofFun {K : Set ℝ | IsCompact K} truncation, ?_, ?_⟩
  · -- Compactness bounds the truncation's range.
    change Bornology.IsBounded (range truncation)
    exact isBounded_range_compactTruncation SV.1 hK.isBounded
  · -- On the selected compact set the truncation equals the identity, hence is in the entourage.
    intro x hx
    simpa only [UniformOnFun.toFun_ofFun, truncation, if_pos hx] using
      (refl_mem_uniformity hV : (x, x) ∈ SV.2)

/-- Helper for Exercise 46.3: the bounded functions `ℝ → ℝ` do not form a closed subset in the
topology of uniform convergence on compact subsets. -/
theorem not_isClosed_boundedFunctions_compactConvergence :
    ¬ IsClosed {f : ℝ →ᵤ[{K : Set ℝ | IsCompact K}] ℝ |
      Bornology.IsBounded (range f)} := by
  intro hClosed
  -- Closedness would force the identity, already in the closure, to have bounded range.
  have hIdentityBounded := hClosed.closure_subset
    identity_mem_closure_boundedFunctions_compactConvergence
  -- Its range is all of `ℝ`; a supposed diameter bound is violated by two sufficiently distant
  -- real numbers.
  change Bornology.IsBounded (range fun x : ℝ ↦ x) at hIdentityBounded
  rw [Metric.isBounded_range_iff] at hIdentityBounded
  obtain ⟨C, hC⟩ := hIdentityBounded
  have hCNonneg : 0 ≤ C := by
    simpa using hC 0 0
  have hFar := hC 0 (C + 1)
  have hCPlusOneNonneg : 0 ≤ C + 1 := by
    linarith
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hCPlusOneNonneg] at hFar
  linarith

/-- Exercise 46.3: the bounded functions `ℝ → ℝ` are closed for uniform convergence but not for
uniform convergence on compact subsets. -/
theorem boundedFunctions_closed_uniform_not_closed_compactConvergence :
    IsClosed {f : ℝ →ᵤ ℝ | Bornology.IsBounded (range f)} ∧
      ¬ IsClosed {f : ℝ →ᵤ[{K : Set ℝ | IsCompact K}] ℝ |
        Bornology.IsBounded (range f)} := by
  -- Combine the two topology-specific conclusions proved above.
  exact ⟨isClosed_boundedFunctions_uniform,
    not_isClosed_boundedFunctions_compactConvergence⟩
