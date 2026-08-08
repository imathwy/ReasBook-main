import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_18
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_27
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric
open scoped BigOperators Pointwise Topology

section SumObjective

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Example 8.36: a nonempty feasible set contained in the interior of every effective
domain yields the relative-interior qualification needed for the finite-sum extendedRealSubdifferential rule.
-/
lemma finset_sum_intrinsicInterior_nonempty_of_nonempty_subset_interior
    {m : ℕ} (f : Fin m → E → EReal) (C : Set E)
    (hC_nonempty : C.Nonempty)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i))) :
    (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (f i))).Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  -- Every feasible point already lies in the interior of each effective domain.
  simp only [Set.mem_iInter]
  intro i
  exact interior_subset_intrinsicInterior (hC_subset i hx)

/-- Helper for Example 8.36: if no summand ever takes the value `⊥`, then neither does their
finite sum. -/
lemma finset_sum_ne_bot
    {m : ℕ} (f : Fin m → E → EReal)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥) :
    ∀ x : E, (∑ i : Fin m, f i x) ≠ ⊥ := by
  induction m with
  | zero =>
      intro x
      simp
  | succ m ih =>
      intro x
      -- Split off the first summand and keep the tail finite by induction.
      rw [Fin.sum_univ_succ, EReal.add_ne_bot_iff]
      exact ⟨hfi_ne_bot 0 x, ih (fun i => f i.succ) (fun i => hfi_ne_bot i.succ) x⟩

/-- Helper for Example 8.36: a point where every summand is finite also lies in the effective
domain of the finite sum objective. -/
lemma finset_sum_ne_top_of_mem_effective_domain
    {m : ℕ} (f : Fin m → E → EReal)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥) :
    ∀ {x : E}, (∀ i : Fin m, x ∈ effective_domain (f i)) → (∑ i : Fin m, f i x) ≠ ⊤ := by
  induction m with
  | zero =>
      intro x hx
      simp
  | succ m ih =>
      intro x hx
      -- Split off the first term and use finiteness of both summands.
      rw [Fin.sum_univ_succ]
      rw [EReal.add_ne_top_iff_ne_top₂ (hfi_ne_bot 0 x)
        (finset_sum_ne_bot (fun i => f i.succ) (fun i => hfi_ne_bot i.succ) x)]
      refine ⟨?_, ?_⟩
      · exact lt_top_iff_ne_top.mp (hx 0)
      · exact ih (fun i => f i.succ) (fun i => hfi_ne_bot i.succ) (fun i => hx i.succ)

/-- Helper for Example 8.36: if `C` lies in the interior of every summand's effective domain,
then `C` also lies in the interior of the finite sum objective's effective domain. -/
lemma finset_sum_subset_interior_effective_domain
    {m : ℕ} (f : Fin m → E → EReal) (C : Set E)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i))) :
    C ⊆ interior (effective_domain (fun y ↦ ∑ i : Fin m, f i y)) := by
  let S : Set E := ⋂ i : Fin m, interior (effective_domain (f i))
  have hS_open : IsOpen S := by
    -- The common interior region is open because the index set is finite.
    simpa [S] using isOpen_iInter_of_finite (fun i : Fin m ↦ isOpen_interior)
  have hS_subset :
      S ⊆ effective_domain (fun y ↦ ∑ i : Fin m, f i y) := by
    intro x hx
    -- On the common interior region, every summand is finite, so the sum stays finite.
    simp only [S, Set.mem_iInter] at hx
    exact lt_top_iff_ne_top.mpr <|
      finset_sum_ne_top_of_mem_effective_domain f hfi_ne_bot (fun i ↦ interior_subset (hx i))
  have hS_interior :
      S ⊆ interior (effective_domain (fun y ↦ ∑ i : Fin m, f i y)) :=
    interior_maximal hS_subset hS_open
  intro x hx
  -- Every feasible point belongs to the common interior region.
  apply hS_interior
  simp only [S, Set.mem_iInter]
  intro i
  exact hC_subset i hx

/-- Helper for Example 8.36: every subgradient of the finite sum objective on `C` has norm bounded
by the sum of the individual subgradient bounds. -/
lemma finset_sum_subgradient_norm_le_on
    {m : ℕ} (f : Fin m → E → EReal) (C : Set E) (L : Fin m → ℝ)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥)
    (hfi_convex : ∀ i : Fin m, is_convex_function (f i))
    (hC_nonempty : C.Nonempty)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i)))
    (hbound : ∀ i : Fin m, ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential (f i) x → ‖g‖ ≤ L i) :
    ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
      x ∈ C →
        g ∈ strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x →
          ‖g‖ ≤ ∑ i : Fin m, L i := by
  intro x g hx hg
  have hqual :=
    finset_sum_intrinsicInterior_nonempty_of_nonempty_subset_interior f C hC_nonempty hC_subset
  -- Rewrite the subgradient of the sum into the pointwise sum of the individual subgradients.
  rw [strongDualSubdifferential_finset_sum_eq_sum_strongDualSubdifferential_of_nonempty_iInter_relativeInterior
    f x hfi_ne_bot hfi_convex hqual] at hg
  rcases (Set.mem_fintype_sum
      (f := fun i : Fin m ↦ strongDualSubdifferential (f i) x) (a := g)).1 hg with
    ⟨g', hg', rfl⟩
  -- Bound the norm of the sum by the sum of the norms, then use the individual estimates.
  calc
    ‖∑ i : Fin m, g' i‖ ≤ ∑ i : Fin m, ‖g' i‖ := by
      simpa using (norm_sum_le (Finset.univ : Finset (Fin m)) g')
    _ ≤ ∑ i : Fin m, L i := by
      exact Finset.sum_le_sum (fun i _ ↦ hbound i hx (hg' i))

-- Proof sketch: the nonempty set `C` sits inside the interior of every effective domain, so it
-- gives the relative-interior qualification required by the finite-sum rule from Theorem 3.18.
-- Decompose any subgradient of the sum as a sum of subgradients of the summands, then apply the
-- triangle inequality together with the pointwise bounds `‖gᵢ‖ ≤ L i`. Positivity of
-- `∑ i, L i` follows from `Finset.sum_pos` because every term is positive and the index set
-- `Finset.univ` is nonempty when `0 < m`.
/-- Example 8.36: if each summand `f i` is convex, the feasible set `C` lies in the interior of
each effective domain, and every subgradient of `f i` on `C` has norm at most `L i > 0`, then the
sum objective `x ↦ ∑ i, f i x` satisfies Assumption 8.12 with Lipschitz constant `∑ i, L i`. -/
theorem finset_sum_satisfies_subgradient_norm_bound
    {m : ℕ} (hm : 0 < m) (f : Fin m → E → EReal) (C : Set E) (L : Fin m → ℝ)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥)
    (hfi_convex : ∀ i : Fin m, is_convex_function (f i))
    (hC_nonempty : C.Nonempty)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i)))
    (hL_pos : ∀ i : Fin m, 0 < L i)
    (hbound : ∀ i : Fin m, ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential (f i) x → ‖g‖ ≤ L i) :
    0 < ∑ i : Fin m, L i ∧
      ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
        x ∈ C →
          g ∈ strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x →
            ‖g‖ ≤ ∑ i : Fin m, L i := by
  constructor
  · let i0 : Fin m := ⟨0, hm⟩
    -- One strictly positive summand already forces the whole finite sum to be positive.
    calc
      0 < L i0 := hL_pos i0
      _ ≤ ∑ i : Fin m, L i := by
        exact Finset.single_le_sum (fun i _ ↦ (hL_pos i).le) (by simp [i0])
  · -- The finite-sum subgradient decomposition gives the desired norm estimate.
    exact
      finset_sum_subgradient_norm_le_on f C L
        hfi_ne_bot hfi_convex hC_nonempty hC_subset hbound

-- Proof sketch: apply Theorem 3.27 to the sum objective. The finite-sum subgradient estimate from
-- `finset_sum_satisfies_subgradient_norm_bound` supplies the uniform bound on
-- `strongDualSubdifferential (fun y ↦ ∑ i, f i y) x` over `C`, and the same interior-domain
-- hypotheses ensure that the sum objective is finite on `C`.
/-- The finite-valued restriction of the sum objective from Example 8.36 is Lipschitz continuous
on `C` with Lipschitz constant `∑ i, L i`. -/
theorem lipschitzOnWith_toReal_finset_sum_of_subgradient_bounds
    {m : ℕ} (f : Fin m → E → EReal) (C : Set E) (L : Fin m → ℝ)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥)
    (hfi_convex : ∀ i : Fin m, is_convex_function (f i))
    (hC_nonempty : C.Nonempty)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i)))
    (hL_pos : ∀ i : Fin m, 0 < L i)
    (hbound : ∀ i : Fin m, ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential (f i) x → ‖g‖ ≤ L i) :
    LipschitzOnWith (Real.toNNReal (∑ i : Fin m, L i))
      (fun x ↦ ((∑ i : Fin m, f i x)).toReal) C := by
  have hsum_subset :
      C ⊆ interior (effective_domain (fun y ↦ ∑ i : Fin m, f i y)) :=
    finset_sum_subset_interior_effective_domain f C hfi_ne_bot hC_subset
  have hsum_nonneg : 0 ≤ ∑ i : Fin m, L i := by
    exact Finset.sum_nonneg (fun i _ ↦ (hL_pos i).le)
  refine lipschitzOnWith_toReal_of_subdifferential_norm_le_on
      (f := fun y ↦ ∑ i : Fin m, f i y)
      (X := C)
      (L := Real.toNNReal (∑ i : Fin m, L i))
      hsum_subset ?_
  intro x hx g hg
  -- Convert the norm estimate for subgradients into the closed-ball inclusion used by Theorem 3.27.
  simpa [mem_closedBall_iff_norm'', Real.toNNReal_of_nonneg hsum_nonneg] using
    finset_sum_subgradient_norm_le_on f C L
      hfi_ne_bot hfi_convex hC_nonempty hC_subset hbound hx hg

end SumObjective

section PackagedBound

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The canonical Chapter 8 subgradient-norm-bound package attached to the finite sum objective in
Example 8.36. -/
def finset_sum_subgradientNormBoundOn
    {m : ℕ} (hm : 0 < m) (f : Fin m → E → EReal) (C : Set E) (L : Fin m → ℝ)
    (hfi_ne_bot : ∀ i : Fin m, ∀ x : E, f i x ≠ ⊥)
    (hfi_convex : ∀ i : Fin m, is_convex_function (f i))
    (hC_nonempty : C.Nonempty)
    (hC_subset : ∀ i : Fin m, C ⊆ interior (effective_domain (f i)))
    (hL_pos : ∀ i : Fin m, 0 < L i)
    (hbound : ∀ i : Fin m, ∀ ⦃x : E⦄, ∀ ⦃g : StrongDual ℝ E⦄,
      x ∈ C → g ∈ strongDualSubdifferential (f i) x → ‖g‖ ≤ L i) :
    SubgradientNormBoundOn (fun y ↦ ∑ i : Fin m, f i y) C :=
  { L_f := ∑ i : Fin m, L i
    L_f_pos :=
      (finset_sum_satisfies_subgradient_norm_bound hm f C L
        hfi_ne_bot hfi_convex hC_nonempty hC_subset hL_pos hbound).1
    norm_le := fun hx hg ↦
      (finset_sum_satisfies_subgradient_norm_bound hm f C L
        hfi_ne_bot hfi_convex hC_nonempty hC_subset hL_pos hbound).2 hx hg }

end PackagedBound

section DiameterBound

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Proof sketch: the map `(x, y) ↦ (1 / 2 : ℝ) * ‖x - y‖^2` is continuous on `E × E`. If `C` is
-- compact, then `C ×ˢ C` is compact as well, so this map is bounded above on `C ×ˢ C`; any such
-- upper bound is the required constant `Θ`.
/-- A compact feasible set admits a finite upper bound on its half squared diameter. -/
theorem exists_half_squared_diameter_bound_of_isCompact
    (C : Set E) (hC_compact : IsCompact C) :
    ∃ Θ : ℝ, ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ := by
  let φ : E × E → ℝ := fun p ↦ (1 / 2 : ℝ) * ‖p.1 - p.2‖ ^ (2 : ℕ)
  have hφ_cont : Continuous φ := by
    -- The half-squared-distance map is built from continuous algebraic operations.
    continuity
  rcases bddAbove_def.mp ((hC_compact.prod hC_compact).bddAbove_image hφ_cont.continuousOn) with
    ⟨Θ, hΘ⟩
  refine ⟨Θ, ?_⟩
  intro x hx y hy
  -- Evaluate the bounded-above image estimate at the pair `(x, y) ∈ C ×ˢ C`.
  have hxy : φ (x, y) ∈ φ '' (C ×ˢ C) := by
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  simpa [φ] using hΘ (φ (x, y)) hxy

-- Proof sketch: every optimal point `xStar ∈ XStar` lies in `C` by `hXStar_subset`, while the
-- initial point `x0` is a point of `C` by construction. Apply the half squared diameter bound
-- `hΘ` to the pair `((x0 : E), xStar)`.
/-- Any half squared diameter bound on `C` controls the initial-distance term to an optimal point,
which is the quantity appearing in projected-subgradient complexity estimates. -/
theorem half_sqdist_to_optimal_point_le_of_half_squared_diameter_bound
    (C XStar : Set E) {Θ : ℝ}
    (hXStar_subset : XStar ⊆ C)
    (hΘ : ∀ x ∈ C, ∀ y ∈ C, (1 / 2 : ℝ) * ‖x - y‖ ^ (2 : ℕ) ≤ Θ)
    (x0 : C) {xStar : E} (hxStar : xStar ∈ XStar) :
    (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) ≤ Θ := by
  -- Both the initial point and the chosen optimal point belong to `C`, so specialize `hΘ`.
  exact hΘ (x0 : E) x0.property xStar (hXStar_subset hxStar)

end DiameterBound
