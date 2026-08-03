import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Example_6_43
import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Theorem_16_3
import BauschkeLean.Chap16.Proposition_16_44
import BauschkeLean.Chap16.Corollary_16_50
import BauschkeLean.Chap20.Theorem_20_25
import BauschkeLean.Chap26.Theorem_26_9

open Set
open Filter
open SetValuedOperator
open scoped InnerProductSpace Pointwise SetValuedOperator Topology

universe u

namespace ERealFunction

-- Semantic recall: `lean_leansearch` surfaced only generic orthogonal-projection infrastructure
-- here. The source-facing recursion `(28.9)` is therefore kept explicitly, while the reusable
-- convergence engine remains the Chapter 26 partial-inverse orbit and solution owners.
--
-- Source/core/bridge triage:
-- - `source-facing`: `IsSpingarnProximalSubspaceOrbit` and Proposition 28.2 itself.
-- - `core/canonical`: `IsSpingarnPartialInverseOrbit` and `IsSpingarnPartialInverseSolution`.
-- - `bridge/view`: `SubspaceConstraintRegularity`, the subdifferential specialization of the
--   orbit recursion, and the constrained-argmin/partial-inverse equivalence for the subspace
--   constraint `V`.

section SpingarnPartialInverses

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A quadruple of sequences `x`, `u`, `y`, `v` satisfies the source recursion `(28.9)` for the
subspace-constrained minimization problem for `f` over `V`. -/
structure IsSpingarnProximalSubspaceOrbit
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x0 u0 : H) (x u y v : ℕ → H) : Prop where
  /-- The initial primal iterate belongs to `V`. -/
  x0_mem : x0 ∈ V
  /-- The initial dual iterate belongs to `Vᗮ`. -/
  u0_mem : u0 ∈ Vᗮ
  /-- The primal orbit starts at the prescribed point `x0`. -/
  x_zero : x 0 = x0
  /-- The dual orbit starts at the prescribed point `u0`. -/
  u_zero : u 0 = u0
  /-- The proximal step is `y n = Prox_f (x n + u n)`. -/
  y_eq : ∀ n : ℕ, y n = Prox[f, hf] (x n + u n)
  /-- The residual is `v n = x n + u n - y n`. -/
  v_eq : ∀ n : ℕ, v n = x n + u n - y n
  /-- The next primal iterate is the projection of `y n` onto `V`. -/
  x_succ_eq : ∀ n : ℕ, x (n + 1) = V.starProjection (y n)
  /-- The next dual iterate is the projection of `v n` onto `Vᗮ`. -/
  u_succ_eq : ∀ n : ℕ, u (n + 1) = Vᗮ.starProjection (v n)

namespace IsSpingarnProximalSubspaceOrbit

/-- The source recursion `(28.9)` is the Chapter 26 Spingarn orbit specialized to the
subdifferential operator `∂ f`. -/
theorem toIsSpingarnPartialInverseOrbit
    {f : H → Set.Ioi (⊥ : EReal)} {hf : f ∈ Γ₀(H)} {V : Submodule ℝ H}
    [V.HasOrthogonalProjection] {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnProximalSubspaceOrbit hf V x0 u0 x u y v) :
    IsSpingarnPartialInverseOrbit (∂ f) V x0 u0 x u y v := by
  refine
    { x0_mem := hOrbit.x0_mem
      u0_mem := hOrbit.u0_mem
      x_zero := hOrbit.x_zero
      u_zero := hOrbit.u_zero
      v_eq := hOrbit.v_eq
      v_mem := ?_
      x_succ_eq := hOrbit.x_succ_eq
      u_succ_eq := hOrbit.u_succ_eq }
  intro n
  -- Rewrite the proximal step as the standard subdifferential characterization of `Prox_f`.
  simpa [hOrbit.y_eq n, hOrbit.v_eq n] using
    (eq_proximityOperator_iff_sub_mem_subdifferential
      hf (x n + u n) (Prox[f, hf] (x n + u n))).1 rfl

end IsSpingarnProximalSubspaceOrbit

/-- The source regularity hypothesis in Proposition 28.2: `0 ∈ sri (V - dom f)`. -/
def SubspaceConstraintRegularity
    (f : H → Set.Ioi (⊥ : EReal)) (V : Submodule ℝ H) : Prop :=
  (0 : H) ∈ sri ((V : Set H) - effectiveDomain f)

/-- Helper for Proposition 28.2: the zero-set condition for `N[C] + ∂ f` is equivalent to an
explicit subgradient witness whose negative lies in the normal cone. -/
private theorem mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H} {xbar : H} :
    xbar ∈ ((N[C]) + (∂ f)).zeros ↔
      ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[C] xbar := by
  rw [SetValuedOperator.mem_zeros_iff]
  change 0 ∈ N[C] xbar + (∂ f) xbar ↔
    ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[C] xbar
  rw [Set.mem_add]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    have hu' : u = -v := by
      simpa using eq_neg_of_add_eq_zero_left huv
    have hneg : -v ∈ N[C] xbar := by
      simpa [hu'] using hu
    exact ⟨v, hv, hneg⟩
  · rintro ⟨u, hu, hneg⟩
    exact ⟨-u, hneg, u, hu, by simp⟩

/-- Helper for Proposition 28.2: every zero of `(∂ f) + (∂ g)` minimizes `f + g`. -/
private theorem mem_argmin_of_mem_zeros_subdifferential_add
    {f g : H → Set.Ioi (⊥ : EReal)} {xbar : H}
    (hxzero : xbar ∈ ((∂ f) + (∂ g)).zeros) :
    xbar ∈ Argmin (f + g).asEReal := by
  have hxsub :
      xbar ∈ (∂ (f + g) : SetValuedOperator H H).zeros := by
    rw [SetValuedOperator.mem_zeros_iff] at hxzero ⊢
    exact
      subdifferential_add_adjoint_image_subset_subdifferential_add_comp
        f g (ContinuousLinearMap.id ℝ H) xbar
        (by simpa [ContinuousLinearMap.adjointImageSubdifferential] using hxzero)
  -- Fermat's rule closes the unconstrained minimization problem for `f + g`.
  simpa [argmin_eq_zeros_subdifferential] using hxsub

/-- Helper for Proposition 28.2: the indicator of a nonempty closed convex set belongs to
`Γ₀(H)`. This keeps the proof dependency local and avoids the conflicting Chapter 12 owner import
in this snapshot. -/
private theorem indicator_mem_gammaZero_closedConvex_local
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    ι[C] ∈ Γ₀(H) := by
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[C]) y : EReal)) := by
    -- Closedness of `C` is exactly lower semicontinuity of its indicator.
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed C).2 hC_closed
  have hindicator_dom : effectiveDomain (ι[C]) = C := by
    -- The effective domain of an indicator is the underlying set itself.
    ext y
    by_cases hy : y ∈ C <;> simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hindicator_dom] using hC_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyC : y ∈ C := by
    simpa [hindicator_dom] using hy
  have hzC : z ∈ C := by
    simpa [hindicator_dom] using hz
  have hayzC : a • y + (1 - a) • z ∈ C :=
    hC_convex hyC hzC ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  -- Convexity of `C` makes the indicator satisfy the convexity inequality.
  simp [ERealFunction.indicator, hyC, hzC, hayzC]

/-- Helper for Proposition 28.2: under the strong-relative-interior constraint qualification,
the subdifferential of `f + ι[C]` splits as the normal cone of `C` plus `∂ f`. -/
private theorem subdifferential_add_indicator_eq_normalCone_add_subdifferential_of_zero_mem_sri
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hsri : (0 : H) ∈ sri (C - effectiveDomain f)) :
    (∂ (f + ι[C]) : SetValuedOperator H H) = (N[C]) + (∂ f) := by
  have hC_nonempty : C.Nonempty := by
    -- The strong relative interior hypothesis already places `0` in `C - dom f`.
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
    rcases Set.mem_sub.mp hzero with ⟨x, hxC, _, _, _⟩
    exact ⟨x, hxC⟩
  have hindicator : ι[C] ∈ Γ₀(H) :=
    indicator_mem_gammaZero_closedConvex_local hC_nonempty hC_closed hC_convex
  have hsri_indicator :
      (0 : H) ∈ sri (effectiveDomain (ι[C]) - effectiveDomain f) := by
    -- Swap the summands so that the public Chapter 16 sum rule matches the given hypothesis.
    simpa [effectiveDomain_indicator] using hsri
  have hsum :
      (∂ (ι[C] + f) : SetValuedOperator H H) = (∂ ι[C]) + (∂ f) :=
    subdifferential_add_eq_add_of_zero_mem_sri_sub_effectiveDomain
      hindicator hf hsri_indicator
  -- Rewrite the indicator subdifferential as the normal cone and commute the pointwise sum.
  simpa [pointwiseAdd_apply, add_comm,
    subdifferential_setIndicator_eq_normalCone C hC_nonempty] using hsum

/-- Helper for Proposition 28.2: the `zero_mem_sri` branch of Proposition 27.8 specialized to a
closed convex constraint set `C`. -/
private theorem mem_argminOn_iff_mem_zeros_normalCone_add_subdifferential_of_zero_mem_sri
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {C : Set H} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hsri : (0 : H) ∈ sri (C - effectiveDomain f)) {xbar : H} :
    xbar ∈ Argmin[C] f.asEReal ↔
      xbar ∈ ((N[C]) + (∂ f)).zeros := by
  have hC_nonempty : C.Nonempty := by
    -- The strong relative interior hypothesis already places `0` in `C - dom f`, hence `C`
    -- contains the first component of a difference representation of `0`.
    rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
    rcases Set.mem_sub.mp hzero with ⟨x, hxC, _, _, _⟩
    exact ⟨x, hxC⟩
  have hbot : ∀ x ∉ C, (f x : EReal) ≠ ⊥ := by
    intro x hx
    exact ne_of_gt (f x).2
  rw [argminOn_eq_inter_argmin_add_indicator f.asEReal C hbot]
  constructor
  · rintro ⟨hxC, hxarg⟩
    have hxarg' : xbar ∈ Argmin (f + ι[C]).asEReal := by
      -- Normalize the pointwise sum so Fermat's rule sees the canonical owner `f + ι[C]`.
      simpa [pointwiseAdd_apply] using hxarg
    have hxsub :
        xbar ∈ (∂ (f + ι[C]) : SetValuedOperator H H).zeros := by
      -- Fermat's rule turns the unconstrained minimizer of `f + ι[C]` into a zero of its
      -- subdifferential.
      simpa [argmin_eq_zeros_subdifferential] using hxarg'
    -- Route correction: rewrite `∂ (f + ι[C])` through the Chapter 16 sum rule applied in the
    -- safe order `(ι[C], f)` instead of the broken Chapter 27 owner route.
    rw [subdifferential_add_indicator_eq_normalCone_add_subdifferential_of_zero_mem_sri
      hf hC_closed hC_convex hsri] at hxsub
    exact hxsub
  · intro hxzero
    have hxzero' :
        xbar ∈ ((∂ f) + (∂ ι[C])).zeros := by
      -- Convert the normal-cone witness back into the indicator-subdifferential form.
      rw [SetValuedOperator.mem_zeros_iff] at hxzero ⊢
      change 0 ∈ N[C] xbar + (∂ f) xbar at hxzero
      change 0 ∈ (∂ f) xbar + (∂ ι[C]) xbar
      rw [subdifferential_setIndicator_eq_normalCone C hC_nonempty]
      rw [Set.mem_add] at hxzero ⊢
      rcases hxzero with ⟨u, hu, v, hv, huv⟩
      have hsum : v + u = 0 := by
        simpa [add_comm] using huv
      exact ⟨v, hv, u, hu, hsum⟩
    have hxarg : xbar ∈ Argmin (f.asEReal + (ι[C]).asEReal) := by
      -- The general zero-set helper turns the split subdifferential witness into a minimizer.
      exact mem_argmin_of_mem_zeros_subdifferential_add hxzero'
    have hxC : xbar ∈ C := by
      -- A zero of `N[C] + ∂ f` must lie in `C` because the normal cone is empty off `C`.
      by_contra hxC
      rw [SetValuedOperator.mem_zeros_iff] at hxzero
      change 0 ∈ N[C] xbar + (∂ f) xbar at hxzero
      rw [Set.normalCone_of_not_mem hxC, Set.mem_add] at hxzero
      simpa using hxzero
    exact ⟨hxC, hxarg⟩

/-- Helper for Proposition 28.2: the affine normal-cone witness for the linear subspace
constraint `V` is exactly feasibility together with a subgradient in `Vᗮ`. -/
private theorem exists_mem_subdifferential_neg_normalCone_subspace_iff
    {f : H → Set.Ioi (⊥ : EReal)} {V : Submodule ℝ H} {xbar : H} :
    (∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[(AffineSubspace.mk' (0 : H) V : Set H)] xbar) ↔
      xbar ∈ V ∧ (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) := by
  constructor
  · rintro ⟨u, hu, hneg⟩
    by_cases hxC : xbar ∈ (AffineSubspace.mk' (0 : H) V : Set H)
    · -- On the affine subspace `0 + V`, the normal cone is exactly `Vᗮ`.
      have hxV : xbar ∈ V := by
        simpa [AffineSubspace.mem_mk'] using hxC
      have hu_orth : u ∈ (Vᗮ : Set H) := by
        have hneg_orth : -u ∈ (Vᗮ : Set H) := by
          simpa [AffineSubspace.direction_mk',
            normalCone_affineSubspace_eq_direction_orthogonal_of_mem
              (AffineSubspace.mk' (0 : H) V) hxC] using hneg
        simpa using Submodule.neg_mem (Vᗮ) hneg_orth
      exact ⟨hxV, ⟨u, hu, hu_orth⟩⟩
    · -- Outside the affine subspace, its normal cone is empty.
      rw [normalCone_affineSubspace_eq_empty_of_not_mem (AffineSubspace.mk' (0 : H) V) hxC] at hneg
      exact hneg.elim
  · rintro ⟨hxV, ⟨u, hu, hu_orth⟩⟩
    have hxC : xbar ∈ (AffineSubspace.mk' (0 : H) V : Set H) := by
      simpa [AffineSubspace.mem_mk'] using hxV
    have hneg_orth : -u ∈ (Vᗮ : Set H) := by
      simpa using Submodule.neg_mem (Vᗮ) hu_orth
    refine ⟨u, hu, ?_⟩
    -- Rewrite the affine normal cone back into the orthogonal complement of `V`.
    simpa [AffineSubspace.direction_mk',
      normalCone_affineSubspace_eq_direction_orthogonal_of_mem
        (AffineSubspace.mk' (0 : H) V) hxC] using hneg_orth

/-- Assuming `V` is closed and `0 ∈ sri (V - dom f)`, a point `xbar` minimizes `f` over `V` if
and only if it admits a dual certificate `u ∈ Vᗮ ∩ ∂ f(xbar)`, packaged here as a Chapter 26
partial-inverse solution for `∂ f`. -/
theorem mem_argmin_subspace_iff_exists_isSpingarnPartialInverseSolution_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (V : Submodule ℝ H)
    (hV_closed : IsClosed (V : Set H)) (hregular : SubspaceConstraintRegularity f V)
    {xbar : H} :
    xbar ∈ Argmin[V] f.asEReal ↔
      ∃ u : H, IsSpingarnPartialInverseSolution (∂ f) V xbar u := by
  let C0 : AffineSubspace ℝ H := AffineSubspace.mk' (0 : H) V
  have hC0_eq : (C0 : Set H) = (V : Set H) := by
    ext x
    simp [C0, AffineSubspace.mem_mk']
  have hC0_closed : IsClosed (C0 : Set H) := by
    simpa [hC0_eq] using hV_closed
  have hC0_convex : Convex ℝ (C0 : Set H) := by
    simpa [hC0_eq] using V.convex
  -- Route correction: avoid the heavier Proposition 27.16 import path and specialize
  -- Proposition 27.8 directly to the affine subspace `0 + V`.
  calc
    xbar ∈ Argmin[V] f.asEReal ↔ xbar ∈ Argmin[(C0 : Set H)] f.asEReal := by
      simp [hC0_eq]
    _ ↔ xbar ∈ ((N[(C0 : Set H)]) + (∂ f)).zeros := by
      exact
        mem_argminOn_iff_mem_zeros_normalCone_add_subdifferential_of_zero_mem_sri
          hf hC0_closed hC0_convex (by simpa [hC0_eq] using hregular)
    _ ↔ ∃ u : H, u ∈ (∂ f) xbar ∧ -u ∈ N[(C0 : Set H)] xbar := by
      exact mem_zeros_normalCone_add_subdifferential_iff_exists_mem_subdifferential_neg
    _ ↔ xbar ∈ V ∧ (((∂ f) xbar ∩ (Vᗮ : Set H)).Nonempty) := by
      simpa [C0] using
        (exists_mem_subdifferential_neg_normalCone_subspace_iff
          (f := f) (V := V) (xbar := xbar))
    _ ↔ ∃ u : H, IsSpingarnPartialInverseSolution (∂ f) V xbar u := by
      constructor
      · rintro ⟨hxV, ⟨u, hu, hu_orth⟩⟩
        exact ⟨u, hxV, hu_orth, hu⟩
      · rintro ⟨u, hxV, hu_orth, hu⟩
        exact ⟨hxV, ⟨u, hu, hu_orth⟩⟩

/-- Assuming `V` is closed and `0 ∈ sri (V - dom f)`, minimizing `f` over `V` is equivalent to
belonging to `V` and having a subgradient in `Vᗮ`. -/
theorem mem_argmin_subspace_iff_mem_and_subdifferential_inter_orthogonal_nonempty
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (V : Submodule ℝ H)
    (hV_closed : IsClosed (V : Set H)) (hregular : SubspaceConstraintRegularity f V)
    {xbar : H} :
    xbar ∈ Argmin[V] f.asEReal ↔
      xbar ∈ V ∧ (((∂ f) xbar ∩ Vᗮ).Nonempty) := by
  -- Repackage the Chapter 26 solution witness as a nonempty intersection with `Vᗮ`.
  rw [mem_argmin_subspace_iff_exists_isSpingarnPartialInverseSolution_subdifferential
    hf V hV_closed hregular]
  constructor
  · rintro ⟨u, hxbar, hu, hsub⟩
    exact ⟨hxbar, ⟨u, hsub, hu⟩⟩
  · rintro ⟨hxbar, u, hsub, hu⟩
    exact ⟨u, hxbar, hu, hsub⟩

/-- Assuming `V` is closed and `0 ∈ sri (V - dom f)`, the constrained argmin set is nonempty
exactly when the Chapter 26 partial-inverse problem for `∂ f` over `V` has a solution. -/
theorem argmin_subspace_nonempty_iff_exists_isSpingarnPartialInverseSolution_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (V : Submodule ℝ H)
    (hV_closed : IsClosed (V : Set H)) (hregular : SubspaceConstraintRegularity f V) :
    (Argmin[V] f.asEReal).Nonempty ↔
      ∃ x u, IsSpingarnPartialInverseSolution (∂ f) V x u := by
  constructor
  · rintro ⟨xbar, hxbar⟩
    -- Read a minimizer as the corresponding Chapter 26 primal-dual solution.
    rcases
        (mem_argmin_subspace_iff_exists_isSpingarnPartialInverseSolution_subdifferential
          hf V hV_closed hregular).1 hxbar with
      ⟨ubar, hubar⟩
    exact ⟨xbar, ubar, hubar⟩
  · rintro ⟨xbar, ubar, hubar⟩
    -- Conversely, a Chapter 26 solution certifies nonemptiness of the constrained argmin set.
    exact
      ⟨xbar,
        (mem_argmin_subspace_iff_exists_isSpingarnPartialInverseSolution_subdifferential
          hf V hV_closed hregular).2 ⟨ubar, hubar⟩⟩

/-- Proposition 28.2: let `f ∈ Γ₀(H)` and let `V` be a closed linear subspace, represented by
`[V.HasOrthogonalProjection]`. Assume `0 ∈ sri (V - dom f)` and that the constrained problem
`minimize f(x)` over `x ∈ V` has a solution. If `x`, `u`, `y`, and `v` satisfy the proximal
recursion `(28.9)` from initial data `x0 ∈ V` and `u0 ∈ Vᗮ`, then `(x n)` converges weakly to a
solution of that constrained problem. -/
theorem spingarnProximalSubspace_exists_weakLimit_mem_argmin
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (V : Submodule ℝ H)
    [V.HasOrthogonalProjection]
    (hregular : SubspaceConstraintRegularity f V)
    (hargmin : (Argmin[V] f.asEReal).Nonempty)
    {x0 u0 : H} {x u y v : ℕ → H}
    (hOrbit : IsSpingarnProximalSubspaceOrbit hf V x0 u0 x u y v) :
    ∃ xbar ∈ Argmin[V] f.asEReal,
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xbar)) := by
  have hV_closed : IsClosed (V : Set H) := by
    -- A subspace with an orthogonal projection is the fixed-point set of a continuous map.
    simpa [Submodule.starProjection_eq_self_iff] using
      (isClosed_eq V.starProjection.continuous continuous_id :
        IsClosed {x : H | V.starProjection x = x})
  -- Apply Theorem 26.9 to the subdifferential orbit obtained from the source recursion.
  obtain ⟨xbar, ubar, hxubar, hxbar, _⟩ :=
    exists_weakLimit_isSpingarnPartialInverseSolution_of_isSpingarnPartialInverseOrbit
      (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf) V
      ((argmin_subspace_nonempty_iff_exists_isSpingarnPartialInverseSolution_subdifferential
        hf V hV_closed hregular).1 hargmin)
      (hOrbit.toIsSpingarnPartialInverseOrbit)
  refine ⟨xbar, ?_, hxbar⟩
  -- Convert the limiting Chapter 26 solution back into a constrained minimizer of `f` on `V`.
  exact
    (mem_argmin_subspace_iff_exists_isSpingarnPartialInverseSolution_subdifferential
      hf V hV_closed hregular).2 ⟨ubar, hxubar⟩

end SpingarnPartialInverses

end ERealFunction
