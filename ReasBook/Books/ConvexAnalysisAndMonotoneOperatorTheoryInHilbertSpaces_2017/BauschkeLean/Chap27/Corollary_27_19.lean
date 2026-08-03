import BauschkeLean.Chap27.Proposition_27_17

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u

namespace ERealFunction

/- Source/core/bridge triage:
- `source-facing`: Corollary 27.19 is the cone-constrained minimization criterion for the special
  case `L = id`.
- `core/canonical`: the Chapter 27 owner abstraction is `PolarSubgradientWitness`, together with
  `mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient`.
- `bridge/view`: this file only specializes that owner to the identity map and rewrites the
  witness with the textbook dual-cone variable `u ∈ Kᵒ⊕`.

The local duplicate certificate wrapper therefore disappears in favor of the existing owner
theorem plus a thin source-facing bridge. -/

section ConeConstraints

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- For the identity constraint map, the Proposition 27.17 witness for `-u` is exactly the
textbook dual-cone multiplier system `u ∈ Kᵒ⊕ ∩ ∂ f xbar` with complementary slackness. -/
theorem polarSubgradientWitness_id_neg_iff
    {f : H → Set.Ioi (⊥ : EReal)} {K : Set H} {xbar u : H} :
    PolarSubgradientWitness f K (ContinuousLinearMap.id ℝ H) xbar (-u) ↔
      u ∈ Kᵒ⊕ ∧ u ∈ (∂ f) xbar ∧ ⟪xbar, u⟫_ℝ = 0 := by
  constructor
  · intro hu
    refine ⟨(mem_dualCone_iff).2 hu.mem_polarCone, ?_, ?_⟩
    · simpa using hu.mem_subdifferential
    · simpa using hu.complementary_slackness
  · rintro ⟨hu_dual, hu_sub, hu_inner⟩
    refine ⟨(mem_dualCone_iff).1 hu_dual, ?_, ?_⟩
    · simpa using hu_sub
    · simpa using hu_inner

/-- Corollary 27.19: let `K` be a closed convex cone in `H`, let `f ∈ Γ₀(H)`, and let
`xbar ∈ H`. If one of the three source regularity alternatives holds, then `xbar` solves
`minimize f(x)` over `x ∈ K` if and only if `xbar ∈ K` and there exists
`u ∈ K^⊕ ∩ ∂f(xbar)` with `⟪xbar, u⟫ = 0`. -/
theorem mem_argminOn_cone_iff_exists_dual_cone_subgradient
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {K : Set H} (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hcond : ConeConstraintRegularity f K (ContinuousLinearMap.id ℝ H))
    {xbar : H} :
    xbar ∈ Argmin[K] f.asEReal ↔
      xbar ∈ K ∧
        ∃ u : H, u ∈ Kᵒ⊕ ∧ u ∈ (∂ f) xbar ∧ ⟪xbar, u⟫_ℝ = 0 := by
  have hK_nonempty : K.Nonempty := by
    cases hcond with
    | closed_subspace V hEq hClosed =>
        have hzero :
            (0 : H) ∈ K - cone (ContinuousLinearMap.id ℝ H '' effectiveDomain f) := by
          rw [hEq]
          simp
        rcases Set.mem_sub.mp hzero with ⟨x, hxK, _, _, _⟩
        exact ⟨x, hxK⟩
    | finite_dimensional_polyhedral_ri hfin hpolyK hri =>
        rcases hri with ⟨x, hxK, _⟩
        exact ⟨x, hxK⟩
    | finite_dimensional_polyhedral_function hfinH hfinG hpolyf hpolyK hfeas =>
        rcases hfeas with ⟨x, hxK, _⟩
        exact ⟨x, hxK⟩
  have hbot : ∀ x ∉ K, f.asEReal x ≠ ⊥ := by
    intro x hxK
    exact ne_of_gt (f x).2
  have hargminOn :
      Argmin[K] f.asEReal =
        K ∩ Argmin (compositePrimalObjective f (ι[K]) (ContinuousLinearMap.id ℝ H)) := by
    simpa [compositePrimalObjective, primalObjective] using
      argminOn_eq_inter_argmin_add_indicator f.asEReal K hbot
  have howner :
      xbar ∈ Argmin (compositePrimalObjective f (ι[K]) (ContinuousLinearMap.id ℝ H)) ↔
        xbar ∈ K ∧
          ∃ vbar : H,
            PolarSubgradientWitness f K (ContinuousLinearMap.id ℝ H) xbar vbar :=
    mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient
      hf hK_nonempty hK_closed hK_convex hK_cone hcond
  rw [hargminOn, Set.mem_inter_iff]
  constructor
  · rintro ⟨_, hxobj⟩
    rcases howner.mp hxobj with ⟨hxK, vbar, hvbar⟩
    refine ⟨hxK, -vbar, ?_⟩
    have hbridge :
        PolarSubgradientWitness f K (ContinuousLinearMap.id ℝ H) xbar (-(-vbar)) ↔
          -vbar ∈ Kᵒ⊕ ∧ -vbar ∈ (∂ f) xbar ∧ ⟪xbar, -vbar⟫_ℝ = 0 :=
      polarSubgradientWitness_id_neg_iff
    simpa using hbridge.1 (by simpa using hvbar)
  · rintro ⟨hxK, u, hu_dual, hu_sub, hu_inner⟩
    have hbridge :
        PolarSubgradientWitness f K (ContinuousLinearMap.id ℝ H) xbar (-u) ↔
          u ∈ Kᵒ⊕ ∧ u ∈ (∂ f) xbar ∧ ⟪xbar, u⟫_ℝ = 0 :=
      polarSubgradientWitness_id_neg_iff
    have hu :
        PolarSubgradientWitness f K (ContinuousLinearMap.id ℝ H) xbar (-u) :=
      hbridge.2 ⟨hu_dual, hu_sub, hu_inner⟩
    refine ⟨hxK, howner.mpr ?_⟩
    exact ⟨hxK, -u, hu⟩

end ConeConstraints

end ERealFunction
