import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic.Recall
import SmoothManifolds_Lee_2012.Chap07.Sec07_50.Definition_7_50_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- The declarations below use the canonical smooth-action and orbit owners directly:
-- `ContMDiffSMul`, `orbit_map`, `range_orbit_map`, `MulAction.orbit.eq_or_disjoint`, and
-- `MulAction.univ_eq_iUnion_orbit`.

open scoped ContDiff Manifold
open Metric (sphere)
open Set

/-- Helper for Problem 7-11: the real dimension of `ℂ^(n+1)` is `(2n+1)+1`. -/
theorem hopf_complex_finrank_fact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = (2 * n + 1) + 1) := by
  -- Rewrite the ambient complex vector space dimension over `ℝ` through its complex dimension.
  refine Fact.mk ?_
  calc
    Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) =
        2 * Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) := by
          simpa using finrank_real_of_complex (EuclideanSpace ℂ (Fin (n + 1)))
    _ = 2 * (n + 1) := by
          rw [finrank_euclideanSpace_fin]
    _ = (2 * n + 1) + 1 := by
          omega

/-- Helper for Problem 7-11: `ℂ` has real dimension `1 + 1`, matching the circle model. -/
theorem hopf_circle_finrank_fact : Fact (Module.finrank ℝ ℂ = 1 + 1) := by
  -- Normalize the standard `2`-dimensional fact to the `1 + 1` form used by the sphere API.
  simpa using (Complex.finrank_real_complex_fact : Fact (Module.finrank ℝ ℂ = 2))

attribute [local instance] hopf_circle_finrank_fact
attribute [local instance] hopf_complex_finrank_fact

section HopfAction

variable (n : ℕ)

local notation "HopfSphere" => sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1

local instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Submonoid.unitSphere ℂ) :=
  inferInstanceAs <| ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle
local instance : IsManifold (𝓡 1) ω (Submonoid.unitSphere ℂ) :=
  inferInstanceAs <| IsManifold (𝓡 1) ω Circle

local instance : SMul Circle HopfSphere :=
  inferInstanceAs <| SMul (sphere (0 : ℂ) 1) HopfSphere

local instance : MulAction Circle HopfSphere :=
  inferInstanceAs <| MulAction (sphere (0 : ℂ) 1) HopfSphere

/-- Helper for Problem 7-11: the Hopf action is coordinatewise complex scalar multiplication. -/
theorem hopf_action_map_coe_apply (z : Circle) (w : HopfSphere) (i : Fin (n + 1)) :
    ((z • w : HopfSphere) : EuclideanSpace ℂ (Fin (n + 1))) i =
      (z : ℂ) * (w : EuclideanSpace ℂ (Fin (n + 1))) i := by
  -- The sphere action is defined by the ambient scalar action, so the coordinate formula is
  -- just the ambient scalar-multiplication formula.
  rfl

/-- Helper for Problem 7-11: the ambient map `(z, w) ↦ z • w` on `Circle × HopfSphere` is smooth
as a map to `ℂ^(n+1)`. -/
lemma hopfActionAmbient_contMDiff :
    ContMDiff
      ((𝓡 1).prod (𝓡 (2 * n + 1)))
      𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
      ∞
      (fun p : Circle × HopfSphere ↦ (p.1 : ℂ) • (p.2 : EuclideanSpace ℂ (Fin (n + 1)))) := by
  let c : Circle → ℂ := (↑)
  let s : HopfSphere → EuclideanSpace ℂ (Fin (n + 1)) := (↑)
  -- First pass to the ambient product `ℂ × ℂ^(n+1)` using the two sphere inclusions.
  have hIncl :
      ContMDiff
        ((𝓡 1).prod (𝓡 (2 * n + 1)))
        (𝓘(ℝ, ℂ).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))))
        ∞
        (Prod.map c s) := by
    apply ContMDiff.prodMap
    · simpa [c] using (contMDiff_coe_sphere (m := ∞) (n := 1) (E := ℂ))
    · simpa [s] using
        (contMDiff_coe_sphere (m := ∞) (n := 2 * n + 1)
          (E := EuclideanSpace ℂ (Fin (n + 1))))
  -- Then compose with the ambient smooth scalar-multiplication map.
  have hSmul :
      ContMDiff
        (𝓘(ℝ, ℂ).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))))
        𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))
        ∞
        (fun p : ℂ × EuclideanSpace ℂ (Fin (n + 1)) ↦ p.1 • p.2) := by
    -- Rewrite the source model to the product manifold model expected for `Circle × HopfSphere`.
    have hProd :
        ContMDiff
          (𝓘(ℝ, ℂ).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))))
          𝓘(ℝ, ℂ × EuclideanSpace ℂ (Fin (n + 1)))
          ∞
          (@id (ℂ × EuclideanSpace ℂ (Fin (n + 1)))) := by
      rw [contMDiff_prod_module_iff, ← contMDiff_prod_iff]
      exact contMDiff_id
    exact contDiff_smul.contMDiff.comp hProd
  simpa [c, s] using hSmul.comp hIncl

/-- Helper for Problem 7-11: the ambient Hopf action preserves the unit sphere. -/
lemma hopfActionAmbient_memSphere (p : Circle × HopfSphere) :
    ((p.1 : ℂ) • (p.2 : EuclideanSpace ℂ (Fin (n + 1)))) ∈
      sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1 := by
  -- Both factors have norm `1`, so scalar multiplication preserves the unit norm.
  rw [mem_sphere_zero_iff_norm]
  have hz : ‖(p.1 : ℂ)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp p.1.2
  have hw : ‖(p.2 : EuclideanSpace ℂ (Fin (n + 1)))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp p.2.2
  rw [norm_smul, hz, hw, one_mul]

/-- Problem 7-11 (1): the canonical `Circle`-action on the Hopf sphere `𝕊^(2n+1)` is smooth. -/
theorem hopf_action_smooth :
    ContMDiffSMul (𝓡 1) (𝓡 (2 * n + 1)) ∞ Circle HopfSphere := by
  refine ⟨?_⟩
  let f : Circle × HopfSphere → EuclideanSpace ℂ (Fin (n + 1)) :=
    fun p ↦ (p.1 : ℂ) • (p.2 : EuclideanSpace ℂ (Fin (n + 1)))
  -- Route correction: prove smoothness in the ambient vector space, then codRestrict back to the
  -- sphere once the norm-one side condition is isolated.
  have hcod :
      (Set.codRestrict f (sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
        (hopfActionAmbient_memSphere (n := n)) : Circle × HopfSphere → HopfSphere) =
        fun p : Circle × HopfSphere ↦ p.1 • p.2 := by
    -- Both maps have the same ambient value; only the sphere-membership proof differs.
    funext p
    apply Subtype.ext
    rfl
  rw [← hcod]
  -- The codRestriction is smooth because the ambient map is smooth and stays in the sphere.
  exact ContMDiff.codRestrict_sphere (n := 2 * n + 1) (f := f)
    (hopfActionAmbient_contMDiff (n := n))
    (hopfActionAmbient_memSphere (n := n))

/- Problem 7-11 (2): specialized to the Hopf action, this is exactly `range_orbit_map`. -/
recall range_orbit_map

/-- Problem 7-11 (3): the Hopf `Circle`-action on `𝕊^(2n+1)` is free. -/
theorem hopf_action_isFree :
    IsCancelSMul Circle HopfSphere := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro z w hzw
  apply Subtype.ext
  have hw_ne : (w : EuclideanSpace ℂ (Fin (n + 1))) ≠ 0 := by
    intro hw0
    have hw_norm : ‖(w : EuclideanSpace ℂ (Fin (n + 1)))‖ = (1 : ℝ) :=
      mem_sphere_zero_iff_norm.mp w.2
    simp [hw0] at hw_norm
  have hzw' : (z : ℂ) • (w : EuclideanSpace ℂ (Fin (n + 1))) =
      (w : EuclideanSpace ℂ (Fin (n + 1))) :=
    congrArg (fun v : HopfSphere ↦ (v : EuclideanSpace ℂ (Fin (n + 1)))) hzw
  have hz_sub : ((z : ℂ) - 1) • (w : EuclideanSpace ℂ (Fin (n + 1))) = 0 := by
    rw [sub_smul, one_smul, hzw', sub_self]
  rcases smul_eq_zero.mp hz_sub with hz | hw0
  · simpa using sub_eq_zero.mp hz
  · exact (hw_ne hw0).elim

/-- For each `w ∈ 𝕊^(2n+1)`, the Hopf orbit map is injective, hence each orbit is a copy of the
unit circle in `ℂ^(n+1)`. -/
theorem hopf_action_orbit_map_injective (w : HopfSphere) :
    Function.Injective (orbit_map Circle w) := by
  letI : IsCancelSMul Circle HopfSphere := hopf_action_isFree n
  intro z₁ z₂ hz
  exact IsCancelSMul.right_cancel z₁ z₂ w hz

/- Problem 7-11 (4): any two Hopf orbits are either equal or disjoint; this is
`MulAction.orbit.eq_or_disjoint`. -/
recall MulAction.orbit.eq_or_disjoint

/- Problem 7-11 (5): the Hopf orbits cover the whole sphere `𝕊^(2n+1)`; this is
`MulAction.univ_eq_iUnion_orbit`. -/
recall MulAction.univ_eq_iUnion_orbit

end HopfAction
