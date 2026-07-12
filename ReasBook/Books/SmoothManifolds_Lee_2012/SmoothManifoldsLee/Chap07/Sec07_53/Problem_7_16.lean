import SmoothManifolds_Lee_2012.Chap07.Sec07_53.Problem_7_23
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

-- Domain sampling: the primary domain here is Lie groups modeled on standard spheres.
-- The owner declarations checked before refinement were the sphere manifold owners
-- `ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1)` and
-- `IsManifold (𝓡 n) ω (sphere (0 : E) 1)` from `Instances/Sphere`, the smooth inclusion
-- `contMDiff_coe_sphere`, the circle Lie-group instance `LieGroup (𝓡 1) ω Circle`, and the
-- chapter owner `LieGroupIsomorphism`. The canonical source-facing owner for the `S^3` model is
-- the quaternion unit sphere `sphere (0 : ℍ) 1`; the `SU(2)` presentation is a bridge view
-- connected to that owner by a group equivalence.

open scoped ContDiff Manifold Quaternion
open Metric (sphere)

local notation "QuaternionSphere" => sphere (0 : ℍ) 1

theorem finrank_real_quaternion_fact : Fact (Module.finrank ℝ ℍ = 3 + 1) := by
  exact ⟨by simpa using (Quaternion.finrank_eq_four : Module.finrank ℝ ℍ = 4)⟩

attribute [local instance] finrank_real_quaternion_fact

instance : StarModule ℝ ℍ where
  star_smul r q := by
    ext <;> simp [smul_eq_mul]

instance : LieGroup (𝓡 3) ω QuaternionSphere where
  contMDiff_mul := by
    have hmul :
        ContMDiff (𝓘(ℝ, ℍ).prod 𝓘(ℝ, ℍ)) 𝓘(ℝ, ℍ) ω fun z : ℍ × ℍ ↦ z.1 * z.2 := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y ↦ contDiff_mul.contDiffOn⟩
    have hprod :
        ContMDiff ((𝓡 3).prod (𝓡 3)) (𝓘(ℝ, ℍ).prod 𝓘(ℝ, ℍ)) ω
          (Prod.map ((↑) : QuaternionSphere → ℍ) ((↑) : QuaternionSphere → ℍ)) := by
      apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
    have hambient :
        ContMDiff ((𝓡 3).prod (𝓡 3)) 𝓘(ℝ, ℍ) ω
          (fun p : QuaternionSphere × QuaternionSphere ↦ (p.1 : ℍ) * (p.2 : ℍ)) := by
      simpa [Function.comp] using hmul.comp hprod
    have hsphere :
        ∀ p : QuaternionSphere × QuaternionSphere,
          (fun q : QuaternionSphere × QuaternionSphere ↦ (q.1 : ℍ) * (q.2 : ℍ)) p ∈
            sphere (0 : ℍ) 1 := by
      intro p
      have hp₁ : ‖(p.1 : ℍ)‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using p.1.property
      have hp₂ : ‖(p.2 : ℍ)‖ = 1 := by
        simpa [mem_sphere_zero_iff_norm] using p.2.property
      rw [mem_sphere_zero_iff_norm, norm_mul, hp₁, hp₂, one_mul]
    simpa using ContMDiff.codRestrict_sphere hambient hsphere
  contMDiff_inv := by
    have hstar : ContMDiff 𝓘(ℝ, ℍ) 𝓘(ℝ, ℍ) ω (fun x : ℍ ↦ star x) := by
      simpa using (starL ℝ : ℍ ≃L[ℝ] ℍ).contDiff.contMDiff
    have hinv (x : QuaternionSphere) : ((x : ℍ)⁻¹) = star (x : ℍ) := by
      calc
        ((x : ℍ)⁻¹) = (Quaternion.normSq (x : ℍ))⁻¹ • star (x : ℍ) := by rfl
        _ = star (x : ℍ) := by
          simp [Quaternion.normSq_eq_norm_mul_self]
    have hEq : (fun x : QuaternionSphere ↦ ((x : ℍ)⁻¹)) =
        (fun x : QuaternionSphere ↦ star (x : ℍ)) :=
      funext hinv
    have hstarSphere :
        ContMDiff (𝓡 3) 𝓘(ℝ, ℍ) ω (fun x : QuaternionSphere ↦ star (x : ℍ)) := by
      simpa [Function.comp] using hstar.comp contMDiff_coe_sphere
    have hambient :
        ContMDiff (𝓡 3) 𝓘(ℝ, ℍ) ω (fun x : QuaternionSphere ↦ ((x : ℍ)⁻¹)) := by
      rw [hEq]
      exact hstarSphere
    have hsphere : ∀ x : QuaternionSphere, (fun y : QuaternionSphere ↦ ((y : ℍ)⁻¹)) x ∈
        sphere (0 : ℍ) 1 := by
      intro x
      simp [Metric.unitSphere.coe_inv] using (x⁻¹).property
    simpa using ContMDiff.codRestrict_sphere hambient hsphere

/- Problem 7-16: the canonical `SU(2)` comparison from Problem 7-23 already lives on the
quaternion unit sphere, so the `SU(2) ≅ S^3` statement is the direct symmetric form below. -/
#check quaternionSphereContinuousMulEquivSpecialUnitary.symm
