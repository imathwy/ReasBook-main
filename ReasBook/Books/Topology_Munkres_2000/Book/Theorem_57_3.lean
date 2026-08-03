module

public import Topology_Munkres_2000.Book.Definition_57_2.Antipodal

import Topology_Munkres_2000.Book.Theorem_57_2
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv

noncomputable section

public section

/-- Helper for Theorem 57.3: radial normalization of a continuous nonvanishing
map is continuous. -/
private theorem continuousRadialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) :
    Continuous (fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1) := by
  -- Lift `F` to the punctured space before applying radial coordinates.
  exact continuous_fst.comp ((homeomorphUnitSphereProd E).continuous.comp
    (Continuous.subtype_mk F.continuous hF))

/-- Helper for Theorem 57.3: the radial direction of a continuous nonvanishing
map, valued in the unit sphere. -/
private def radialDirection {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) : C(X, Metric.sphere (0 : E) 1) :=
  ⟨fun x ↦ ((homeomorphUnitSphereProd E) ⟨F x, hF x⟩).1,
    continuousRadialDirection F hF⟩

/-- Helper for Theorem 57.3: radial direction has the expected normalized
ambient vector. -/
private theorem radialDirection_coe {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) (x : X) :
    (radialDirection F hF x : E) = ‖F x‖⁻¹ • F x := by
  -- Expose only the first-coordinate formula of the radial homeomorphism.
  exact homeomorphUnitSphereProd_apply_fst_coe E ⟨F x, hF x⟩

/-- Helper for Theorem 57.3: radial normalization preserves oddness. -/
private theorem radialDirectionOdd {X E : Type*} [TopologicalSpace X] [Neg X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : C(X, E))
    (hF : ∀ x, F x ∈ ({0}ᶜ : Set E)) (hF_odd : Function.Odd F) :
    Function.Odd (radialDirection F hF) := by
  -- Compare the two sphere points through their normalized ambient vectors.
  intro x
  have normalized_neg :
      ‖F (-x)‖⁻¹ • F (-x) = -(‖F x‖⁻¹ • F x) := by
    rw [hF_odd x, norm_neg, smul_neg]
  apply Subtype.ext
  calc
    (radialDirection F hF (-x) : E) = ‖F (-x)‖⁻¹ • F (-x) :=
      radialDirection_coe F hF (-x)
    _ = -(‖F x‖⁻¹ • F x) := normalized_neg
    _ = -(radialDirection F hF x : E) :=
      congrArg Neg.neg (radialDirection_coe F hF x).symm
    _ = ((-(radialDirection F hF x) : Metric.sphere (0 : E) 1) : E) := rfl

/-- Helper for Theorem 57.3: separating every antipodal pair produces an odd
map from `S^(n+1)` to `S^n`. -/
private theorem existsOddSphereMap_of_antipodal_ne (n : ℕ)
    (f : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))))
    (hf : ∀ x, f x ≠ f (-x)) :
    ∃ g : C(StandardSphere (n + 1), StandardSphere n), Function.Odd g := by
  -- The source proof's controlled object is the antipodal difference.
  have difference_continuous : Continuous (fun x ↦ f x - f (-x)) := by
    fun_prop
  let difference : C(StandardSphere (n + 1), EuclideanSpace ℝ (Fin (n + 1))) :=
    ⟨fun x ↦ f x - f (-x), difference_continuous⟩
  have difference_ne : ∀ x, difference x ∈
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n + 1)))) := by
    intro x
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr (hf x)
  have difference_odd : Function.Odd difference := by
    intro x
    simp only [difference, ContinuousMap.coe_mk]
    rw [neg_neg, neg_sub]
  -- Radial normalization turns this nonzero odd vector into a sphere-valued map.
  have normalized_difference_odd :
      Function.Odd (radialDirection difference difference_ne) :=
    radialDirectionOdd difference difference_ne difference_odd
  exact ⟨radialDirection difference difference_ne, normalized_difference_odd⟩

/-- Theorem 57.3 (Borsuk–Ulam for `S²`). Every continuous map from `S²` to `ℝ²`
identifies an antipodal pair. -/
theorem existsAntipodalEqSphereTwo
    (f : C(StandardSphere 2, EuclideanSpace ℝ (Fin 2))) :
    ∃ x, f x = f (-x) := by
  -- Otherwise the normalized antipodal difference is the forbidden odd map `S² → S¹`.
  by_contra hf
  push Not at hf
  exact notExistsOddMapSphereTwoToOne
    (existsOddSphereMap_of_antipodal_ne 1 f hf)
