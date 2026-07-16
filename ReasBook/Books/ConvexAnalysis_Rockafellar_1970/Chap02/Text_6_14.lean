import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_13
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_8
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

section

variable {𝕜 V P : Type*}
variable [Ring 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [TopologicalSpace P] [AddTorsor V P]

namespace Set

/-
Source/core/bridge triage:
- `source-facing`: Text 6.14 records that the closure of any subset of a finite-dimensional
  ambient space, in particular of `ℝ^n`, lies in its affine hull, via the chain
  `cl C ⊆ cl (aff C) = aff C`.
- `core/canonical`: the primitive owner condition for this closure statement is that the affine
  hull itself is closed; then the owner bridge is
  `closure C ⊆ affineSpan 𝕜 C`, obtained from `closure_minimal`.
- `bridge/view`: finite-dimensionality of the affine-hull direction is a sufficient source-facing
  hypothesis that supplies affine-hull closedness via
  `Submodule.closed_of_finiteDimensional` and
  `AffineSubspace.isClosed_direction_iff`.
- Primitive data vs derived API: `affineSpan 𝕜 C` is the owner object;
  `closure_subset_affineSpan` is the primitive closure bridge on that owner; the finite-direction
  formulations are derived API.
- Domain-style sampling used here: `closure_minimal`, `Set.aff_mono`,
  `Submodule.closed_of_finiteDimensional`, and `AffineSubspace.isClosed_direction_iff`.
- Layer target: this file promotes the primitive closed-affine-hull owner layer first, then
  exposes the finite-direction source-facing corollaries.
-/

/-- Primitive owner form behind Text 6.14: if the affine hull of `C` is closed, then the closure
of `C` is contained in that affine hull. -/
theorem closure_subset_affineSpan {C : Set P}
    (hclosed : IsClosed (aff[𝕜] C : Set P)) :
    closure C ⊆ (aff[𝕜] C : Set P) :=
  closure_minimal (subset_aff C) hclosed

/-- Primitive intrinsic companion: if `affineSpan 𝕜 C` is closed, intrinsic and ambient closures
coincide. -/
theorem intrinsicClosure_eq_closure_of_isClosed_affineSpan {C : Set P}
    (hclosed : IsClosed (aff[𝕜] C : Set P)) :
    cl[𝕜](C) = closure C := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  exact inter_eq_left.2 (closure_subset_affineSpan hclosed)

/-- Primitive affine-hull consequence: if `affineSpan 𝕜 C` is closed, then taking closure does not
change affine span. -/
theorem affineSpan_closure_of_isClosed_affineSpan {C : Set P}
    (hclosed : IsClosed (aff[𝕜] C : Set P)) :
    (aff[𝕜] (closure C)) = (aff[𝕜] C) := by
  refine le_antisymm ?_ (Set.aff_mono subset_closure)
  exact aff_min (closure_subset_affineSpan hclosed)

end Set

end

section

variable {𝕜 V P : Type*}
variable [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul 𝕜 V] [T1Space V]
variable [TopologicalSpace P] [AddTorsor V P] [IsTopologicalAddTorsor P]

namespace Set

/-- Finite-direction bridge to the primitive closed-affine-hull owner layer. -/
theorem isClosed_affineSpan {C : Set P}
    [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    IsClosed (aff[𝕜] C : Set P) := by
  simpa using
    (aff[𝕜] C).isClosed_of_finiteDimensional

/-- Text 6.14, source-facing finite-direction form: the closure of any set in a
finite-dimensional normed affine space, in particular in a finite-dimensional real normed space
and hence in `ℝ^n`, is contained in its affine span. Equivalently, `cl C ⊆ cl (aff C) = aff C`. -/
theorem closure_subset_affineSpan_of_finiteDimensional_direction
    {C : Set P} [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    closure C ⊆ (aff[𝕜] C : Set P) :=
  closure_subset_affineSpan
    (isClosed_affineSpan (C := C))

/-- On the finite-direction affine-hull owner layer, intrinsic and ambient closures coincide. -/
theorem intrinsicClosure_eq_closure_of_finiteDimensional_direction {C : Set P}
    [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    cl[𝕜](C) = closure C :=
  intrinsicClosure_eq_closure_of_isClosed_affineSpan
    (isClosed_affineSpan (C := C))

/-- The closure of a set has the same affine span once the affine hull has finite-dimensional
direction. -/
theorem affineSpan_closure {C : Set P} [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    (aff[𝕜] (closure C)) = (aff[𝕜] C) :=
  affineSpan_closure_of_isClosed_affineSpan
    (isClosed_affineSpan (C := C))

end Set

end
