import Mathlib.Analysis.InnerProductSpace.Orthogonal
import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing
import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Z : Type*} [AddCommMonoid Z] [Module 𝕜 Z]
variable {I : Sort u}

/-
Source/core/bridge triage:
- `core/canonical`: the primitive owner layer for homogeneous equations is a family of linear
  maps `f : I → X →ₗ[𝕜] Z`; the common zero set is the intersection of kernels
  `⋂ i, LinearMap.ker (f i)` and should be exposed as a convex-cone theorem at this layer.
- `bridge/view`: the pairing form `⟪x, b i⟫ₚ = 0` is a specialization through
  `f i = HasLinearPairing.pairingLinear.flip (b i)`.
- `source-facing`: the labeled corollary remains the textbook pairing statement, now factored as
  a thin bridge over the linear-map owner theorem.
- Primitive data vs derived API: primitive data for the canonical owner theorem are
  `f : I → X →ₗ[𝕜] Z`; primitive data for the source-facing corollary are `b : I → Y` and a
  pairing instance. Convex-cone closure is derived API in both views.
- Layer target: `core/canonical` first, with pairing and inner-product statements as bridge views.
-/

namespace LinearMap

/-- The kernel of a linear map is a convex cone. -/
theorem ker_isConvexCone (f : X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 (LinearMap.ker f : Set X) := by
  refine ⟨?_, (LinearMap.ker f).convex⟩
  refine (Set.isCone_iff_forall_pos_smul_subset (𝕜 := 𝕜)
    (K := (LinearMap.ker f : Set X))).2 ?_
  intro c _hc x hx
  rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
  exact (LinearMap.ker f).smul_mem c hy

/-- Core owner theorem for Corollary 2.5.5: the common kernel of any family of linear maps is a
convex cone. -/
theorem iInter_ker_isConvexCone (f : I → X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 (⋂ i, (LinearMap.ker (f i) : Set X)) := by
  exact Set.IsConvexCone.iInter (fun i ↦ ker_isConvexCone (f i))

/-- Set-builder bridge for the linear-map owner theorem: a homogeneous system
`f i x = 0` defines a convex cone. -/
theorem setOf_forall_eq_zero_isConvexCone (f : I → X →ₗ[𝕜] Z) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, f i x = 0} := by
  have hset : {x : X | ∀ i, f i x = 0} = ⋂ i, (LinearMap.ker (f i) : Set X) := by
    ext x
    simp [LinearMap.mem_ker]
  simpa [hset] using iInter_ker_isConvexCone (f := f)

end LinearMap

end

section

variable {𝕜 : Type v} [CommSemiring 𝕜] [PartialOrder 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort u}

namespace LinearConstraintRelation

/-- Corollary 2.5.5 at the canonical homogeneous-constraint owner layer: for equality constraints,
the homogeneous feasible set is a convex cone. -/
theorem homogeneousEqFeasibleSet_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜
      (homogeneousEqFeasibleSet 𝕜 b : Set X) := by
  rw [homogeneousEqFeasibleSet_eq_setOf (b := b)]
  simpa [HasLinearPairing.pairing_eq_pairingLinear] using
    (LinearMap.setOf_forall_eq_zero_isConvexCone
      (f := fun i : I ↦ HasLinearPairing.pairingLinear.flip (b i)))

end LinearConstraintRelation

/-- Corollary 2.5.5, stated at the pairing layer: for any family of vectors `b i`, the common
zero set of the homogeneous linear equations `⟪x, b i⟫ₚ = 0` is a convex cone, formalized in the
chapter's short source-facing form `Set.IsConvexCone 𝕜 _`. -/
theorem setOf_forall_pairing_eq_zero_isConvexCone (b : I → Y) :
    Set.IsConvexCone 𝕜 {x : X | ∀ i, ⟪x, b i⟫ₚ = (0 : 𝕜)} := by
  simpa [LinearConstraintRelation.homogeneousEqFeasibleSet_eq_setOf (b := b)] using
    (LinearConstraintRelation.homogeneousEqFeasibleSet_isConvexCone (b := b))

end

section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {I : Sort u}

/-- Inner-product bridge for Corollary 2.5.5: in an inner-product space, the common zero set of
the equations `inner 𝕜 x (b i) = 0` is exactly the orthogonal complement of the span of the family
`b`. -/
theorem setOf_forall_inner_eq_zero_eq_orthogonal (b : I → E) :
    {x : E | ∀ i, inner 𝕜 x (b i) = 0} = (Submodule.span 𝕜 (Set.range b))ᗮ := by
  let K : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range b)
  ext x
  change (∀ i, inner 𝕜 x (b i) = 0) ↔ x ∈ Kᗮ
  rw [Submodule.mem_orthogonal']
  constructor
  · intro hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        rcases hy with ⟨i, rfl⟩
        exact hx i
    | zero =>
        simp
    | add y z _ _ hy hz =>
        simp [inner_add_right, hy, hz]
    | smul a y _ hy =>
        simp [inner_smul_right, hy]
  · intro hx i
    exact hx _ (Submodule.subset_span ⟨i, rfl⟩)

end
