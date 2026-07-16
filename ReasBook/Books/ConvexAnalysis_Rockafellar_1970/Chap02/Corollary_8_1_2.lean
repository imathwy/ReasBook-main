import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [HasPairing X Y 𝕜] {I : Sort*}

/-
Source/core/bridge triage:
- `source-facing`: Corollary 8.1.2 identifies the recession cone of the feasible region cut out by
  the inequalities `β i ≤ ⟪x, b i⟫ₚ`.
- `core/canonical`: the chapter owner abstractions are `0⁺`,
  `LinearConstraintRelation.geFeasible`, and
  `LinearConstraintRelation.homogeneousGeFeasibleSet`; this item is the `.ge` feasible-region
  specialization of the mixed owner layer.
- `bridge/view`: the textbook sets `⋂ i, closedHalfSpaceGE (b i) (β i)` and
  `⋂ i, closedHalfSpaceGE (b i) 0` are the `.ge` specializations of the owner feasible sets with
  right-hand sides `β` and `0`.
- Domain-style sampling: the relevant existing declarations in this domain are
  `HasPairing`, `IsLinearMap`, `LinearConstraintRelation.geFeasible`,
  `LinearConstraintRelation.mem_geFeasible`,
  `LinearConstraintRelation.mem_homogeneousGeFeasibleSet`,
  `closedHalfSpaceGE`, `0⁺`, `Set.mem_recessionCone_iff`,
  `mem_recessionCone_iff_add_singleton_subset_self`, and
  `LinearConstraintRelation.convex_feasibleSet`; the primitive owner layer for this corollary only
  needs the indexed linearity data `x ↦ ⟪x, b i⟫ₚ`, while the global
  `HasLinearPairing` owner stays as a derived bridge.
- Primitive data vs derived API: the primitive inputs are the normals `b` and thresholds `β`,
  together with linearity of each map `x ↦ ⟪x, b i⟫ₚ`; the recession-cone equality is derived API
  on the canonical feasible-region owner.
- Layer target: the main theorem is `core/canonical`, and the displayed half-space intersection is
  retained only as a thin `bridge/view` corollary.
-/

namespace LinearConstraintRelation

/-- Corollary 8.1.2, primitive owner form: if the feasible region of the `.ge` linear constraints
`β i ≤ ⟪x, b i⟫ₚ` is nonempty and each indexed pairing evaluation is linear in `x`, then its
recession cone `0⁺ C` is exactly the corresponding homogeneous `.ge` feasible region. -/
-- Proof sketch: choose `x ∈ C` from the nonemptiness hypothesis. For the forward inclusion,
-- apply the defining property of `recessionCone` to `x + a • y ∈ C`, compare the inequalities
-- with those for `x`, and divide by `a ≥ 0` to get `0 ≤ ⟪y, b i⟫ₚ`. For the reverse inclusion,
-- use the owner definition of `recessionCone`: a homogeneous feasible direction stays feasible
-- after nonnegative scaling, and then adding that scaled direction preserves every `.ge`
-- constraint.
theorem recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
    (b : I → Y) (β : I → 𝕜)
    (hlin : ∀ i, IsLinearMap 𝕜 (((fun x : X ↦ ⟪x, b i⟫ₚ) : X → 𝕜)))
    (hC : (geFeasible b β : Set X).Nonempty) :
    0⁺[𝕜] (geFeasible b β : Set X) = (homogeneousGeFeasibleSet 𝕜 b : Set X) := by
  let C : Set X := geFeasible b β
  let K : Set X := homogeneousGeFeasibleSet 𝕜 b
  have pairing_add (i : I) (x y : X) :
      (⟪x + y, b i⟫ₚ : 𝕜) = ⟪x, b i⟫ₚ + ⟪y, b i⟫ₚ :=
    (hlin i).map_add x y
  have pairing_smul (i : I) (a : 𝕜) (x : X) :
      (⟪a • x, b i⟫ₚ : 𝕜) = a * ⟪x, b i⟫ₚ := by
    simpa [smul_eq_mul] using (hlin i).map_smul a x
  obtain ⟨x, hx⟩ := hC
  have mem_C_iff (x : X) : x ∈ C ↔ ∀ i, β i ≤ ⟪x, b i⟫ₚ := by
    change x ∈ geFeasible b β ↔ ∀ i, β i ≤ ⟪x, b i⟫ₚ
    exact (mem_geFeasible (b := b) (β := β) (x := x))
  have mem_K_iff (y : X) : y ∈ K ↔ ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ := by
    change y ∈ homogeneousGeFeasibleSet 𝕜 b ↔ ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ
    exact (mem_homogeneousGeFeasibleSet (𝕜 := 𝕜) (b := b) (x := y))
  have hx : x ∈ C := by
    simpa [C] using hx
  have hx' : ∀ i, β i ≤ ⟪x, b i⟫ₚ := (mem_C_iff x).mp hx
  have mem_K_of_mem_recession {y : X} (hy : y ∈ 0⁺[𝕜] C) : y ∈ K := by
    rw [mem_K_iff]
    rw [Set.mem_recessionCone_iff] at hy
    intro i
    have hxi : β i ≤ ⟪x, b i⟫ₚ := hx' i
    by_contra hyi
    have hyi_lt : ⟪y, b i⟫ₚ < (0 : 𝕜) := lt_of_not_ge hyi
    let a : 𝕜 := (⟪x, b i⟫ₚ - β i + 1) / (-⟪y, b i⟫ₚ)
    have ha : 0 ≤ a := by
      have hnum : 0 ≤ ⟪x, b i⟫ₚ - β i + 1 := by
        linarith
      have hden : (0 : 𝕜) ≤ -⟪y, b i⟫ₚ := by
        linarith
      exact div_nonneg hnum hden
    have hxy : β i ≤ ⟪x, b i⟫ₚ + a * ⟪y, b i⟫ₚ := by
      have hxy : x + a • y ∈ C := hy x hx a ha
      have hxy' : β i ≤ ⟪x + a • y, b i⟫ₚ := (mem_C_iff (x + a • y)).mp hxy i
      simpa [pairing_add i x (a • y), pairing_smul i a y] using hxy'
    have ha_mul : a * ⟪y, b i⟫ₚ = -(⟪x, b i⟫ₚ - β i + 1) := by
      dsimp [a]
      have hyi_ne : (⟪y, b i⟫ₚ : 𝕜) ≠ 0 := by
        linarith
      have hqq : (⟪y, b i⟫ₚ : 𝕜) * (⟪y, b i⟫ₚ : 𝕜)⁻¹ = 1 := by
        field_simp [hyi_ne]
      calc
        ((⟪x, b i⟫ₚ - β i + 1) / (-⟪y, b i⟫ₚ)) * ⟪y, b i⟫ₚ
            = -((⟪x, b i⟫ₚ - β i + 1) * (⟪y, b i⟫ₚ * (⟪y, b i⟫ₚ)⁻¹)) := by
                ring_nf
        _ = -((⟪x, b i⟫ₚ - β i + 1) * 1) := by rw [hqq]
        _ = -(⟪x, b i⟫ₚ - β i + 1) := by ring
    linarith
  have smul_mem_K {a : 𝕜} {y : X} (hy : y ∈ K) (ha : 0 ≤ a) : a • y ∈ K := by
    rw [mem_K_iff] at hy ⊢
    intro i
    have hai : (0 : 𝕜) ≤ a * ⟪y, b i⟫ₚ := mul_nonneg ha (hy i)
    simpa [pairing_smul i a y] using hai
  have add_mem_C {y z : X} (hy : y ∈ C) (hz : z ∈ K) : y + z ∈ C := by
    rw [mem_C_iff] at hy ⊢
    intro i
    have hyi : β i ≤ ⟪y, b i⟫ₚ := hy i
    have hzi : (0 : 𝕜) ≤ ⟪z, b i⟫ₚ := (mem_K_iff z).mp hz i
    have hyz : β i ≤ ⟪y, b i⟫ₚ + ⟪z, b i⟫ₚ := by
      linarith
    simpa [pairing_add i y z] using hyz
  ext y
  constructor
  · intro hy
    change y ∈ 0⁺[𝕜] C at hy
    change y ∈ K
    exact mem_K_of_mem_recession hy
  · intro hy
    change y ∈ K at hy
    change y ∈ 0⁺[𝕜] C
    rw [Set.mem_recessionCone_iff]
    intro z hz a ha
    exact add_mem_C hz (smul_mem_K hy ha)

end LinearConstraintRelation

/-- Corollary 8.1.2 in the textbook pointwise form: if the feasible region
`{x | ∀ i, β i ≤ ⟪x, b i⟫ₚ}` is nonempty and each indexed pairing evaluation is linear in `x`,
then its recession cone is exactly the homogeneous feasible region
`{y | ∀ i, 0 ≤ ⟪y, b i⟫ₚ}`. -/
theorem recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg_of_forall_isLinear
    (b : I → Y) (β : I → 𝕜)
    (hlin : ∀ i, IsLinearMap 𝕜 (((fun x : X ↦ ⟪x, b i⟫ₚ) : X → 𝕜)))
    (hC : ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}).Nonempty) :
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
      {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
  have hβ :
      (LinearConstraintRelation.geFeasible b β : Set X) =
        {x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ} := by
    simpa using (LinearConstraintRelation.geFeasible_eq_setOf (b := b) (β := β))
  have h0 :
      (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) =
        {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
    simpa using
      (LinearConstraintRelation.homogeneousGeFeasibleSet_eq_setOf
        (𝕜 := 𝕜) (b := b))
  have hC' :
      (LinearConstraintRelation.geFeasible b β : Set X).Nonempty := by
    rw [hβ]
    exact hC
  have hrec :
      0⁺[𝕜] (LinearConstraintRelation.geFeasible b β : Set X) =
        (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) :=
    LinearConstraintRelation.recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
      (X := X) (b := b) (β := β) hlin hC'
  calc
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
        0⁺[𝕜] (LinearConstraintRelation.geFeasible b β : Set X) := by
      rw [← hβ]
    _ = (LinearConstraintRelation.homogeneousGeFeasibleSet 𝕜 b : Set X) := hrec
    _ = {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := h0

end

section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] {I : Sort*}

namespace LinearConstraintRelation

/-- Corollary 8.1.2, bridge owner form under a linear pairing owner. -/
theorem recessionCone_geFeasible_eq_homogeneousGeFeasibleSet
    (b : I → Y) (β : I → 𝕜)
    (hC : (geFeasible b β : Set X).Nonempty) :
    0⁺[𝕜] (geFeasible b β : Set X) = (homogeneousGeFeasibleSet 𝕜 b : Set X) := by
  exact recessionCone_geFeasible_eq_homogeneousGeFeasibleSet_of_forall_isLinear
    (X := X) (b := b) (β := β)
    (hlin := fun i ↦ HasLinearPairing.isLinear_pairing_left (b i)) hC

end LinearConstraintRelation

/-- Corollary 8.1.2 in the textbook pointwise form under a linear pairing owner. -/
theorem recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg
    (b : I → Y) (β : I → 𝕜)
    (hC : ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}).Nonempty) :
    0⁺[𝕜] ({x : X | ∀ i, β i ≤ ⟪x, b i⟫ₚ}) =
      {y : X | ∀ i, (0 : 𝕜) ≤ ⟪y, b i⟫ₚ} := by
  exact recessionCone_setOf_forall_ge_eq_setOf_forall_nonneg_of_forall_isLinear
    (X := X) (b := b) (β := β)
    (hlin := fun i ↦ HasLinearPairing.isLinear_pairing_left (b i)) hC

end
