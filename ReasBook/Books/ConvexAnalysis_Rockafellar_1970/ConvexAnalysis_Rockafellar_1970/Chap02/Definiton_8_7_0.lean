import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_5_0

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Pointwise

variable {X α : Type*} [Neg X] [LE α] [Zero α]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.7.0 introduces the constancy space of a proper convex function by
  an explicit condition on its recession function `f0⁺`.
- `core/canonical`: the primitive owner declaration already present in Chapter 8 is
  `Function.recessionCone`, the nonpositive sublevel set of a recession function. In this file,
  with no primitive cone-law hypotheses, the canonical owner is the symmetric set-level
  intersection `f₀.recessionCone ∩ -(f₀.recessionCone)`; the source-facing
  textbook order `-(f₀.recessionCone) ∩ f₀.recessionCone` is kept as a direct
  compatibility theorem.
- `bridge/view`: `Function.mem_constancySpace_iff` rewrites membership in the source-facing owner
  back into the symmetric pair of inequalities from the textbook, using the existing owner-side
  bridge `Function.mem_recessionCone_iff`.
- Primitive data vs derived API: once the recession function is fixed, the primitive object is the
  owner set `f₀.recessionCone`; the textbook inequalities are derived API obtained by
  combining that owner with pointwise negation. Because the owner from Definition 8.5.0 lives on
  the canonical extended codomain layer `WithTopBot α`, this file stays on that same layer.

Domain-style sampling used here:
- `Function.recessionCone` and `Function.mem_recessionCone_iff` from Definition 8.5.0;
- the preorder bridge `Function.recessionCone_eq_preimage_Iic` from Definition 8.5.0;
- the canonical pointwise negation `-s` of a subset and its membership rewrite `Set.mem_neg`;
- the standard preimage-sublevel owner surface `f ⁻¹' Set.Iic 0`.
-/

namespace Function

/-- Definition 8.7.0: the constancy space attached to a function `f₀` is the set of vectors `y`
such that both `f₀ y` and `f₀ (-y)` are at most `0`. -/
def constancySpace (f₀ : X → WithTopBot α) : Set X :=
  f₀.recessionCone ∩ -(f₀.recessionCone)

/-- The constancy space is definitionally the intersection of the positive and negative recession
cones. -/
theorem constancySpace_eq_recessionCone_inter_neg_recessionCone (f₀ : X → WithTopBot α) :
    f₀.constancySpace = f₀.recessionCone ∩ -(f₀.recessionCone) :=
  rfl

/-- Canonicalization bridge: the raw owner expression `f₀.recessionCone ∩ -(f₀.recessionCone)`
rewrites to `f₀.constancySpace`. -/
@[simp] theorem recessionCone_inter_neg_recessionCone_eq_constancySpace
    (f₀ : X → WithTopBot α) :
    f₀.recessionCone ∩ -(f₀.recessionCone) = f₀.constancySpace :=
  rfl

/-- The constancy space can equivalently be written in the lineality-style order as the
intersection of the negative and positive recession cones. -/
theorem constancySpace_eq_neg_recessionCone_inter_recessionCone (f₀ : X → WithTopBot α) :
    f₀.constancySpace = -(f₀.recessionCone) ∩ f₀.recessionCone := by
  simp [constancySpace, Set.inter_comm]

/-- Source-order compatibility bridge from the lineality-style intersection back to the canonical
owner `f₀.constancySpace`. -/
@[simp] theorem neg_recessionCone_inter_recessionCone_eq_constancySpace
    (f₀ : X → WithTopBot α) :
    -(f₀.recessionCone) ∩ f₀.recessionCone = f₀.constancySpace := by
  rw [constancySpace_eq_neg_recessionCone_inter_recessionCone]

/-- Canonical owner-level membership bridge for the intersection expression in Definition 8.7.0. -/
@[simp] theorem mem_constancySpace_iff_mem_recessionCone_and_mem_neg_recessionCone
    {f₀ : X → WithTopBot α} {y : X} :
    y ∈ f₀.constancySpace ↔ y ∈ f₀.recessionCone ∧ y ∈ -(f₀.recessionCone) := by
  simp [constancySpace]

/-- A vector belongs to the constancy space exactly when both the opposite direction and the
original direction lie in the recession cone. -/
theorem mem_constancySpace_iff_neg_mem_recessionCone {f₀ : X → WithTopBot α} {y : X} :
    y ∈ f₀.constancySpace ↔ -y ∈ f₀.recessionCone ∧ y ∈ f₀.recessionCone := by
  rw [constancySpace_eq_neg_recessionCone_inter_recessionCone, Set.mem_inter_iff, Set.mem_neg]

/-- A vector belongs to the constancy space exactly when the recession function is nonpositive in
both that direction and its opposite. -/
@[simp] theorem mem_constancySpace_iff_mem_recessionCone
    {f₀ : X → WithTopBot α} {y : X} :
    y ∈ f₀.constancySpace ↔ y ∈ f₀.recessionCone ∧ -y ∈ f₀.recessionCone := by
  rw [mem_constancySpace_iff_mem_recessionCone_and_mem_neg_recessionCone, Set.mem_neg]

/-- A vector belongs to the constancy space exactly when the recession function is nonpositive in
both that direction and its opposite. -/
@[simp] theorem mem_constancySpace_iff {f₀ : X → WithTopBot α} {y : X} :
    y ∈ f₀.constancySpace ↔ f₀ y ≤ 0 ∧ f₀ (-y) ≤ 0 := by
  rw [mem_constancySpace_iff_mem_recessionCone, mem_recessionCone_iff, mem_recessionCone_iff]

end Function

end

section

open scoped Pointwise

variable {X α : Type*} [Neg X] [Preorder α] [Zero α]

namespace Function

/-- On a preorder codomain, the constancy space is the intersection of the `0`-sublevel preimage
and its pointwise negation. -/
theorem constancySpace_eq_preimage_Iic_inter_neg_preimage_Iic (f₀ : X → WithTopBot α) :
    f₀.constancySpace = (f₀ ⁻¹' Set.Iic (0 : WithTopBot α)) ∩
      -(f₀ ⁻¹' Set.Iic (0 : WithTopBot α)) := by
  ext y
  simp [constancySpace, Set.mem_neg]

/-- Canonicalization bridge: the `Set.Iic` preimage intersection expression rewrites back to the
owner `f₀.constancySpace`. -/
@[simp] theorem preimage_Iic_inter_neg_preimage_Iic_eq_constancySpace
    (f₀ : X → WithTopBot α) :
    (f₀ ⁻¹' Set.Iic (0 : WithTopBot α)) ∩
      -(f₀ ⁻¹' Set.Iic (0 : WithTopBot α)) = f₀.constancySpace := by
  rw [constancySpace_eq_preimage_Iic_inter_neg_preimage_Iic]

end Function

end
