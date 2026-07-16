import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u v w

open scoped Pointwise

variable {P : Type u} {E : Type v} [Neg E]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.4.2 introduces the lineality space of a set `C`, namely the
  symmetric recession-direction set `(-0⁺[𝕜] C) ∩ 0⁺[𝕜] C`.
- `core/canonical`: the chapter owner abstraction in this domain is the generic scalar-parameterized
  recession cone `0⁺[𝕜] C`; the lineality space is therefore defined directly from that primitive
  owner in canonical conjunction order `0⁺[𝕜] C ∩ -0⁺[𝕜] C`.
- `bridge/view`: the companion theorems `mem_lineal_iff`,
  `mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone`, and
  `mem_lineal_iff_forall` unpack the source-facing owner into symmetric recession membership and
  then into the textbook ray
  quantifiers.
- Primitive data vs derived API: the primitive owner data are exactly the two recession conditions
  encoded by `0⁺[𝕜] C ∩ -0⁺[𝕜] C`; the quantifier expansion is derived API. No convexity,
  nonemptiness, or bundled-cone structure is primitive here.
- Layer target: this file provides the `source-facing` owner object on `Set`, not a second bundled
  cone abstraction.

Domain-style sampling used here:
- the owner declaration `Set.recessionCone` from Definition 8.0.2;
- the owner-side membership bridge `Set.mem_recessionCone_iff`.
-/

namespace Set

/-- Definition 8.4.2: the lineality set of `C`, i.e. the symmetric recession-direction set
`0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
def lineal (𝕜 : Type w) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P] (C : Set P) : Set E :=
  0⁺[𝕜] C ∩ -0⁺[𝕜] C

scoped[Rockafellar] notation "lin[" 𝕜 "](" C ")" => Set.lineal 𝕜 C

open scoped Rockafellar

variable {𝕜 : Type w} [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P]

/-- Canonical membership bridge: `y ∈ lin[𝕜](C)` iff both `y` and `-y` are recession directions
of `C`. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone_and_mem_neg_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ y ∈ -0⁺[𝕜] C := by
  simp [Set.lineal]

/-- Compatibility bridge from owner-level negated-cone membership to element-level negation. -/
@[simp] theorem mem_lineal_iff_mem_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ -y ∈ 0⁺[𝕜] C := by
  simp [Set.mem_neg, mem_lineal_iff_mem_recessionCone_and_mem_neg_recessionCone]

/-- Canonical membership bridge: conjunction order follows
`lin[𝕜](C) = 0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
@[simp] theorem mem_lineal_iff {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ y ∈ 0⁺[𝕜] C ∧ -y ∈ 0⁺[𝕜] C :=
  mem_lineal_iff_mem_recessionCone

/-- Unfolding bridge: `lin[𝕜](C)` is definitionally the canonical owner expression
`0⁺[𝕜] C ∩ -0⁺[𝕜] C`. -/
theorem lineal_eq_recessionCone_inter_neg_recessionCone (C : Set P) :
    lin[𝕜](C) = ((0⁺[𝕜] C) ∩ (-0⁺[𝕜] C) : Set E) :=
  rfl

/-- Canonicalization bridge: the raw owner expression `0⁺[𝕜] C ∩ -0⁺[𝕜] C` rewrites to
`lin[𝕜](C)`. -/
theorem recessionCone_inter_neg_recessionCone_eq_lineal (C : Set P) :
    ((0⁺[𝕜] C) ∩ (-0⁺[𝕜] C) : Set E) = lin[𝕜](C) :=
  rfl

/-- Source-order compatibility bridge with the source-facing `(−y, y)` conjunction order. -/
theorem mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔ -y ∈ 0⁺[𝕜] C ∧ y ∈ 0⁺[𝕜] C := by
  rw [mem_lineal_iff, and_comm]

/-- The source-facing textbook formula for the lineality space is the intersection of the negative
and positive recession cones. -/
theorem lineal_eq_neg_recessionCone_inter_recessionCone (C : Set P) :
    lin[𝕜](C) = (-0⁺[𝕜] C ∩ 0⁺[𝕜] C : Set E) :=
  by
    ext y
    simp [Set.lineal, and_comm]

/-- Membership in `lin[𝕜](C)` means that both `y` and `-y` are recession directions of `C`,
expanded into the textbook ray-preservation quantifiers. -/
theorem mem_lineal_iff_forall {C : Set P} {y : E} :
    y ∈ lin[𝕜](C) ↔
      (∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • (-y) ∈ C) ∧
        ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C := by
  simpa [Set.mem_recessionCone_iff] using
    (mem_lineal_iff_neg_mem_recessionCone_and_mem_recessionCone (𝕜 := 𝕜) (C := C) (y := y))

end Set

end
