import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set

section

variable {𝕜 : Type w} {P : Type u} {E : Type v}
  [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P] [Zero E]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.0.1 says that `C` recedes in the direction `y`, i.e. `y` is a
  nonzero recession direction of `C`.
- `core/canonical`: the owner abstraction in this chapter is the set-valued recession cone
  `recessionCone C` from Definition 8.0.2.
- `source-facing owner`: `Set.RecedesInDirection` is the textbook nonzero-direction predicate,
  defined directly from the core owner `recessionCone`.

Domain-style sampling used here:
- the project owner `recessionCone` and its owner-side API `Set.mem_recessionCone_iff` from
  Definition 8.0.2;
- the later real-specialized bridge `recessionCone_eq_asymptoticCone` in Theorem 8.2,
  connecting the chapter owner to mathlib's `asymptoticCone`;
- mathlib's higher-level owner `asymptoticCone` in
  `Mathlib/Topology/Algebra/AsymptoticCone.lean`.

Primitive data vs derived API:
- primitive source-facing content: only the nonzero direction `y` together with owner membership
  `y ∈ recessionCone C`;
- derived API: the ray-closure clause `x + t • y ∈ C` is exposed by the companion theorem
  `recedesInDirection_iff_forall` via `Set.mem_recessionCone_iff`, while
  `recedesInDirection_iff` keeps the primitive owner bridge explicit; the
  negation symmetry is reused from
  the owner theorem `Set.neg_mem_recessionCone_neg_iff` in Definition 8.0.2.
-/

namespace Set

variable (𝕜)

/-- Definition 8.0.1: a set `C` recedes in the direction of a vector `y` when `y` is nonzero and
every nonnegative translate `x + λ • y` of a point `x ∈ C` remains in `C`.

The scalar is a core owner parameter for this notion and cannot be recovered from `C` and `y`, so
the primary owner is scalar-parameterized. The textbook real statement is a specialization. -/
def RecedesInDirection (C : Set P) (y : E) : Prop :=
  y ∈ 0⁺[𝕜] C ∧ y ≠ 0

variable {𝕜}

namespace RecedesInDirection

theorem ne_zero {C : Set P} {y : E} (hy : C.RecedesInDirection 𝕜 y) : y ≠ 0 :=
  hy.2

theorem mem_recessionCone {C : Set P} {y : E} (hy : C.RecedesInDirection 𝕜 y) :
    y ∈ 0⁺[𝕜] C :=
  hy.1

theorem of_mem_recessionCone {C : Set P} {y : E}
    (hy_ne : y ≠ 0) (hy_mem : y ∈ 0⁺[𝕜] C) :
    C.RecedesInDirection 𝕜 y :=
  ⟨hy_mem, hy_ne⟩

end RecedesInDirection

/-- Source-order bridge: a source-facing recession direction is exactly a nonzero recession-cone
vector. -/
theorem recedesInDirection_iff {C : Set P} {y : E} :
    C.RecedesInDirection 𝕜 y ↔ y ≠ 0 ∧ y ∈ 0⁺[𝕜] C :=
  by simp [RecedesInDirection, and_comm]

/-- Primitive owner-level bridge: a source-facing recession direction is exactly a nonzero
recession-cone vector. -/
@[simp] theorem recedesInDirection_iff_mem_recessionCone {C : Set P} {y : E} :
    C.RecedesInDirection 𝕜 y ↔ y ∈ 0⁺[𝕜] C ∧ y ≠ 0 :=
  Iff.rfl

/-- The source-facing recession-direction predicate in explicit ray-quantifier form. -/
theorem recedesInDirection_iff_forall {C : Set P} {y : E} :
    C.RecedesInDirection 𝕜 y ↔ y ≠ 0 ∧ ∀ x ∈ C, ∀ t : 𝕜, 0 ≤ t → x + t • y ∈ C := by
  rw [recedesInDirection_iff, Set.mem_recessionCone_iff]

end Set

end

section

variable {𝕜 : Type w} {E : Type v}
  [Zero 𝕜] [LE 𝕜] [AddCommGroup E] [DistribSMul 𝕜 E]

namespace Set

/-- Negating both the set and the direction preserves the source-facing recession-direction
predicate. -/
theorem recedesInDirection_neg_iff {C : Set E} {y : E} :
    (-C).RecedesInDirection 𝕜 (-y) ↔ C.RecedesInDirection 𝕜 y := by
  rw [RecedesInDirection, RecedesInDirection, neg_ne_zero, Set.neg_mem_recessionCone_neg_iff]

end Set

end
