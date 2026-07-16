import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_0_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {𝕜 : Type v} {P : Type u} {E : Type w}
  [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P] [Zero E]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 8.0.3 names the set of nonzero recession directions of `C`.
- `core/canonical`: the owner is the source predicate
  `Set.RecedesInDirection`, collected as a set of directions.
- `bridge/view`: membership in this owner is equivalent to the canonical nonzero
  recession-cone slice `0⁺[𝕜] C \ ({0} : Set E)` and to the explicit
  ray-quantifier formula from `Set.recedesInDirection_iff_forall`.
- Primitive data vs derived API: no convexity/topological assumptions are primitive here; the owner
  only uses nonnegative scalar rays and nonzeroness through
  `Set.RecedesInDirection`, exactly as in Definition 8.0.1.
- Layer target: `source-facing` owner declaration with canonical bridges.

Domain-style sampling used here:
- the set owner `recessionCone` (`0⁺[𝕜] C`) from Definition 8.0.2;
- the owner predicate bridge `Set.RecedesInDirection` and its canonical bridge theorem
  `Set.recedesInDirection_iff_mem_recessionCone` from Definition 8.0.1;
- the quantifier bridge `Set.recedesInDirection_iff_forall`.
-/

namespace Set

variable (𝕜)

/-- Definition 8.0.3: the recession directions of `C` are the nonzero vectors `y` such that every
forward ray `x + a • y` (`x ∈ C`, `0 ≤ a`) stays in `C`. -/
def recessionDirections (C : Set P) : Set E :=
  {y | C.RecedesInDirection 𝕜 y}

variable {𝕜}

/-- Canonical membership bridge: `y` is a recession direction iff it lies in the recession cone and
is nonzero. -/
@[simp] theorem mem_recessionDirections_iff_mem_recessionCone {C : Set P} {y : E} :
    y ∈ recessionDirections 𝕜 C ↔ y ∈ 0⁺[𝕜] C ∧ y ≠ 0 := by
  simp [recessionDirections, Set.recedesInDirection_iff_mem_recessionCone]

/-- Compatibility bridge with the source-facing predicate `C.RecedesInDirection 𝕜 y`. -/
@[simp] theorem mem_recessionDirections_iff {C : Set P} {y : E} :
    y ∈ recessionDirections 𝕜 C ↔ C.RecedesInDirection 𝕜 y := by
  rfl

/-- Membership in `recessionDirections` rewritten in textbook ray-quantifier form. -/
theorem mem_recessionDirections_iff_forall {C : Set P} {y : E} :
    y ∈ recessionDirections 𝕜 C ↔
      y ≠ 0 ∧ ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C := by
  rw [mem_recessionDirections_iff, recedesInDirection_iff_forall]

/-- The recession directions are exactly the recession-cone vectors excluding `0`. -/
theorem recessionDirections_eq_recessionCone_diff_singleton {C : Set P} :
    recessionDirections 𝕜 C = 0⁺[𝕜] C \ ({0} : Set E) :=
  by
    ext y
    simp [recessionDirections, Set.recedesInDirection_iff_mem_recessionCone]

end Set

end
