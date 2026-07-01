import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped Pointwise

section

variable {P : Type u} {E : Type v}

/- 
Source/core/bridge triage:
- `source-facing`: Definition 8.0.2 introduces the recession cone of a subset `C` as the
  set of all directions `y` such that every ray `x + λ y` with base point `x ∈ C` and scalar
  `λ ≥ 0` stays in `C`.
- `core/canonical`: there is no pre-existing primitive bundled recession-cone owner in the
  current mathlib/project context, so the primary public API is the source-facing set-valued
  definition on an ambient set `Set P` with directions in `E`.
- `bridge/view`: the owner remains `recessionCone`, while the public theorem surface is written
  with the scalar-annotated notation `0⁺[𝕜] C`. The theorem `Set.mem_recessionCone_iff` rewrites
  membership in that owner into the textbook quantifier form;
  `Set.mem_recessionCone_iff_nonneg_vaddSet_subset` and `Set.mem_recessionCone_iff_vadd` give
  the intrinsic affine-action bridge surfaces; and
  `Set.neg_mem_recessionCone_neg_iff` records the canonical negation symmetry of that owner.
- Primitive data vs derived API: the primitive object is just the subset of admissible recession
  directions. The source mentions `C ⊆ ℝ^n`, but the defining formula itself only needs an
  ambient action `x + a • y`, so the owner declaration is kept at the weaker scalar-parameterized
  and affine-ambient level instead of freezing a real vector-space model into the public API.
- Owner-shape refinement: the scalar type is a genuine owner parameter that cannot be recovered
  from `C`, so it is made explicit in the raw declaration `C.recessionCone 𝕜`; the notation
  `0⁺[𝕜] C` is the source-facing surface that suppresses the auxiliary ambient parameters.
- Domain-style sampling: the relevant owner-side comparison targets in this domain are the chapter
  predicate `Set.IsCone 𝕜` and mathlib's `asymptoticCone 𝕜 C` for later closed-convex bridges.
  The present item keeps the set-valued owner as primary; bundled cone views should use the
  canonical owner `ConvexCone.hull` directly.
-/

/-- Definition 8.0.2: the recession cone of a subset `C` is the set of directions `y`
such that `x + λ • y ∈ C` for every `x ∈ C` and every scalar `λ ≥ 0`. -/
def Set.recessionCone (C : Set P) (𝕜 : Type w) [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P] :
    Set E :=
  {y | ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C}

end

/-- Scalar-annotated recession-cone notation `0⁺[𝕜] C`. -/
-- Lean does not admit numeral-leading atoms in plain `notation`, and `n⁺` already parses as a
-- built-in form, so this textbook token uses a minimal parser bridge.
macro:max n:num noWs "⁺[" 𝕜:term "]" C:term:max : term => do
  let some k := n.raw.isNatLit? | Lean.Macro.throwUnsupported
  unless k == 0 do
    Lean.Macro.throwErrorAt n "expected `0⁺`"
  `(Set.recessionCone $C $𝕜)

section

variable {𝕜 : Type w} {P : Type u} {E : Type v}
  [Zero 𝕜] [LE 𝕜] [SMul 𝕜 E] [HAdd P E P]

namespace Set

/-- Membership in the recession cone is exactly the textbook condition that every forward ray from
every point of `C` in direction `y` remains in `C`. -/
@[simp] theorem mem_recessionCone_iff {C : Set P} {y : E} :
    y ∈ 0⁺[𝕜] C ↔ ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → x + a • y ∈ C :=
  Iff.rfl

@[simp] theorem recessionCone_empty :
    0⁺[𝕜] (∅ : Set P) = (Set.univ : Set E) := by
  ext y
  simp [Set.mem_recessionCone_iff]

@[simp] theorem recessionCone_univ :
    0⁺[𝕜] (Set.univ : Set P) = (Set.univ : Set E) := by
  ext y
  simp [Set.mem_recessionCone_iff]

end Set

end

section

variable {𝕜 : Type w} {E : Type v}
  [Zero 𝕜] [LE 𝕜] [AddCommSemigroup E] [SMul 𝕜 E]

namespace Set

/-- Recession-cone membership is equivalent to stability under every nonnegative scalar translate
in the intrinsic affine-action form. -/
theorem mem_recessionCone_iff_nonneg_vaddSet_subset {C : Set E} {y : E} :
    y ∈ 0⁺[𝕜] C ↔ ∀ a : 𝕜, 0 ≤ a → a • y +ᵥ C ⊆ C := by
  constructor
  · intro hy a ha z hz
    rcases Set.mem_vadd_set.mp hz with ⟨x, hx, rfl⟩
    simpa [vadd_eq_add, add_comm] using (Set.mem_recessionCone_iff.mp hy) x hx a ha
  · intro h
    rw [Set.mem_recessionCone_iff]
    intro x hx a ha
    exact h a ha (Set.mem_vadd_set.mpr ⟨x, hx, by simp [vadd_eq_add, add_comm]⟩)

/-- Additive-ambient intrinsic-action rewrite of recession-cone membership. -/
theorem mem_recessionCone_iff_vadd {C : Set E} {y : E} :
    y ∈ 0⁺[𝕜] C ↔ ∀ x ∈ C, ∀ a : 𝕜, 0 ≤ a → a • y +ᵥ x ∈ C := by
  constructor
  · intro hy x hx a ha
    exact (Set.mem_recessionCone_iff_nonneg_vaddSet_subset.mp hy) a ha
      (Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩)
  · intro h
    exact (Set.mem_recessionCone_iff_nonneg_vaddSet_subset).2 <| by
      intro a ha z hz
      rcases Set.mem_vadd_set.mp hz with ⟨x, hx, rfl⟩
      exact h x hx a ha

end Set

end

section

variable {𝕜 : Type w} {E : Type v} [Zero 𝕜] [LE 𝕜] [AddCommGroup E] [DistribSMul 𝕜 E]

namespace Set

/-- Negating both the set and the direction preserves recession-cone membership. -/
theorem neg_mem_recessionCone_neg_iff {C : Set E} {y : E} :
    -y ∈ 0⁺[𝕜] (-C) ↔ y ∈ 0⁺[𝕜] C := by
  rw [Set.mem_recessionCone_iff, Set.mem_recessionCone_iff]
  constructor
  · intro h x hx t ht
    have hmem : -x + t • (-y) ∈ -C := h (-x) (by simpa using hx) t ht
    simpa [smul_neg, add_comm, add_left_comm, add_assoc] using Set.mem_neg.mp hmem
  · intro h x hx t ht
    change -(x + t • -y) ∈ C
    have hx_neg : -x ∈ C := by simpa using hx
    simpa [smul_neg, add_comm, add_left_comm, add_assoc] using h (-x) hx_neg t ht

end Set

end
