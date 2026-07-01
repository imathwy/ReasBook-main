import Mathlib.Algebra.Group.Pointwise.Set.Lattice
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
- `source-facing`: Text 3.1.5 expresses a Minkowski sum as a union of translates of one set by
  points of the other.
- `core/canonical`: the intrinsic translation owner is pointwise set `vadd` on `Set α` and `Set β`
  via `Set.iUnion_vadd_left_image`; additive Minkowski sum is its self-action specialization.
- `bridge/view`: the translate of `C₂` by `x₁` is the singleton left action
  `({x₁} : Set α) +ᵥ C₂`, and `Set.singleton_vadd` identifies this with the direct translate
  `x₁ +ᵥ C₂`. In the additive specialization, `Set.singleton_add` gives the textbook
  `{x₁} + C₂` form.
- Primitive data vs derived API: the primitive data are a left action and the two sets; the
  additive Minkowski surface is a specialization theorem.
- Domain-style sampling: this item aligns with `Set.iUnion_vadd_left_image`,
  `Set.singleton_vadd`, `Set.iUnion_add_left_image`, and `Set.singleton_add`.
- Layer target: `core/canonical`; reuse the intrinsic `+ᵥ` owner directly, then give only the
  non-duplicate textbook additive singleton bridge as a specialization.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: keep the codomain at intrinsic `Set` translation owners (`+ᵥ` / `+`);
  no concrete codomain such as `ℝ` or `EReal` is mathematically needed.
- Scalar/ambient-structure check: keep only primitive action/additive assumptions (`[VAdd α β]`,
  `[Add γ]`) required by the reused canonical owners.
- Owner check: use canonical owners `Set.iUnion_vadd_left_image` and
  `Set.iUnion_add_left_image`; expose the source-facing theorem first at the intrinsic `+ᵥ`
  owner surface, then add the additive theorem as a specialization bridge.
- Topology check: this item is algebraic (translation of sets), so no ambient-vs-intrinsic
  topology migration applies.
- Owner-name check: keep short theorem names for the source-facing bridge surfaces only.
- Notation check: keep the intrinsic `x +ᵥ C` owner surface for `vadd`, and use textbook-primary
  singleton notation `{x} + C` on the additive theorem surface.
-/

/- Intrinsic translation owner used by Text 3.1.5: pointwise set `vadd` is the union of left
translates. -/
recall Set.iUnion_vadd_left_image

/- Singleton-left translate bridge for the intrinsic `vadd` owner. -/
recall Set.singleton_vadd

/- Additive specialization used for Minkowski sum in the textbook surface. -/
recall Set.iUnion_add_left_image

/- Singleton-left translate bridge for additive Minkowski sum. -/
recall Set.singleton_add

open scoped Pointwise

namespace Set

section VAddSurface

variable {α β : Type*} [VAdd α β] (D₁ : Set α) (D₂ : Set β)

/-- Primitive intrinsic translation-union owner surface for Text 3.1.5. -/
theorem iUnion_mem_vadd : (⋃ x₁ ∈ D₁, x₁ +ᵥ D₂) = D₁ +ᵥ D₂ :=
  Set.iUnion_vadd_left_image (s := D₁)

/-- Source-facing singleton-translate bridge for Text 3.1.5. -/
theorem iUnion_singleton_vadd : (⋃ x₁ ∈ D₁, ({x₁} : Set α) +ᵥ D₂) = D₁ +ᵥ D₂ := by
  -- Rewrite singleton translates to point translates, then invoke the canonical owner theorem.
  calc
    (⋃ x₁ ∈ D₁, ({x₁} : Set α) +ᵥ D₂) = (⋃ x₁ ∈ D₁, x₁ +ᵥ D₂) := by
      simp [Set.singleton_vadd]
    _ = D₁ +ᵥ D₂ := iUnion_mem_vadd (D₁ := D₁) (D₂ := D₂)

end VAddSurface

section AdditiveSurface

variable {γ : Type*} [Add γ] (D₁ D₂ : Set γ)

/-- Primitive additive translation-union owner surface for the additive specialization. -/
theorem iUnion_mem_add : (⋃ x₁ ∈ D₁, (fun x₂ : γ ↦ x₁ + x₂) '' D₂) = D₁ + D₂ :=
  Set.iUnion_add_left_image (s := D₁) (t := D₂)

/-- Text 3.1.5: the Minkowski sum is the union of singleton left translates. -/
theorem iUnion_singleton_add : (⋃ x₁ ∈ D₁, {x₁} + D₂) = D₁ + D₂ := by
  -- Convert the textbook singleton-translate notation to the additive image surface.
  simpa [Set.singleton_add] using (iUnion_mem_add (D₁ := D₁) (D₂ := D₂))

end AdditiveSurface

end Set
