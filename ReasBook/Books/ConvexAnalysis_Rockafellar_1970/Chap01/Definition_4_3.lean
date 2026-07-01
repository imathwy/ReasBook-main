import Mathlib.Tactic.Recall
import Mathlib.Analysis.Convex.Function

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
`source-facing`: Definition 4.3 says that a function on `s` is affine exactly when it is both
  convex and concave on `s`; the textbook real-valued statement is a specialization of this
  canonical owner surface.
- `core/canonical`: use the existing mathlib owners `ConvexOn` and `ConcaveOn`, surfaced directly
  by the chapter notation `affOn[𝕜](f, s)`.
- `bridge/view`: the affine-combination equality view is exposed as a theorem-level bridge from
  `ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f`.
- Primitive data vs derived API: the primitive inputs are the scalar system `𝕜`, the set `s`, and
  the ambient function `f : E → β`; the affine-equality statement is derived bridge API.
- Domain-style sampling: `ConvexOn`, `ConcaveOn`, `convexOn_iff_forall_pos`,
  `concaveOn_iff_forall_pos`, and the chapter's generalized Jensen owner theorem in Theorem 4.3.
- Layer target: canonical existing owners + source-facing notation.
-/

section

variable {𝕜 E β : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [SMul 𝕜 E]
variable [AddCommMonoid β] [PartialOrder β] [SMul 𝕜 β]

/- Definition 4.3 recalls the canonical convex-on predicate. -/
recall ConvexOn

/- Together with `ConvexOn`, `ConcaveOn` gives the source notion of an affine function on a set. -/
recall ConcaveOn

/-- Textbook notation for affine-on-set predicates from Definition 4.3, expressed directly by the
canonical `ConvexOn`/`ConcaveOn` conjunction. -/
scoped[Rockafellar] notation:max "affOn[" 𝕜 "](" f ", " s ")" =>
  ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f

open scoped Rockafellar

@[simp] theorem affOn_iff_convexOn_concaveOn {s : Set E} {f : E → β} :
    affOn[𝕜](f, s) ↔ (ConvexOn 𝕜 s f ∧ ConcaveOn 𝕜 s f) :=
  Iff.rfl

/-- Ordered-codomain bridge for Definition 4.3: convexity and concavity on the same set are
exactly the affine-combination equality condition. -/
@[simp] theorem affOn_iff_forall_eq_affineCombination {s : Set E} {f : E → β} :
    affOn[𝕜](f, s) ↔
      Convex 𝕜 s ∧
        ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
          f (a • x + b • y) = a • f x + b • f y := by
  constructor
  · rintro ⟨hconvex, hconcave⟩
    refine ⟨hconvex.1, ?_⟩
    intro x hx y hy a b ha hb hab
    exact le_antisymm (hconvex.2 hx hy ha hb hab) (hconcave.2 hx hy ha hb hab)
  · rintro ⟨hs, heq⟩
    refine
      ⟨⟨hs, fun x hx y hy a b ha hb hab => (heq hx hy ha hb hab).le⟩,
        ⟨hs, fun x hx y hy a b ha hb hab => (heq hx hy ha hb hab).ge⟩⟩

/-- Constructor in canonical owner language. -/
theorem affOn_of_convexOn_concaveOn {s : Set E} {f : E → β}
    (hconvex : ConvexOn 𝕜 s f) (hconcave : ConcaveOn 𝕜 s f) :
    affOn[𝕜](f, s) :=
  ⟨hconvex, hconcave⟩

/-- Extract the affine-combination equality view from the canonical owner pair. -/
theorem affOn_eq_affineCombination {s : Set E} {f : E → β} (hf : affOn[𝕜](f, s)) :
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : 𝕜⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • y) = a • f x + b • f y :=
  (affOn_iff_forall_eq_affineCombination (s := s) (f := f)).1 hf |>.2

end
