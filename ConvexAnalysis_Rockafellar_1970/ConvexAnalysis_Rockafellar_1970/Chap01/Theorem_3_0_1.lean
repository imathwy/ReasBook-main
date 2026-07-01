import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-
Source/core/bridge triage:
- `source-facing`: Theorem 3.0.1 says that translating a convex subset by a fixed element of the
  ambient module again yields a convex set.
- `core/canonical`: mathlib's intrinsic translation owner is `Convex.vadd`, expressing convexity
  of the translated set `a +ᵥ C` directly.
- `bridge/view`: source-facing set-translation presentations are recovered by intrinsic
  `VAdd`-owner bridge lemmas: `Set.vaddSet`, `Set.image_vadd`, `Set.singleton_vadd`,
  and `Set.vadd_singleton`.
- Primitive data vs derived API: the convexity predicate `Convex 𝕜 C` is primitive; preservation
  under translation is the canonical derived theorem and needs no new owner definition.
- Domain-style sampling: this item is governed by `Convex.vadd` and the set-level bridge owners
  `Set.vaddSet`, `Set.image_vadd`, `Set.singleton_vadd`, `Set.vadd_singleton`.
- Layer target: `core/canonical`; keep the owner theorem on the intrinsic set-translation surface
  with `+ᵥ` notation, and expose only minimal source-facing bridge lemmas.
-/

/- Canonicalization decision record (this pass):
- Codomain/ambient check: no ordered-extended codomain owner appears in this item.
- Scalar/ambient-structure check: no extra specialization (e.g. `ℝ`, Euclidean model) is needed;
  `Convex.vadd` already stays at the generic convex-space layer.
- Owner check: keep the intrinsic translation owner `Convex.vadd`; use only bridge/view lemmas
  that restate the same translated set in source-facing image/singleton language.
- Topology check: not a topology-facing statement, so intrinsic/relative topology is irrelevant.
- Owner-name/notation check: use the short canonical owner name and textbook-primary notation
  surface `a +ᵥ C`.
-/

/- Theorem 3.0.1: for a convex set `C`, every translate of `C` by `a` is convex.
This is exactly the intrinsic owner theorem `Convex.vadd`. -/
recall Convex.vadd

/- Canonical set-translation owner notation surface. -/
recall Set.vaddSet

/- Map/image bridge for translations used in source-facing additive-map wording. -/
recall Set.image_vadd

/- Singleton-left translation bridge `{a} +ᵥ C`. -/
recall Set.singleton_vadd

/- Singleton-right translation bridge `C +ᵥ {a}`. -/
recall Set.vadd_singleton

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Source-facing image view of Theorem 3.0.1 at the intrinsic `VAdd` bridge layer. -/
theorem Convex.image_vadd {C : Set E} (hC : Convex 𝕜 C) (a : E) :
    Convex 𝕜 ((fun x : E => a +ᵥ x) '' C) := by
  simpa [Set.image_vadd] using hC.vadd a

end
