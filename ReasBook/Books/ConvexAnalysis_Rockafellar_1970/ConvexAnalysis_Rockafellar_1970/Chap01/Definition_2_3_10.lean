import Mathlib.Analysis.Convex.Hull

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.3.10 introduces the convex hull of a subset `S` as the
  intersection of all convex sets containing `S`.
- `core/canonical`: mathlib's owner abstraction is `convexHull 𝕜 s`, the convex-hull closure
  operator on sets.
- `bridge/view`: the textbook's intersection wording is the theorem `convexHull_eq_iInter`.
- Domain-style sampling used here: `convexHull`, `subset_convexHull`, `convex_convexHull`,
  `Convex.convexHull_subset_iff`, and `convexHull_eq_iInter` from
  `Mathlib.Analysis.Convex.Hull`.
- Primitive data vs derived API: the primitive owner interface is the closure-style package
  (`subset_convexHull`, `convex_convexHull`, `Convex.convexHull_subset_iff`) around `convexHull`;
  the explicit intersection formula is derived API and is exposed as a notation-first bridge
  theorem.
- Layer target: `core/canonical`; this item keeps `convexHull` as raw owner, while exposing short
  chapter-surface bridge theorems stated directly in `conv[𝕜]` notation.
-/

/- Abstraction checks for this item:
- Codomain/ambient layer: this item is set-valued (`Set E`), so no ordered extended-codomain
  generalization axis (`EReal`/`WithTopBot`) is involved.
- Scalar/ambient structure: reused upstream owners (`convexHull`, `subset_convexHull`,
  `convex_convexHull`, `convexHull_eq_iInter`) already live at the weakest layer
  `[Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]`; this file stays on that layer.
- Owner choice: keep `convexHull`/`Convex` as primitive owners; the textbook intersection
  formulations are bridge theorems.
- Topology language: not applicable for this item.
- Notation/API surface: keep the chapter notation `conv[𝕜]`, and expose a binder-light
  subtype-intersection surface to avoid proof-binder noise on theorem statements.
-/

/-- Textbook notation for the convex hull of a set. The raw owner remains `convexHull`. -/
scoped[Rockafellar] notation:max "conv[" 𝕜 "] " s => convexHull 𝕜 s

open scoped Rockafellar

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]

namespace Set

/-- Definition 2.3.10 on the chapter surface: every set is contained in its convex hull. -/
theorem subset_conv {s : Set E} : s ⊆ conv[𝕜] s :=
  subset_convexHull 𝕜 s

/-- The convex hull is convex. -/
theorem convex_conv {s : Set E} : Convex 𝕜 (conv[𝕜] s) :=
  convex_convexHull 𝕜 s

/-- Minimality principle in canonical iff form: for convex `t`, containment of `conv[𝕜] s` in `t`
is equivalent to containment of `s` in `t`. -/
theorem conv_subset_iff {s t : Set E} (ht : Convex 𝕜 t) :
    (conv[𝕜] s) ⊆ t ↔ s ⊆ t := by
  simpa using (ht.convexHull_subset_iff (s := s))

/-- Minimality principle in direct implication form: any convex superset of `s` contains
`conv[𝕜] s`. -/
theorem conv_subset {s t : Set E} (hst : s ⊆ t) (ht : Convex 𝕜 t) :
    (conv[𝕜] s) ⊆ t :=
  convexHull_min hst ht

/-- The convex hull as an intersection over the subtype of convex supersets. This keeps the
statement surface free of iterated proof binders. -/
theorem conv_eq_iInter_subtype {s : Set E} :
    (conv[𝕜] s) = ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iInter.2 ?_
    intro u
    exact (conv_subset (s := s) (t := (u : Set E)) u.2.1 u.2.2) hx
  · intro hx
    have hx' := Set.mem_iInter.1 hx ⟨conv[𝕜] s, subset_conv, convex_conv⟩
    simpa using hx'

/-- The textbook intersection description of the convex hull. -/
theorem conv_eq_sInter {s : Set E} :
    (conv[𝕜] s) = ⋂₀ {t : Set E | s ⊆ t ∧ Convex 𝕜 t} := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
      simpa [conv_eq_iInter_subtype] using hx
    refine Set.mem_sInter.2 ?_
    intro t ht
    exact Set.mem_iInter.1 hx' ⟨t, ht⟩
  · intro hx
    have hx' : x ∈ ⋂ u : {t : Set E // s ⊆ t ∧ Convex 𝕜 t}, (u : Set E) := by
      refine Set.mem_iInter.2 ?_
      intro u
      exact Set.mem_sInter.1 hx u u.2
    simpa [conv_eq_iInter_subtype] using hx'

/-- The textbook intersection description of the convex hull, in iterated-`iInter` form. -/
theorem conv_eq_iInter {s : Set E} :
    (conv[𝕜] s) = ⋂ (t : Set E) (_ : s ⊆ t) (_ : Convex 𝕜 t), t := by
  simpa [Set.iInter_subtype, Set.iInter_and] using
    (conv_eq_iInter_subtype (𝕜 := 𝕜) (s := s))

end Set

end
