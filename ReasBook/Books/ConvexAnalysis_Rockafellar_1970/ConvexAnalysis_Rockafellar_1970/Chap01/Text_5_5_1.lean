import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

variable {E : Type u} {𝕜 : Type v} {α : Type w}
variable [Semiring 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

open Function

namespace Function

/-- Helper for Text 5.5.1: the `WithTopBot α`-valued heights of the vertical fiber of `F`
above `x`. -/
def verticalHeights (F : Set (E × α)) (x : E) : Set (WithTopBot α) :=
  ((↑) : α → WithTopBot α) '' {μ : α | (x, μ) ∈ F}

/-- Helper for Text 5.5.1: the function attached to `F` by taking the infimum of the
vertical heights above each base point. -/
noncomputable def verticalInfimum [ConditionallyCompleteLattice α] (F : Set (E × α)) :
    E → WithTopBot α :=
  fun x ↦ sInf (verticalHeights F x)

omit [AddCommMonoid E] in
/-- Helper for Text 5.5.1: `verticalInfimum` is definitionally the infimum of
`verticalHeights`. -/
theorem verticalInfimum_eq_sInf_verticalHeights [ConditionallyCompleteLattice α]
    (F : Set (E × α)) (x : E) :
    verticalInfimum (E := E) F x = sInf (verticalHeights (E := E) F x) :=
  rfl

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.1 defines the convex hull `conv(g)` of a function `g` by taking the
  infimum of the vertical fiber in the convex hull of the epigraph of `g`.
- `core/canonical`: the owner abstractions are the epigraph owner `epi` from Definition 4.1, the
  canonical set owner `Function.convexEpigraph g := _root_.convexHull 𝕜 (epi g)`, and
  `Function.verticalInfimum : Set (E × α) → E → WithTopBot α` from Theorem 5.3.
- Primitive data vs derived API: the function `g` and the canonical set owner
  `Function.convexEpigraph g` are primitive; the displayed infimum formula is the first companion
  specification.
- Ambient minimization: the convex-epigraph owner itself only uses convex-hull operations, so it
  lives at the weaker `PartialOrder` layer on `𝕜`; only the vertical-infimum formula for `conv(g)`
  needs conditional completeness on the codomain layer.

Domain-style sampling used here:
- `epi`;
- `Function.convexEpigraph`;
- `Function.verticalInfimum`;
- `_root_.convexHull`;
- `Function.verticalHeights`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`.
- Layer target: `source-facing`; the public definition remains Rockafellar's `conv(g)`, while the
  chapter owners `epi`, `Function.convexEpigraph`, and `Function.verticalInfimum` supply the
  canonical construction.
-/

section ConvexEpigraph

variable [AddCommMonoid α] [Module 𝕜 α] [LE α]
variable [PartialOrder 𝕜]

/-- Helper for Text 5.5.1: the canonical set owner for the convex hull of the epigraph of `g`. -/
def Function.convexEpigraph (g : E → WithTopBot α) : Set (E × α) :=
  _root_.convexHull 𝕜 (epi g)

-- Proof sketch: `Function.convexEpigraph g` is literally a convex hull, so the ambient
-- convexity theorem `convex_convexHull` applies immediately once the scalar owner is fixed.
/-- Helper for Text 5.5.1: the canonical set owner `Function.convexEpigraph g` is convex. -/
theorem Function.convex_convexEpigraph (g : E → WithTopBot α) :
    Convex 𝕜 (Function.convexEpigraph (𝕜 := 𝕜) g) := by
  simpa [Function.convexEpigraph] using
    (convex_convexHull 𝕜 (epi g))

end ConvexEpigraph

section ConvexHull

variable [AddCommMonoid α] [Module 𝕜 α]
variable [PartialOrder 𝕜] [ConditionallyCompleteLattice α]

/-- Text 5.5.1: the convex hull `conv(g)` of a function `g` is the function obtained by taking,
for each `x`, the infimum of the codomain heights in the convex hull of the epigraph of `g`. -/
def Function.convexHull (g : E → WithTopBot α) : E → WithTopBot α :=
  Function.verticalInfimum (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g)

/-- Helper for Text 5.5.1: Rockafellar notation for the function convex hull. -/
notation:max "conv(" g ")" => Function.convexHull g

-- Proof sketch: this is the canonical owner-level restatement of the definition, so `rfl`
-- closes the goal once the scalar parameter of `Function.convexEpigraph` is fixed.
/-- Helper for Text 5.5.1: in canonical-owner form, `conv(g)` is the vertical infimum of
`Function.convexEpigraph g`. -/
theorem Function.convexHull_eq_verticalInfimum_convexEpigraph
    (g : E → WithTopBot α) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g =
      Function.verticalInfimum (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) := by
  rfl

-- Proof sketch: rewrite the canonical owner `Function.convexEpigraph g` back to the raw set
-- expression `_root_.convexHull 𝕜 (epi g)` used in the textbook display formula.
/-- Helper for Text 5.5.1: bridge/view form with the raw set expression
`_root_.convexHull 𝕜 (epi g)`. -/
theorem Function.convexHull_eq_verticalInfimum_convexHull_epigraph
    (g : E → WithTopBot α) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g =
      Function.verticalInfimum (E := E) (α := α) (_root_.convexHull 𝕜 (epi g)) := by
  simpa [Function.convexEpigraph] using
    (Function.convexHull_eq_verticalInfimum_convexEpigraph
      (E := E) (𝕜 := 𝕜) (α := α) g)

-- Proof sketch: unfold `Function.convexHull` to `Function.verticalInfimum` of
-- `Function.convexEpigraph g`, then use `verticalInfimum_eq_sInf_verticalHeights`.
/-- Helper for Text 5.5.1: the value of `conv(g)` at `x` is the infimum of the intrinsic height owner
`Function.verticalHeights` above `x` for `Function.convexEpigraph g`. -/
theorem Function.convexHull_eq_sInf_verticalHeights
    (g : E → WithTopBot α) (x : E) :
    Function.convexHull (E := E) (𝕜 := 𝕜) (α := α) g x =
      sInf (Function.verticalHeights (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) x) := by
  simpa [Function.convexHull] using
    (Function.verticalInfimum_eq_sInf_verticalHeights
      (E := E) (α := α) (Function.convexEpigraph (𝕜 := 𝕜) g) x)

end ConvexHull

end
