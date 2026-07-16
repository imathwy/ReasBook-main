import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

open scoped Rockafellar

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace Y] [Sub (WithTopBot 𝕜)] [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 12.2 records the basic duality properties of the conjugate of a convex
  function on `R^n`: closedness, convexity, properness equivalence, invariance under closure, and
  biconjugacy.
- `core/canonical`: the owner declarations already present in the project are
  `convexConjugate`, its scoped notation `f⋆`, `Function.IsConvex`, `Function.IsProper`, and
  `lowerSemicontinuousHull` with its scoped notation `cl(f)`, with
  `ConvexOn 𝕜 Set.univ` as the canonical convexity owner surface and
  `Function.IsConvex` retained as a bridge for downstream compatibility.
- `bridge/view`: Rockafellar's closure notation `cl(f)` is rendered by the project owner
  `lowerSemicontinuousHull f`, and the biconjugate `f**` is rendered by the owner notation `f⋆⋆`.

Domain-style sampling used here:
- the chapter owner `convexConjugate` from `Defn_12_2`;
- the chapter owner predicates `Function.IsConvex` and `Function.IsProper`;
- the chapter owner theorem `Function.IsConvex.iSup` for pointwise suprema from Theorem 5.5;
- the chapter owner theorem `Function.isConvex_supportFunction` from `Text_5_5_0`, which fixes the
  correct linear-pairing abstraction layer for dual-variable convexity statements;
- the project owner `lowerSemicontinuousHull` from `Text_7_0_4`;
- mathlib's canonical predicate `LowerSemicontinuous`.

Primitive data vs derived API:
- the primitive inputs for clauses `(1)` and `(4)` are a pairing
  `HasPairing X Y 𝕜`, the primal function `f : X → WithTopBot 𝕜`, and only the extra
  topological structure used by the corresponding owner theorem;
- the primitive input for clause `(2)` is the same primal function together with the canonical
  linear-pairing owner `HasLinearPairing X Y 𝕜`, since convexity in the dual variable uses the
  linearity of each slice `y ↦ ⟪x, y⟫ₚ`, and the codomain-general owner form now lives on
  `WithTopBot 𝕜`;
- the primitive input for clauses `(3)` and `(5)` is a function
  `f : E → WithTopBot 𝕜`, together with the source hypothesis
  `ConvexOn 𝕜 Set.univ f` plus a finite-dimensional scalar-field ambient carrying a continuous
  linear self-pairing;
- the derived API consists of the closedness, convexity, properness, closure-invariance, and
  biconjugacy statements for `f⋆`, with clauses `(1)` and `(4)` stated at the paired-space
  topological layer needed for lower semicontinuity of pairing slices, clause `(2)` stated at the
  canonical linear-pairing layer (including the codomain-general `WithTopBot 𝕜` owner form) needed
  for convexity via `ConvexOn 𝕜 Set.univ`, and clauses `(3)` and `(5)` stated on finite-dimensional
  scalar-field spaces through the pairing owner instead of an inner-product-space owner.

Layer target: `source-facing`; the theorem is stated directly in terms of the project owner
declarations rather than through an auxiliary package. The source's `R^n` wording is rendered on
the stronger reusable owner ambient of paired spaces for clauses `(1)` and `(4)`, on the
canonical linear-pairing owner for clause `(2)`, and on finite-dimensional scalar-field spaces with
continuous linear self-pairing for clauses `(3)` and `(5)`, so the file avoids a separate
Euclidean-model wrapper.
-/

-- Proof sketch: view `f⋆` as the pointwise supremum of the affine functions
-- `y ↦ ⟪y, x⟫ - f x`. Each such affine function is lower semicontinuous, and lower semicontinuity
-- is preserved under arbitrary pointwise suprema.
/-- Theorem 12.2 (1): the conjugate `f⋆` of any extended-codomain-valued function is closed,
expressed here as lower semicontinuity. The Euclidean source statement is lifted to the canonical
paired-space owner layer by assuming only lower semicontinuity of the pairing slices on the dual
side. -/
theorem lowerSemicontinuous_convexConjugate_of_pairingSlices
    (f : X → WithTopBot 𝕜)
    (hpair : ∀ x : X, LowerSemicontinuous (fun y : Y ↦ ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜))) :
    LowerSemicontinuous (f⋆ : Y → WithTopBot 𝕜) := sorry

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedAddMonoid 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

-- Proof sketch: rewrite `f⋆` as the pointwise supremum of the affine functions
-- `y ↦ ⟪x, y⟫ - f x`. The linear-pairing owner `HasLinearPairing X Y 𝕜` provides the linearity of
-- each dual-variable slice `y ↦ ⟪x, y⟫ₚ`, so each summand is convex and the supremum is convex.
/-- Theorem 12.2 (2), canonical owner form: the conjugate `f⋆` of any
`WithTopBot 𝕜`-valued function is convex on `Set.univ`. The canonical owner layer here is a linear
pairing, not a raw pairing, because convexity in the dual variable uses the linearity of the
pairing slices. -/
theorem Function.convexOn_univ_convexConjugate
    (f : X → WithTopBot 𝕜) :
    ConvexOn 𝕜 (Set.univ : Set Y) (f⋆ : Y → WithTopBot 𝕜) := sorry

/-- Bridge form of Theorem 12.2 (2) through the chapter owner alias `Function.IsConvex`. -/
theorem Function.isConvex_convexConjugate
    (f : X → WithTopBot 𝕜) :
    (f⋆ : Y → WithTopBot 𝕜).IsConvex 𝕜 := by
  rw [Function.isConvex_iff_convex_epigraph]
  simpa [convexOn_iff_convex_epigraph, Set.mem_univ] using
    (Function.convexOn_univ_convexConjugate (f := f))

end

section

variable {X : Type u} {Y : Type v} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable [TopologicalSpace X] [Sub (WithTopBot 𝕜)] [HasPairing X Y 𝕜]

-- Proof sketch: `cl(f) ≤ f`, so monotonicity of conjugation gives one
-- inequality. For the reverse inequality, every affine minorant of `f` is lower semicontinuous,
-- hence also a minorant of `cl(f)`; taking the supremum over affine minorants
-- yields equality of conjugates.
/-- Theorem 12.2 (4): taking the conjugate commutes with Rockafellar's closure `cl(f)`. The
Euclidean source statement is lifted to the canonical paired-space owner layer by assuming only
lower semicontinuity of the primal pairing slices. -/
theorem convexConjugate_lowerSemicontinuousHull_eq_of_pairingSlices
    (f : X → WithTopBot 𝕜)
    (hpair : ∀ y : Y, LowerSemicontinuous (fun x : X ↦ ((⟪x, y⟫ₚ : 𝕜) : WithTopBot 𝕜))) :
    (cl(f)⋆ : Y → WithTopBot 𝕜) = (f⋆ : Y → WithTopBot 𝕜) := sorry

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [TopologicalSpace E]
variable [Sub (WithTopBot 𝕜)] [HasPairingSwap E E 𝕜] [HasContinuousPairing E E 𝕜]

/-- Continuity-and-symmetry bridge for Theorem 12.2 (1): on a self-paired space, continuity in
the first variable and pairing symmetry provide lower semicontinuity of the dual-variable slices,
hence lower semicontinuity of the conjugate. -/
private theorem lowerSemicontinuous_convexConjugate_of_continuousPairingSwap
    (f : E → WithTopBot 𝕜) :
    LowerSemicontinuous (f⋆ : E → WithTopBot 𝕜) := sorry

/-- Theorem 12.2 (1), self-pairing canonical owner form: on a self-paired space with pairing
continuity and swap compatibility, the conjugate is lower semicontinuous. -/
theorem lowerSemicontinuous_convexConjugate
    (f : E → WithTopBot 𝕜) :
    LowerSemicontinuous (f⋆ : E → WithTopBot 𝕜) := by
  simpa using lowerSemicontinuous_convexConjugate_of_continuousPairingSwap (f := f)

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace E] [Sub (WithTopBot 𝕜)] [HasContinuousPairing E E 𝕜]

/-- Continuity-layer bridge for Theorem 12.2 (4). -/
theorem convexConjugate_lowerSemicontinuousHull_eq
    (f : E → WithTopBot 𝕜) :
    (cl(f)⋆ : E → WithTopBot 𝕜) = (f⋆ : E → WithTopBot 𝕜) := sorry

end

section

variable {E : Type u} {𝕜 : Type w}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]

namespace Function

-- Proof sketch: if `f` is proper and convex, the supporting-affine-minorant theorem gives a finite
-- affine minorant, which yields a finite point of `f⋆`; the definition of the
-- conjugate rules out the value `-∞`. Conversely, if `f⋆` is proper, apply the same
-- argument to `f⋆`, use biconjugacy below, and read properness back through `cl(f)`.
/-- Theorem 12.2 (3), canonical owner form: for a convex function on `Set.univ` in a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, the conjugate
`f⋆` is proper if and only if `f` is proper. -/
theorem convexConjugate_isProper_iff_of_convexOn_univ
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    (f⋆ : E → WithTopBot 𝕜).IsProper ↔ f.IsProper := sorry

-- Proof sketch: apply closure-invariance to replace `cl(f)⋆` by `f⋆`, then use the
-- closed-case biconjugacy statement on `cl(f)`.
/-- Theorem 12.2 (5), canonical owner form: for a convex function on `Set.univ` in a
finite-dimensional scalar-field space equipped with a continuous linear self-pairing, the
biconjugate `f⋆⋆` equals the closure `cl(f)`. -/
theorem biconjugate_eq_lowerSemicontinuousHull_of_convexOn_univ
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    f⋆⋆ = cl(f) := sorry

end Function

namespace Function.IsConvex

private theorem convexOn_univ {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    ConvexOn 𝕜 (Set.univ : Set E) f := by
  rw [convexOn_iff_convex_epigraph]
  simpa [Function.isConvex_iff_convex_epigraph, Set.mem_univ] using hf

-- Proof sketch: if `f` is proper and convex, the supporting-affine-minorant theorem gives a finite
-- affine minorant, which yields a finite point of `f⋆`; the definition of the
-- conjugate rules out the value `-∞`. Conversely, if `f⋆` is proper, apply the same
-- argument to `f⋆`, use the biconjugacy theorem below, and read properness back
-- through `cl(f)`.
/-- Theorem 12.2 (3): for a convex function on a finite-dimensional scalar field space equipped
with a continuous linear self-pairing, the
conjugate `f⋆` is proper if and only if `f` is proper. -/
theorem convexConjugate_isProper_iff
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    (f⋆ : E → WithTopBot 𝕜).IsProper ↔ f.IsProper := by
  exact Function.convexConjugate_isProper_iff_of_convexOn_univ
    (hf := hf.convexOn_univ)

-- Proof sketch: apply the preceding closure-invariance theorem to replace
-- `cl(f)⋆` by `f⋆`. Then apply the closed-case biconjugacy statement to the closed convex function
-- `cl(f)`.
/-- Theorem 12.2 (5): for a convex function on a finite-dimensional scalar field space equipped
with a continuous linear self-pairing, the
biconjugate `f⋆⋆` equals the closure `cl(f)`. -/
theorem biconjugate_eq_lowerSemicontinuousHull
    {f : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) :
    f⋆⋆ = cl(f) := by
  exact Function.biconjugate_eq_lowerSemicontinuousHull_of_convexOn_univ
    (hf := hf.convexOn_univ)

end Function.IsConvex

end
