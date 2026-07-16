import Mathlib
import Mathlib.Tactic.Recall

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

/- 
Source/core/bridge triage:
- `source-facing`: Definition 2.2.10 introduces finite convex combinations of vectors, i.e. finite
  weighted sums with nonnegative coefficients summing to `1`.
- `core/canonical`: mathlib's owner abstraction for those coefficients is `StdSimplex R ι`; the
  corresponding point operation is `ConvexSpace.convexCombination`.
- `bridge/view`: `convexCombination_eq_sum` recovers the textbook weighted-sum formula from
  `ConvexSpace.convexCombination`, while `Finset.centerMass_eq_of_sum_1` is the finite-index-set
  bridge to the chapter's explicit `Finset`-sum presentation.
- Primitive data vs derived API: nonnegativity and total mass `1` belong to `StdSimplex`; the
  explicit sum and center-of-mass formulas are derived API and should be recalled directly rather
  than repackaged as a parallel local predicate.
- Domain-style sampling: this item aligns with `StdSimplex`,
  `ConvexSpace.convexCombination`, `convexCombination_eq_sum`, and
  `Finset.centerMass_eq_of_sum_1`.
-/

/- Definition 2.2.10: the canonical owner object for a finite convex combination is
`StdSimplex R ι`. -/
recall Convexity.StdSimplex

/- The corresponding point determined by simplex coefficients is the canonical convex-space
combination `ConvexSpace.convexCombination`. -/
recall Convexity.ConvexSpace.sConvexComb

/- In an ordered-ring module, `ConvexSpace.convexCombination` for simplex coefficients is exactly
the textbook weighted sum `∑ i, w i • x i`. -/
recall Convexity.IsModuleConvexSpace.sConvexComb_eq_sum

/- For a fixed finite index set, the same weighted sum is the corresponding center of mass once
the coefficients sum to `1`. -/
recall Finset.centerMass_eq_of_sum_1

namespace Convexity.StdSimplex

variable {𝕜 ι E : Type*}

/-- Compatibility name for the support-indexed sum used by the pre-4.30 simplex API. -/
def sum {β : Type*} [LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜] [AddCommMonoid β]
    (w : StdSimplex 𝕜 ι) (f : ι → 𝕜 → β) : β :=
  w.weights.sum f

/-- Compatibility projection for the finite support of simplex weights. -/
abbrev support [LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜] (w : StdSimplex 𝕜 ι) : Finset ι :=
  w.weights.support

/-- Compatibility projection removing the `⊤` coordinate from simplex weights. -/
noncomputable def some {M : Type*} [LE 𝕜] [AddCommMonoid 𝕜] [One 𝕜]
    (w : StdSimplex 𝕜 (WithTop M)) : M →₀ 𝕜 :=
  w.weights.some

/-- Object-prefix owner surface for simplex convex combinations. -/
def convexCombination [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [ConvexSpace 𝕜 E] (w : StdSimplex 𝕜 E) : E :=
  ConvexSpace.sConvexComb w

section

variable [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Bridge for mapped simplex coefficients: pushing coefficients along `z` and summing in `E`
is the same as summing `z` against the original coefficients. -/
@[simp] theorem map_sum_smul_eq_sum (w : StdSimplex 𝕜 ι) (z : ι → E) :
    (w.map z).sum (fun y r ↦ r • y) = w.sum (fun i r ↦ r • z i) := by
  simpa [StdSimplex.map] using
    (Finsupp.sum_mapDomain_index (f := z) (s := w.weights)
      (h := fun y r ↦ r • y)
      (h_zero := fun _ ↦ zero_smul 𝕜 _)
      (h_add := fun _ _ _ ↦ add_smul _ _ _))

end

section

variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

local instance moduleConvexSpace : ConvexSpace 𝕜 E := ConvexSpace.ofModule
local instance moduleIsModuleConvexSpace : IsModuleConvexSpace 𝕜 E :=
  IsModuleConvexSpace.ofModule

/-- In the module specialization, the canonical owner `ConvexSpace.convexCombination` recovers the
textbook weighted-sum formula. -/
@[simp] theorem convexCombination_eq_sum (w : StdSimplex 𝕜 E) :
    w.convexCombination = w.sum (fun x r ↦ r • x) := by
  simpa only [StdSimplex.convexCombination, StdSimplex.sum] using
    (Convexity.IsModuleConvexSpace.sConvexComb_eq_sum (w := w))

/-- Source-facing mapped-family bridge:
for simplex coefficients on an index type `ι`, convex-combining the pushed-forward simplex over
`E` matches the textbook weighted sum `∑ i, w i • z i`. -/
@[simp] theorem map_convexCombination_eq_sum (w : StdSimplex 𝕜 ι) (z : ι → E) :
    (w.map z).convexCombination = w.sum (fun i r ↦ r • z i) := by
  calc
    (w.map z).convexCombination = (w.map z).sum (fun y r ↦ r • y) := by
      exact StdSimplex.convexCombination_eq_sum (w := w.map z)
    _ = w.sum (fun i r ↦ r • z i) := StdSimplex.map_sum_smul_eq_sum (w := w) (z := z)

end

end Convexity.StdSimplex
