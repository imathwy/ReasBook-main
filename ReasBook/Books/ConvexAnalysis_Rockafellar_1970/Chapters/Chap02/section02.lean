import Mathlib
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_2_2 (from Chap01) -/
/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.2 says that a subset of a module is convex exactly when it contains
  every finite convex combination of its elements; the textbook `ℝ^n` statement is the
  specialization `R = ℝ`.
- `core/canonical`: the owner abstraction is `Convex R s`; the owner-facing finite-combination
  closure theorem is `Convex.sum_mem`, and the corresponding characterization theorem is
  `convex_iff_sum_mem`.
- `bridge/view`: finite convex combinations are also naturally represented by the simplex owner
  `StdSimplex`; the source-facing bridge is a simplex-sum closure theorem together with an iff
  characterization at that owner layer.
- Primitive data vs derived API: `Convex` is the primitive owner notion; closure under finite
  convex combinations is its canonical derived characterization.
- Domain-style sampling: this refinement is guided by `Convex`, `Convex.sum_mem`,
  `convex_iff_sum_mem`, and the chapter-local finite-convex-combination recall file
  `Definition_2_2_10`.
- Layer target: `core/canonical` with a source-facing simplex-owner bridge; the canonical recalls
  stay primary, and nearby theorem surfaces are stated on `StdSimplex` where finite combinations
  are the mathematical object.
-/

/- Owner-facing forward closure under finite convex combinations. -/
recall Convex.sum_mem

/- Theorem 2.2: a subset is convex iff it contains every finite convex combination of its
elements; this is the canonical characterization theorem `convex_iff_sum_mem`. -/
recall convex_iff_sum_mem

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Convex

/-- Converse simplex-sum bridge on the weakest scalar layer needed for the duple argument:
if a set contains every simplex weighted sum supported in it, then it is convex. -/
theorem of_stdSimplex_sum_mem {s : Set E}
    (h : ∀ {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E),
      (∀ i ∈ w.support, z i ∈ s) → w.sum (fun i r ↦ r • z i) ∈ s) :
    Convex 𝕜 s := by
  intro x hx y hy a b ha hb hab
  let w : StdSimplex 𝕜 (ULift (Fin 2)) :=
    StdSimplex.duple (ULift.up 0) (ULift.up 1) ha hb hab
  let z : ULift (Fin 2) → E := fun i ↦ if i.down = 0 then x else y
  have hz : ∀ i ∈ w.support, z i ∈ s := by
    intro i hi
    rcases i with ⟨i⟩
    fin_cases i <;> simp [z, hx, hy]
  have hw : w.sum (fun i r ↦ r • z i) ∈ s := h w z hz
  have hsum : w.sum (fun i r ↦ r • z i) = a • x + b • y := by
    simp [w, z, StdSimplex.duple, Finsupp.sum_add_index, add_smul]
  simpa [hsum] using hw

end Convex

end

section

variable {𝕜 E : Type*}
variable [Ring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace Convex

/-- Converse simplex-owner bridge on the weakest layer where the `convexCombination`/sum bridge is
available: if a set contains every mapped simplex convex combination supported in it, then it is
convex. -/
theorem of_stdSimplex_convexCombination_mem {s : Set E}
    (h : ∀ {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E),
      (∀ i ∈ w.support, z i ∈ s) → (w.map z).convexCombination ∈ s) :
    Convex 𝕜 s := by
  refine Convex.of_stdSimplex_sum_mem ?_
  intro ι w z hz
  have hmem : (w.map z).convexCombination ∈ s := h w z hz
  simpa using hmem

end Convex

end

section

variable {𝕜 E : Type*}
variable [LinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace Convex

/-- Source-facing simplex-sum bridge: a convex set contains every simplex weighted sum of points
in that set. -/
theorem stdSimplex_sum_mem {s : Set E} (hs : Convex 𝕜 s)
    {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E)
    (hz : ∀ i ∈ w.support, z i ∈ s) :
    w.sum (fun i r ↦ r • z i) ∈ s := by
  simpa [Finsupp.sum] using
    hs.sum_mem (t := w.weights.support) (w := fun i ↦ w.weights i) (z := z)
      (fun i hi ↦ by simpa using w.nonneg i)
      (by simpa [Finsupp.sum] using w.total)
      hz

end Convex

/-- Theorem 2.2 on the simplex weighted-sum bridge layer:
a set is convex iff it is closed under all finite simplex weighted sums of its points. -/
theorem convex_iff_stdSimplex_sum_mem {s : Set E} :
    Convex 𝕜 s ↔
      ∀ {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E),
        (∀ i ∈ w.support, z i ∈ s) → w.sum (fun i r ↦ r • z i) ∈ s := by
  constructor
  · intro hs ι w z hz
    exact hs.stdSimplex_sum_mem w z hz
  · intro h
    exact Convex.of_stdSimplex_sum_mem h

end

section

variable {𝕜 E : Type*}
variable [LinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace Convex

/-- Owner-facing intrinsic simplex form of finite-combination closure:
a convex set contains the mapped convex combination carried by any simplex whose support maps
into the set. -/
theorem stdSimplex_convexCombination_mem {s : Set E} (hs : Convex 𝕜 s)
    {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E)
    (hz : ∀ i ∈ w.support, z i ∈ s) :
    (w.map z).convexCombination ∈ s := by
  have hsum_mem : w.sum (fun i r ↦ r • z i) ∈ s := hs.stdSimplex_sum_mem w z hz
  simpa using hsum_mem

end Convex

/-- Theorem 2.2 on the intrinsic simplex owner layer:
a set is convex iff it contains every mapped simplex convex combination supported in the set. -/
theorem convex_iff_stdSimplex_convexCombination_mem {s : Set E} :
    Convex 𝕜 s ↔
      ∀ {ι : Type*} (w : StdSimplex 𝕜 ι) (z : ι → E),
        (∀ i ∈ w.support, z i ∈ s) →
          (w.map z).convexCombination ∈ s := by
  constructor
  · intro hs ι w z hz
    exact hs.stdSimplex_convexCombination_mem w z hz
  · intro h
    exact Convex.of_stdSimplex_convexCombination_mem h

end

/-! ### Definition_2_2_10 (from Chap01) -/
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
recall StdSimplex

/- The corresponding point determined by simplex coefficients is the canonical convex-space
combination `ConvexSpace.convexCombination`. -/
recall ConvexSpace.convexCombination

/- In an ordered-ring module, `ConvexSpace.convexCombination` for simplex coefficients is exactly
the textbook weighted sum `∑ i, w i • x i`. -/
recall convexCombination_eq_sum

/- For a fixed finite index set, the same weighted sum is the corresponding center of mass once
the coefficients sum to `1`. -/
recall Finset.centerMass_eq_of_sum_1

namespace StdSimplex

variable {𝕜 ι E : Type*}

/-- Object-prefix owner surface for simplex convex combinations. -/
def convexCombination [Semiring 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [ConvexSpace 𝕜 E] (w : StdSimplex 𝕜 E) : E :=
  ConvexSpace.convexCombination w

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

/-- In the module specialization, the canonical owner `ConvexSpace.convexCombination` recovers the
textbook weighted-sum formula. -/
@[simp] theorem convexCombination_eq_sum (w : StdSimplex 𝕜 E) :
    w.convexCombination = w.sum (fun x r ↦ r • x) := by
  simpa [StdSimplex.convexCombination] using (_root_.convexCombination_eq_sum (f := w))

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

end StdSimplex
