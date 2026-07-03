import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_6_9 (from Chap02) -/
/- Short intrinsic-closure notation used in this item's theorem surfaces. -/
local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Text 6.9 records the immediate inclusion chain between the relative interior,
  the set itself, and its closure.
- `core/canonical`: the intrinsic owner chain is
  `intrinsicInterior_subset` and `subset_intrinsicClosure`.
- `bridge/view`: ambient closure is a downstream bridge from the intrinsic owner layer, with
  `subset_closure` retained as the textbook ambient companion.
- Primitive data vs derived API: this item introduces no data; it only recalls canonical facts
  about `intrinsicInterior`, `intrinsicClosure`, and `closure`.
- Domain-style sampling used here: `intrinsicInterior`, `intrinsicClosure`, `closure`,
  `intrinsicInterior_subset`, `subset_intrinsicClosure`, and `subset_closure`.
- Layer target: the main labeled entries are `core/canonical`.
-/

section

variable
    {𝕜 : Type*} [Ring 𝕜]
    {V : Type*} [AddCommGroup V] [Module 𝕜 V]
    {P : Type*} [TopologicalSpace P] [AddTorsor V P]

/- Text 6.9 (1): the relative interior inclusion `ri C ⊆ C` is exactly the canonical owner theorem
`intrinsicInterior_subset`. -/
recall intrinsicInterior_subset
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    ri[𝕜](C) ⊆ C

/- Text 6.9 (2), canonical relative-topology layer: the set inclusion into relative closure is the
canonical owner theorem `subset_intrinsicClosure`. -/
recall subset_intrinsicClosure
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    C ⊆ cl[𝕜](C)

/-- Canonical chain form of Text 6.9 at the intrinsic layer: relative interior is contained in
relative closure. -/
theorem ri_subset_intrinsicClosure
    (C : Set P) :
    ri[𝕜](C) ⊆ cl[𝕜](C) :=
  (intrinsicInterior_subset : ri[𝕜](C) ⊆ C).trans
    (subset_intrinsicClosure : C ⊆ cl[𝕜](C))

/- Bridge from the intrinsic closure layer to ambient closure. -/
recall intrinsicClosure_subset_closure
    {𝕜 : Type*} {V : Type*} {P : Type*}
    [Ring 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [TopologicalSpace P] [AddTorsor V P] {C : Set P} :
    cl[𝕜](C) ⊆ closure C

/- Text 6.9 bridge companion: chaining the intrinsic inclusion with
`intrinsicClosure_subset_closure` yields the textbook ambient inclusion `ri C ⊆ closure C`. -/
theorem ri_subset_closure (C : Set P) :
    ri[𝕜](C) ⊆ closure C :=
  (ri_subset_intrinsicClosure (𝕜 := 𝕜) C).trans
    (intrinsicClosure_subset_closure (𝕜 := 𝕜) (s := C))

/- Ambient-closure bridge for the textbook surface `C ⊆ cl C`. -/
recall subset_closure

end

/-! ### Theorem_6_9 (from Chap02) -/
open scoped Pointwise Rockafellar

section

variable
    {ι E 𝕜 : Type*}
    [Finite ι]
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.9 identifies the relative interior of the convex hull of finitely many
  nonempty convex subsets of a finite-dimensional normed space over `𝕜` with the union of all
  strictly positive convex combinations of their relative interiors.
- `core/canonical`: the owner notions are `convexHull 𝕜`, `intrinsicInterior 𝕜`, and the simplex
  owner sum `w.sum (fun i a ↦ a • S i)` with coefficients carried by `StdSimplex 𝕜 ι`.
- `bridge/view`: Rockafellar's `ri` is represented by `intrinsicInterior 𝕜`, while the source
  coefficient conditions `λᵢ > 0` and `∑ λᵢ = 1` are expressed directly by a coefficient function
  `w : StdSimplex 𝕜 ι` together with the extra strict-positivity condition `∀ i,
  0 < w.weights i`.
- Primitive data vs derived API: the primitive data are the family `C`, its convexity and
  nonemptiness hypotheses, and the simplex owner object `w : StdSimplex 𝕜 ι`; the strict
  positivity requirement and the displayed simplex-sum membership are derived conditions on
  that owner object, while the fixed-weight relative-interior formula is itself derived from the
  Chapter 6 owner API and is therefore kept only as a private bridge below rather than as a second
  public simplex-sum owner.
- Domain-style sampling used here: `StdSimplex`, the chapter theorem
  `Set.conv_iUnion_eq_iUnion_simplex_sum`, the section theorem
  `Convex.intrinsicInterior_add`, the scalar-dilation bridge `Convex.intrinsicInterior_smul`, and
  the homogenization bridge `Convex.intrinsicInterior_homogenizationCone_eq`.
- Layer target: this item remains source-facing as a direct set equality in the canonical
  `intrinsicInterior`/`convexHull`/positive-weight language.
- Ambient/index minimization: the statement uses only finite indexing and finite-dimensional
  relative-interior theory, not coordinates or ordered positions, so the public owner surface is
  stated for an arbitrary finite index type `ι` and an arbitrary finite-dimensional normed space `E`
  over `𝕜` rather than the concrete model `EuclideanSpace ℝ (Fin n)`.
-/

namespace Convex

/- For a fixed simplex weight family, relative interior commutes with the corresponding simplex
sum of convex sets. This is an internal bridge extracted from the Chapter 6 owner API
`Convex.intrinsicInterior_add` and `Convex.intrinsicInterior_smul`, so the source-facing theorem
below does not need to repeat finite simplex-sum bookkeeping at every simplex witness. -/
private theorem intrinsicInterior_simplex_sum
    (w : StdSimplex 𝕜 ι) (C : ι → Set E) (hconv : ∀ i, Convex 𝕜 (C i)) :
    ri[𝕜](w.sum (fun i a ↦ a • C i)) = w.sum (fun i a ↦ a • ri[𝕜](C i)) := sorry

/-- Theorem 6.9: for a finite family of nonempty convex sets in a finite-dimensional normed space
over `𝕜`, the relative interior `ri` of the convex hull of their union is exactly the set of
points lying in a convex combination of the relative interiors with strictly positive simplex
coefficients. Specializing to `𝕜 = ℝ` and `E = EuclideanSpace ℝ (Fin n)` recovers the textbook
`R^n` statement. -/
-- Proof sketch: pass to the homogenization cones in `𝕜 × E`, where Corollary 6.8.1 rewrites the
-- relative interior of each cone as the positive rays over `ri (C i)`. The
-- simplex-weighted convex-hull description from Theorem 3.3 organizes the unit-height slice of
-- the homogenized convex hull. The fixed-weight slices are normalized by the private bridge
-- `intrinsicInterior_simplex_sum`, extracted from
-- `Convex.intrinsicInterior_add` and `Convex.intrinsicInterior_smul`, so the finite Minkowski-sum
-- part of the argument is handled at the owner level rather than by ad hoc coordinate
-- bookkeeping. Reading off the first coordinate then gives a simplex weight vector
-- `w : StdSimplex 𝕜 ι` with strictly positive coordinates, and the second coordinate is exactly
-- the required simplex sum of points in the relative interiors.
theorem intrinsicInterior_convexHull_iUnion_eq_positive_simplex_sum
    (C : ι → Set E) (hconv : ∀ i, Convex 𝕜 (C i)) (hnonempty : ∀ i, (C i).Nonempty) :
    ri[𝕜](convexHull 𝕜 (⋃ i, C i)) =
      {x : E |
        ∃ w : StdSimplex 𝕜 ι,
          (∀ i, 0 < w.weights i) ∧ x ∈ w.sum (fun i a ↦ a • ri[𝕜](C i))} := sorry

end Convex

end
