import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_0_2

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped BigOperators
open scoped Rockafellar

universe u v

variable {R : Type u} {E : Type v}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]

local instance : ConvexSpace R E := ConvexSpace.ofModule
local instance : IsModuleConvexSpace R E := IsModuleConvexSpace.ofModule

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 17.0.3 says that every point of `conv[R] S` can be written as a
  convex combination of points of `S`, with support size at most
  `finrank R (vectorSpan R S) + 1` when `vectorSpan R S` is finite-dimensional.
- `core/canonical`: mathlib's owner theorem
  `eq_pos_convex_span_of_mem_convexHull` already gives a finite affinely independent family in `S`
  with strictly positive convex weights summing to `1`.
- `bridge/view`: the coefficient owner is `StdSimplex R ι`; source-membership is tracked on the
  direct set/function surface by `z : ι → E` together with `Set.range z ⊆ S`.
  `AffineIndependent.card_le_finrank_succ` then bounds the witness cardinality by
  `finrank R (vectorSpan R (Set.range z)) + 1`, and `Submodule.finrank_mono` pushes this bound to
  `finrank R (vectorSpan R S) + 1`.
- Domain-style sampling used here: `StdSimplex`,
  `eq_pos_convex_span_of_mem_convexHull`, and `AffineIndependent.card_le_finrank_succ`.
- Primitive data vs derived API: the primitive coefficient datum is `w : StdSimplex R ι` together
  with point data `z : ι → E` and the source-membership certificate `Set.range z ⊆ S`;
  coefficient nonnegativity and total mass `1` are owner fields of
  `w`, while the weighted-sum display is derived from
  `StdSimplex.map_convexCombination_eq_sum`.
- Layer target: `source-facing`, using chapter notation `conv[R]` and the direct set/function
  surface (`z : ι → E`, `Set.range z ⊆ S`) rather than subtype coercion-heavy output.
- Canonicalization checks (explicit closure):
  1. Codomain concreteness: not applicable; this item is point-valued (`x : E`) and does not use
     an extended scalar codomain owner.
  2. Scalar/ambient minimality: in this Lean/mathlib snapshot, the canonical primitive owner
     layer for ordered-field convexity is the split trio
     `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`. The source-facing theorem matches this
     owner-level minimal interface (no extra ambient hypotheses).
  3. Intrinsic-owner choice: statement uses intrinsic `conv[R] S` and `vectorSpan R S`, not a
     concrete coordinate model.
  4. Topology-language applicability: not applicable; no ambient/interior/closure owner appears.
-/

/-- Theorem 17.0.3: over an ordered field `R`, every point of the convex hull of `S` can be
written as a convex combination of points of `S`, with at most
`Module.finrank R (vectorSpan R S) + 1` points when `vectorSpan R S` is finite-dimensional. -/
theorem exists_convex_combination_card_le_of_mem_conv {S : Set E}
    [FiniteDimensional R (vectorSpan R S)] {x : E}
    (hx : x ∈ conv[R] S) :
    ∃ ι : Type v, ∃ _ : Fintype ι, ∃ w : StdSimplex R ι, ∃ z : ι → E,
      Set.range z ⊆ S ∧
      (w.map z).convexCombination = x ∧
      Fintype.card ι ≤ Module.finrank R (vectorSpan R S) + 1 := by
  classical
  have hx' : x ∈ convexHull R S := by
    simpa using hx
  obtain ⟨ι, _, z, w, hzS, hAff, hwpos, hsum, hcomb⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx'
  let simplex : StdSimplex R ι :=
    { weights := Finsupp.equivFunOnFinite.symm w
      nonneg := fun i ↦ (hwpos i).le
      total := by
        rw [Finsupp.equivFunOnFinite_symm_sum]
        exact hsum }
  have hzSpan : vectorSpan R (Set.range z) ≤ vectorSpan R S :=
    vectorSpan_mono (k := R) hzS
  have hcard_ι : Fintype.card ι ≤ Module.finrank R (vectorSpan R S) + 1 := by
    calc
      Fintype.card ι ≤ Module.finrank R (vectorSpan R (Set.range z)) + 1 :=
        hAff.card_le_finrank_succ
      _ ≤ Module.finrank R (vectorSpan R S) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_mono hzSpan) 1
  refine ⟨ι, inferInstance, simplex, z, hzS, ?_, hcard_ι⟩
  have hsimp (i : ι) : simplex.weights i = w i := by
    simp [simplex]
  have hx_sum : x = ∑ i, simplex.weights i • z i := by
    calc
      x = ∑ i, w i • z i := hcomb.symm
      _ = ∑ i, simplex.weights i • z i := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hsimp]
  have hx_simplex : (simplex.map z).convexCombination = x := by
    calc
      (simplex.map z).convexCombination = simplex.sum (fun i r ↦ r • z i) := by
        exact StdSimplex.map_convexCombination_eq_sum (w := simplex) (z := z)
      _ = ∑ i, simplex.weights i • z i := by
        simpa using
          (Finsupp.sum_fintype (f := simplex.weights) (g := fun i r ↦ r • z i)
            (h := fun _ ↦ by simp))
      _ = x := hx_sum.symm
  exact hx_simplex

end
