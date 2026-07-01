import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_3_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Theorem 2.3 says that the convex hull of `S` is exactly the set of all
  finite convex combinations of points of `S`.
- `core/canonical`: mathlib's owner theorem is `mem_convexHull_iff_exists_fintype`, which
  characterizes membership in `convexHull R S` by a finitely supported weighted sum with
  nonnegative coefficients summing to `1`. For finite supports, the canonical owner theorem is
  `Finset.mem_convexHull`, using `Finset.centerMass`.
- `core/owner`: simplex coefficients are intrinsically owned by `StdSimplex R ι`, where
  nonnegativity and total-mass constraints are fields instead of separate hypotheses.
- `bridge/view`: `Finset.mem_convexHull'` is the equivalent finite-support weighted-sum view,
  matching the textbook display formula directly.
- Primitive data vs derived API: the canonical object is `convexHull`; the convex-combination
  presentation is its standard membership theorem and should be recalled directly rather than
  restated through a parallel owner. The chapter surface still benefits from a short notation-first
  bridge using `conv[𝕜]`.
- Domain-style sampling: this item grows from the earlier chapter recall `convexHull` from
  `Definition_2_3_10`, together with the owner theorem
  `mem_convexHull_iff_exists_fintype`, its finite-support companion `Finset.mem_convexHull'`, and
  the minimality view `convexHull_eq_iInter`.
- Layer target: `core/canonical`, with source-facing theorem surfaces written in the chapter's
  `conv[𝕜]` notation and short local bridge names while reusing the same canonical owners.

Abstraction checks for this item:
- Codomain/ambient layer: this item is set-valued (`Set E`) and does not involve extended codomain
  owners (`EReal`, `WithBotTop`), so no codomain lift applies here.
- Scalar structure: the canonical owner theorem used here is
  `mem_convexHull_iff_exists_fintype`, whose current upstream layer is
  `[Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]`; this file keeps exactly that layer.
- Owner choice: upgrade the source-facing core membership theorem to `StdSimplex` owner form, then
  keep the explicit weighted-sum theorem as a bridge view.
- Topology language: not applicable for this item.
- Owner naming/notation: keep the short chapter notation `conv[𝕜]` and use short theorem names in
  `Set`/`Finset` namespaces.
-/

/- Theorem 2.3: a point belongs to the convex hull of `S` exactly when it is a finite convex
combination of points of `S`; this is the canonical theorem
`mem_convexHull_iff_exists_fintype`. -/
recall mem_convexHull_iff_exists_fintype

/- Finite-support membership is canonically packaged by `Finset.mem_convexHull`. -/
recall Finset.mem_convexHull

/- The equivalent explicit weighted-sum formulation is `Finset.mem_convexHull'`. -/
recall Finset.mem_convexHull'

section

variable {𝕜 : Type*} {E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]

namespace Set

/- The owner-level simplex form of Theorem 2.3. -/
theorem mem_conv_iff_exists_stdSimplex {s : Set E} {x : E} :
    x ∈ (conv[𝕜] s) ↔
      ∃ w : StdSimplex 𝕜 s,
        (w.map Subtype.val).convexCombination = x := by
  constructor
  · intro hx
    rcases (mem_convexHull_iff_exists_fintype (R := 𝕜) (s := s) (x := x)).1 hx with
      ⟨ι, _, w, z, hw₀, hw₁, hz, hxsum⟩
    let simplex : StdSimplex 𝕜 ι :=
      { weights := Finsupp.equivFunOnFinite.symm w
        nonneg := by
          intro i
          simpa using hw₀ i
        total := by
          simpa [Finsupp.sum_fintype] using hw₁ }
    refine ⟨simplex.map (fun i ↦ ⟨z i, hz i⟩), ?_⟩
    have hxcomb : (simplex.map (fun i ↦ z i)).convexCombination = x := by
      calc
        (simplex.map (fun i ↦ z i)).convexCombination =
            simplex.sum (fun i r ↦ r • z i) := by
          exact StdSimplex.map_convexCombination_eq_sum (w := simplex) (z := z)
        _ = x := by
          simpa [simplex, Finsupp.sum_fintype] using hxsum
    simpa [StdSimplex.map_map] using hxcomb
  · rintro ⟨w, hxcomb⟩
    let κ := { i // i ∈ w.weights.support }
    have hxsum : w.sum (fun i r ↦ r • (i : E)) = x := by
      calc
        w.sum (fun i r ↦ r • (i : E)) = (w.map Subtype.val).convexCombination := by
          exact
            (StdSimplex.map_convexCombination_eq_sum (w := w) (z := Subtype.val)).symm
        _ = x := hxcomb
    have hw₁ : ∑ i : κ, w.weights i.1 = 1 := by
      have hsub :
          (∑ i : κ, w.weights i.1) = ∑ i ∈ w.weights.support, w.weights i := by
        symm
        refine Finset.sum_subtype (s := w.weights.support) (f := fun i : s ↦ w.weights i) ?_
        intro i
        simp
      calc
        (∑ i : κ, w.weights i.1) = ∑ i ∈ w.weights.support, w.weights i := hsub
        _ = 1 := by
          simpa [Finsupp.sum] using w.total
    have hxκ : ∑ i : κ, w.weights i.1 • ((i.1 : s) : E) = x := by
      have hsub :
          (∑ i : κ, w.weights i.1 • ((i.1 : s) : E)) =
            ∑ i ∈ w.weights.support, w.weights i • (i : E) := by
        symm
        refine Finset.sum_subtype (s := w.weights.support)
          (f := fun i : s ↦ w.weights i • (i : E)) ?_
        intro i
        simp
      calc
        (∑ i : κ, w.weights i.1 • ((i.1 : s) : E)) =
            ∑ i ∈ w.weights.support, w.weights i • (i : E) := hsub
        _ = x := by
          simpa [Finsupp.sum] using hxsum
    exact mem_convexHull_of_exists_fintype
      (s := s)
      (w := fun i : κ ↦ w.weights i.1)
      (z := fun i : κ ↦ (i.1 : E))
      (fun i ↦ w.nonneg i.1) hw₁ (fun i ↦ i.1.2) hxκ

/-- Theorem 2.3 on the chapter surface: membership in `conv[𝕜] s` is equivalent to the existence
of a finite convex-combination representation. This is the weighted-sum bridge view of
`Set.mem_conv_iff_exists_stdSimplex`. -/
theorem mem_conv_iff_exists_fintype {s : Set E} {x : E} :
    x ∈ (conv[𝕜] s) ↔
      ∃ (ι : Type) (_ : Fintype ι) (w : ι → 𝕜) (z : ι → E),
        (∀ i, 0 ≤ w i) ∧
        ∑ i, w i = 1 ∧
        (∀ i, z i ∈ s) ∧
        ∑ i, w i • z i = x := by
  simpa using (mem_convexHull_iff_exists_fintype (R := 𝕜) (s := s) (x := x))

end Set

namespace Finset

/-- Finite-support owner-level simplex form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_stdSimplex {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : StdSimplex 𝕜 (s : Set E),
        (w.map Subtype.val).convexCombination = x := by
  simpa using (Set.mem_conv_iff_exists_stdSimplex (𝕜 := 𝕜) (s := (s : Set E)) (x := x))

/-- Finite-support center-mass form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_centerMass {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : E → 𝕜,
        (∀ y ∈ s, 0 ≤ w y) ∧
        ∑ y ∈ s, w y = 1 ∧
        s.centerMass w id = x := by
  simpa using
    (Finset.mem_convexHull (R := 𝕜) (s := s) (x := x))

/-- Finite-support weighted-sum form of Theorem 2.3 on the chapter surface. -/
theorem mem_conv_iff_exists_weightedSum {s : Finset E} {x : E} :
    x ∈ (conv[𝕜] (s : Set E)) ↔
      ∃ w : E → 𝕜,
        (∀ y ∈ s, 0 ≤ w y) ∧
        ∑ y ∈ s, w y = 1 ∧
        ∑ y ∈ s, w y • y = x := by
  simpa using
    (Finset.mem_convexHull' (R := 𝕜) (s := s) (x := x))

end Finset

end
