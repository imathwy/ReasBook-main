import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_6_5_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_11_3_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_11_3

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 : Type*} [CommRing 𝕜] [Preorder 𝕜]
variable {V : Type*} [TopologicalSpace V] [AddCommGroup V] [Module 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 11.6 characterizes when a convex set `C` admits a non-trivial
  supporting hyperplane containing a given nonempty convex subset `D ⊆ C`.
- `core/canonical`: the owner abstractions are `Convex 𝕜`, the relative interior operator
  `intrinsicInterior 𝕜`, the Chapter 11 predicate `AffineSubspace.IsNontrivialSupportingHyperplane`,
  and the proper-separation relation `AffineSubspace.SeparatesProperly`.
- `bridge/view`: the textbook phrase "supporting hyperplane to `C` containing `D`" is expressed by
  `H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H`, while the proof route factors through Theorem
  11.3 on proper separation.
- Primitive data vs derived API: the primitive inputs are the two sets together with convexity,
  nonemptiness of `D`, and the inclusion `D ⊆ C`; existence of a containing supporting hyperplane
  and the disjointness criterion are theorem-level content.
- Domain-style sampling used here: `AffineSubspace.IsNontrivialSupportingHyperplane` from
  `Text_11_3_4`, `AffineSubspace.SeparatesProperly` from `Text_11_0_2`, the proper-separation
  criterion `exists_separatesProperly_iff_disjoint_ri` from
  `Theorem_11_3`, and the `Convex`-owner relative-interior inclusion theorem
  from `Corollary_6_5_2`.
- Layer target: `source-facing`, with the theorem stated directly in the supporting-hyperplane API
  and the canonical intrinsic-interior language, rather than by introducing a wrapper package.
- Ambient refinement: although Rockafellar states the theorem in `R^n`, the imported owner
  abstractions for proper separation, supporting hyperplanes, and relative interior already live
  on pairing spaces. This local bridge theorem therefore stays at the pairing owner layer rather
  than a real inner-product model.
-/

namespace AffineSubspace

variable {H : AffineSubspace 𝕜 V} {C D : Set V}

/-- A hyperplane properly separates `D` and `C` exactly when it is a non-trivial supporting
hyperplane to `C` containing `D`, provided `D` is nonempty and `D ⊆ C`. -/
-- Proof sketch: if `H` is a non-trivial supporting hyperplane to `C` and `D ⊆ H`, then `C` lies
-- in one supporting closed half-space and `D` lies in the frontier hyperplane, hence in both
-- associated closed half-spaces, so `H` separates `D` and `C`; nontriviality gives properness.
-- Conversely, if `H` properly separates `D` and `C` and `D ⊆ C`, then every point of `D` must
-- lie in the intersection of the two opposite closed half-spaces, hence in `H` itself. Since
-- `D` is nonempty, this yields a contact point of `C` with `H`, so `H` is supporting, and
-- properness shows `C` is not contained in `H`.
theorem separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset
    (hD_nonempty : D.Nonempty) (hDC : D ⊆ C) :
    (H separatesProperly[Y] D and C) ↔
      H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H := sorry

end AffineSubspace

end

section

open scoped Rockafellar

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing V Y 𝕜]

/-- Theorem 11.6: for a convex set `C` and a nonempty convex subset `D ⊆ C`, there exists a
non-trivial supporting hyperplane to `C` containing `D` if and only if `D` is disjoint from the
relative interior `ri[𝕜](C)`. -/
-- Proof sketch: use
-- `AffineSubspace.separatesProperly_iff_isNontrivialSupportingHyperplane_and_subset` to rewrite
-- the existence of a non-trivial supporting hyperplane containing `D` as the existence of a
-- proper separating hyperplane for `D` and `C`. Theorem 11.3 then shows this is equivalent to
-- disjointness of `ri[𝕜](D)` and `ri[𝕜](C)`. Finally, because `D ⊆ C`, Corollary 6.5.2 turns
-- that condition into `Disjoint D (ri[𝕜](C))`.
theorem exists_nontrivial_supporting_hyperplane_containing_iff_disjoint_intrinsicInterior
    {C D : Set V} (hC_conv : Convex 𝕜 C) (hD_conv : Convex 𝕜 D) (hD_nonempty : D.Nonempty)
    (hDC : D ⊆ C) :
    (∃ H : AffineSubspace 𝕜 V, H.IsNontrivialSupportingHyperplane Y C ∧ D ⊆ H) ↔
      Disjoint D (ri[𝕜](C)) := sorry

/-- A boundary point of a convex set lies on a non-trivial supporting hyperplane. -/
theorem exists_nontrivial_supporting_hyperplane_of_mem_rb
    {C : Set V} (hC_conv : Convex 𝕜 C) {x : V} (hx : x ∈ C)
    (hxbd : x ∈ rb[𝕜](C)) :
    ∃ H : AffineSubspace 𝕜 V, H.IsNontrivialSupportingHyperplane Y C ∧ x ∈ H := by
  have hx_not_ri : x ∉ ri[𝕜](C) := by
    rw [← intrinsicClosure_diff_intrinsicInterior] at hxbd
    exact hxbd.2
  have hdisj : Disjoint ({x} : Set V) (ri[𝕜](C)) := by
    simpa [Set.disjoint_singleton_left] using hx_not_ri
  rcases (exists_nontrivial_supporting_hyperplane_containing_iff_disjoint_intrinsicInterior
      (Y := Y) hC_conv (convex_singleton x) (Set.singleton_nonempty x)
      (Set.singleton_subset_iff.2 hx)).2
      hdisj with
    ⟨H, hH, hxH⟩
  exact ⟨H, hH, hxH (by simp)⟩

end
