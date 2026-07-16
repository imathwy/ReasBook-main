import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_4_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_10
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

namespace Function

section GenericCodomain

variable {X : Type*} [TopologicalSpace X]
variable {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜] [TopologicalSpace 𝕜] [Nonempty 𝕜]

/-- For a `WithBotTop 𝕜`-valued function with a nonempty finite codomain layer, passing to the
Chapter 7 closure `cl(·)` can only enlarge the effective domain. This owner-level inclusion is
independent of convexity and properness. -/
theorem subset_dom_lowerSemicontinuousHull (f : X → WithBotTop 𝕜) :
    dom(f) ⊆ dom(cl(f)) := by
  rw [lowerSemicontinuousHull, effectiveDomain_verticalInfimum_eq_image_fst]
  rw [effectiveDomain_eq_image_fst_epi]
  rintro x ⟨p, hp, rfl⟩
  exact ⟨p, subset_closure hp, rfl⟩

end GenericCodomain

end Function

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
variable [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- This finite-dimensional ordered-normed layer is exactly the upstream owner layer used by
-- Theorem 7.4 (`cl(·)` off-frontier `EqOn`) and Theorem 6.3 (intrinsic-interior/closure
-- invariance for convex sets), which this corollary chains without adding stronger assumptions.

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.4.1 says that for a proper convex function, passing from `f` to its
  closure `cl(f)` can only enlarge the effective domain by adding relative-boundary points, and
  therefore does not change the closure, relative interior, or dimension of the effective domain.
- `core/canonical`: the owner abstractions already fixed in the chapter are `Function.IsConvex 𝕜`,
  `Function.IsProper`, Rockafellar's closure owner `cl(·)`, the effective-domain owners `dom(·)`,
  `rb(·)`, and `riDom(·)`, and the set-dimension owner `Set.affineDim`.
- `bridge/view`: the textbook relative boundary is rendered directly by the chapter notation
  `rb[𝕜](dom(f))`, while the relative interior and dimension claims are expressed on
  `riDom[𝕜](·)` and
  `Set.affineDim`.

Domain-style sampling used here:
- `Function.subset_dom_lowerSemicontinuousHull` for the basic inclusion
  `dom(f) ⊆ dom(cl(f))`;
- `Function.IsConvex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper` from
  Theorem 7.4 for the boundary-localization clause;
- `Convex.closure_intrinsicInterior_eq_closure` and
  `Convex.intrinsicInterior_closure_eq_intrinsicInterior` from Theorem 6.3 for the relative-
  interior invariance under closure;
- `Set.affineDim` from Definition 2.4.10 for the dimension clause.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, together with convexity and properness;
- derived outputs: the domain inclusion, the relative-boundary localization of the new domain
  points of `cl(f)`, and the resulting closure, relative-interior, and affine-dimension
  equalities.

Layer target: `source-facing`, split into atomic owner-level consequences rather than packaged as
one large conjunction.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop 𝕜}

/- Corollary 7.4.1 (1): the domain inclusion `dom(f) ⊆ dom(cl(f))` is exactly the owner theorem
`Function.subset_dom_lowerSemicontinuousHull`; it does not use convexity or properness. -/
recall Function.subset_dom_lowerSemicontinuousHull

-- Proof sketch: if `x ∈ dom(cl(f)) \ dom(f)` and `x` were not on the relative frontier of
-- `dom(f)`, then Theorem 7.4 would give `cl(f) x = f x`. Since `x ∉ dom(f)`, this would force
-- `cl(f) x = ⊤`, contradicting `x ∈ dom(cl(f))`. So every new point of `dom(cl(f))` lies in the
-- relative frontier of `dom(f)`.
/-- Corollary 7.4.1 (2): any point added to the effective domain by passing from `f` to `cl(f)`
lies in the relative frontier of `dom(f)`. -/
theorem diff_dom_lowerSemicontinuousHull_subset_intrinsicFrontier_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    dom(cl(f)) \ dom(f) ⊆ rb[𝕜](dom(f)) := by
  intro x hx
  by_contra hx_not_frontier
  have hx_off_frontier : x ∈ (rb[𝕜](dom(f)))ᶜ := by
    simpa [Set.mem_compl] using hx_not_frontier
  have hEqOn :
      Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ :=
    hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
  have hcl_eq_f : cl(f) x = f x := hEqOn hx_off_frontier
  have hx_not_dom : x ∉ dom(f) := hx.2
  have hf_top : f x = (⊤ : WithBotTop 𝕜) := by
    by_contra hfx_ne_top
    exact hx_not_dom (mem_effectiveDomain.mpr (lt_of_le_of_ne le_top hfx_ne_top))
  have hcl_top : cl(f) x = (⊤ : WithBotTop 𝕜) := by
    simpa [hcl_eq_f] using hf_top
  have hcl_lt_top : cl(f) x < (⊤ : WithBotTop 𝕜) := mem_effectiveDomain.mp hx.1
  have htop_lt_top : (⊤ : WithBotTop 𝕜) < ⊤ := by
    rw [hcl_top] at hcl_lt_top
    exact hcl_lt_top
  exact (lt_irrefl (⊤ : WithBotTop 𝕜)) htop_lt_top

-- Proof sketch (intrinsic owner form): clause (2) localizes the new points in `dom(cl(f))` to the
-- relative frontier of `dom(f)`, hence to `intrinsicClosure 𝕜 (dom(f))`; together with
-- `dom(f) ⊆ dom(cl(f))`, this yields equality of intrinsic closures.
/-- Corollary 7.4.1 (3), intrinsic owner form: `dom(cl(f))` and `dom(f)` have the same intrinsic
closure. -/
theorem intrinsicClosure_dom_lowerSemicontinuousHull_eq_intrinsicClosure_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    intrinsicClosure 𝕜 (dom(cl(f))) = intrinsicClosure 𝕜 (dom(f)) := by
  refine subset_antisymm ?_ ?_
  · have hdom_subset : dom(cl(f)) ⊆ intrinsicClosure 𝕜 dom(f) := by
      intro x hx
      by_cases hx_dom : x ∈ dom(f)
      · exact subset_intrinsicClosure hx_dom
      · have hx_frontier : x ∈ rb[𝕜](dom(f)) :=
          (diff_dom_lowerSemicontinuousHull_subset_intrinsicFrontier_of_isProper
            (f := f) hf hf_proper) ⟨hx, hx_dom⟩
        exact intrinsicFrontier_subset_intrinsicClosure hx_frontier
    exact (intrinsicClosure_mono hdom_subset).trans (by
      simp)
  · exact intrinsicClosure_mono (Function.subset_dom_lowerSemicontinuousHull (f := f))

/-- Corollary 7.4.1 (3), ambient-closure bridge: `dom(cl(f))` and `dom(f)` have the same closure.
-/
theorem closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    closure (dom(cl(f))) = closure (dom(f)) := by
  simpa [intrinsicClosure_eq_closure 𝕜 (dom(cl(f))), intrinsicClosure_eq_closure 𝕜 (dom(f))]
    using
      intrinsicClosure_dom_lowerSemicontinuousHull_eq_intrinsicClosure_dom_of_isProper
        (f := f) hf hf_proper

-- Proof sketch: both `dom(f)` and `dom(cl(f))` are convex sets. For convex sets, taking closure
-- does not change the relative interior. Applying this to the common closure from clause (3)
-- gives the same relative interior for the two effective domains.
/-- Corollary 7.4.1 (4): `dom(cl(f))` and `dom(f)` have the same relative interior, written here
as equality of `riDom(cl(f))` and `riDom(f)`. -/
theorem riDom_lowerSemicontinuousHull_eq_riDom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    riDom[𝕜](cl(f)) = riDom[𝕜](f) := by
  have hconv_dom_f : Convex 𝕜 dom(f) := hf.convex_dom
  have hconv_dom_cl : Convex 𝕜 dom(cl(f)) := by
    exact (hf.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hf_proper).convex.convex_dom
  calc
    riDom[𝕜](cl(f))
        = ri[𝕜](closure (dom(cl(f)))) := by
            simpa [riDom_eq_intrinsicInterior_dom] using
              (hconv_dom_cl.intrinsicInterior_closure_eq_intrinsicInterior).symm
    _ = ri[𝕜](closure (dom(f))) := by
          rw [closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
            (f := f) hf hf_proper]
    _ = riDom[𝕜](f) := by
          simpa [riDom_eq_intrinsicInterior_dom] using
            hconv_dom_f.intrinsicInterior_closure_eq_intrinsicInterior

-- Proof sketch (primitive affine owner form): equal closures imply equal affine spans by
-- `Set.affineSpan_closure`.
/-- Corollary 7.4.1 (5), primitive affine owner form: `dom(cl(f))` and `dom(f)` have the same
affine span. -/
theorem affineSpan_dom_lowerSemicontinuousHull_eq_affineSpan_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    affineSpan 𝕜 (dom(cl(f))) = affineSpan 𝕜 (dom(f)) := by
  calc
    affineSpan 𝕜 (dom(cl(f)))
        = affineSpan 𝕜 (closure (dom(cl(f)))) := by
            simpa using (Set.affineSpan_closure (𝕜 := 𝕜) (C := dom(cl(f)))).symm
    _ = affineSpan 𝕜 (closure (dom(f))) := by
          rw [closure_dom_lowerSemicontinuousHull_eq_closure_dom_of_isProper
            (f := f) hf hf_proper]
    _ = affineSpan 𝕜 (dom(f)) := by
          simpa using (Set.affineSpan_closure (𝕜 := 𝕜) (C := dom(f)))

/-- Corollary 7.4.1 (5), affine-dimension bridge: `dom(cl(f))` and `dom(f)` have the same affine
dimension. -/
theorem affineDim_dom_lowerSemicontinuousHull_eq_affineDim_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    dim[𝕜](dom(cl(f))) = dim[𝕜](dom(f)) := by
  simpa [Set.affineDim] using
    congrArg (fun A : AffineSubspace 𝕜 E => A.affineDim)
      (affineSpan_dom_lowerSemicontinuousHull_eq_affineSpan_dom_of_isProper
        (f := f) hf hf_proper)

end Function.IsConvex

end
