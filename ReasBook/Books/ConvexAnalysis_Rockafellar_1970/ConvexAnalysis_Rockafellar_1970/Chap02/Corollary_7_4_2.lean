import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

variable {f : E → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.4.2 says that a proper convex function is closed whenever its
  effective domain is an affine set.
- `core/canonical`: the owner abstractions already fixed in the chapter are `Function.IsConvex 𝕜`,
  `Function.IsProper`, the effective-domain owner `dom(·)`, the affine-set owner
  `Set.IsAffine 𝕜`, and the bundled closed/proper/convex predicate
  `Function.IsClosedProperConvex`.
- `bridge/view`: the textbook phrase "`dom f` is an affine set" is rendered by the canonical
  set-level affine owner predicate `Set.IsAffine 𝕜 dom(f)`.

Domain-style sampling used here:
- `Function.IsConvex.lowerSemicontinuousHull_isClosedProperConvex_of_isProper` from Theorem 7.4;
- `Function.IsConvex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper` from
  Theorem 7.4;
- the affine-set owner `Set.IsAffine 𝕜` (equivalently, affine-subspace carrier form);
- the chapter closed/proper/convex owner `Function.IsClosedProperConvex`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop 𝕜`, together with convexity, properness, and
  the affine-domain hypothesis;
- derived output: the canonical closed/proper/convex owner for `f`, which packages the source
  conclusion "`f` is closed" together with the original convexity and properness assumptions.

Layer target: `source-facing`, stated directly on the canonical chapter owners rather than through
an auxiliary wrapper for affine domains.
-/

-- Proof sketch: Theorem 7.4 gives `Set.EqOn (cl(f)) f (intrinsicFrontier 𝕜 dom(f))ᶜ`. If
-- `dom(f)` is affine, then its intrinsic interior is all of `dom(f)`, so its intrinsic frontier
-- is empty. Hence `cl(f) = f`, and the closed/proper/convex conclusion for `cl(f)` from
-- Theorem 7.4 transfers directly to `f`.
/-- Corollary 7.4.2: if a proper convex function has affine effective domain, written here as
`Set.IsAffine 𝕜 dom(f)`, then it is closed; equivalently, together with the
original hypotheses, it is a closed proper convex function. In particular, this applies when `f`
is finite throughout a finite-dimensional ambient space, so that `dom(f) = Set.univ`. -/
  theorem isClosedProperConvex_of_affine_dom_of_isProper
    (hf : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hdom_affine : Set.IsAffine 𝕜 dom(f)) :
    IsClosedProperConvex[𝕜] f := by
  have hspan : affineSpan 𝕜 dom(f) = dom(f) :=
    (Set.isAffine_iff_affineSpan_eq_self (k := 𝕜) (dom(f))).1 hdom_affine
  have hpre : ((↑) : affineSpan 𝕜 dom(f) → E) ⁻¹' dom(f) = Set.univ := by
    ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : (x : E) ∈ (affineSpan 𝕜 dom(f) : Set E) := x.2
      rw [hspan] at hx
      exact hx
  have hfrontier : intrinsicFrontier 𝕜 dom(f) = ∅ := by
    rw [intrinsicFrontier, hpre, frontier_univ, Set.image_empty]
  have hcl : cl(f) = f := by
    ext x
    have hEqOn : Set.EqOn (cl(f)) f (rb[𝕜](dom(f)))ᶜ :=
      hf.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
    have hx : x ∈ (rb[𝕜](dom(f)))ᶜ := by
      simp [hfrontier]
    exact hEqOn hx
  rw [← hcl]
  exact hf.lowerSemicontinuousHull_isClosedProperConvex_of_isProper hf_proper

end Function.IsConvex

end
