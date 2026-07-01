import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Lemma_7_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.4 says that the closure `cl f` of a convex function is completely
  determined by the values of `f` on `ri (dom f)`, rendered here as `riDom[𝕜](f)`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `lowerSemicontinuousHull` for the lower-semicontinuous hull, `Function.IsConvex` for convexity,
  and mathlib's `intrinsicInterior 𝕜` for relative interior. In this project, Rockafellar's
  closure `cl f` is represented directly by the chapter notation `cl(f)` for the owner
  `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `dom f` is the chapter owner set `dom(f)`, and agreement
  "on `ri (dom f)`" is expressed canonically by `Set.EqOn` on `riDom[𝕜](f)`.

Domain-style sampling used here:
- the chapter effective-domain owner `dom(·)` from `Definition_4_4`;
- the chapter owner predicate `Function.IsConvex` from `Theorem_4_2`;
- the chapter owner construction `lowerSemicontinuousHull` from `Text_7_0_4`;
- the epigraph owner `Function.verticalInfimum` and its comparison theorem
  `le_verticalInfimum_of_subset_epi` from `Chap01.Theorem_5_3`;
- the nearby epigraph-relative-interior bridge
  `Function.IsConvex.mem_ri_epi_iff`
  from `Lemma_7_3`, which is the source theorem's main geometric input.

Primitive data vs derived API:
- primitive datum: an extended-codomain function `f : E → WithTopBot 𝕜`;
- owner construction: `cl(f)`;
- derived API: equality of closures from equality of relative interiors of the owner effective
  domains and agreement on that common relative interior `riDom[𝕜](f)`.

Layer target: the theorem remains `source-facing`, but it belongs on the chapter owner namespace
`Function.IsConvex`, and is stated directly using the chapter owner construction
`cl(·)`, the canonical set-theoretic owner APIs, and the scoped chapter notation `riDom[𝕜](·)` for
the relative interior of the effective domain.
-/

namespace Function.IsConvex

/-- Corollary 7.3.4, primitive epigraph-relative-interior form. -/
theorem ri_epi_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    ri[𝕜](epi f) = ri[𝕜](epi g) := by
  ext p
  rcases p with ⟨x, μ⟩
  rw [hf.mem_ri_epi_iff, hg.mem_ri_epi_iff]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨hri ▸ hx, by simpa [hfg hx] using hlt⟩
  · rintro ⟨hx, hlt⟩
    have hx' : x ∈ riDom[𝕜](f) := hri.symm ▸ hx
    exact ⟨hx', by simpa [hfg hx'] using hlt⟩

/-- Corollary 7.3.4, primitive epigraph-closure form. -/
theorem closure_epi_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    closure (epi f) = closure (epi g) := by
  calc
    closure (epi f) = closure (ri[𝕜](epi f)) := by
      simpa using hf.closure_intrinsicInterior_eq_closure.symm
    _ = closure (ri[𝕜](epi g)) := by
      rw [hf.ri_epi_eq_of_riDom_eq_and_eqOn hg hri hfg]
    _ = closure (epi g) := by
      simpa using hg.closure_intrinsicInterior_eq_closure

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
    [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace E]

namespace Function

/-- Primitive owner bridge: equality of closed epigraphs implies equality of Rockafellar closures
`cl(·)`. This stays at the minimal codomain abstraction layer of `lowerSemicontinuousHull`. -/
theorem lowerSemicontinuousHull_eq_of_closure_epi_eq
    {f g : E → WithTopBot 𝕜} (hclosure : closure (epi f) = closure (epi g)) :
    cl(f) = cl(g) := by
  simpa [lowerSemicontinuousHull] using congrArg Function.verticalInfimum hclosure

end Function

end

section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

/-- Corollary 7.3.4: if two convex functions on a finite-dimensional ordered normed-field space have
same relative interior of their effective domains and agree there, then their closures `cl f` and
`cl g`, represented here by `cl(f)` and `cl(g)`, are equal. -/
-- Proof sketch: Lemma 7.3 identifies agreement on the common relative interior of the effective
-- domains with agreement on the relative interiors of the epigraphs. The convex-set closure
-- theorem for equal relative interiors then yields equality of the epigraph closures, and then the
-- primitive owner bridge `Function.lowerSemicontinuousHull_eq_of_closure_epi_eq` identifies the
-- closures.
theorem cl_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    cl(f) = cl(g) := by
  exact Function.lowerSemicontinuousHull_eq_of_closure_epi_eq
    (hf.closure_epi_eq_of_riDom_eq_and_eqOn hg hri hfg)

end Function.IsConvex

end
