import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: the remark isolates the geometric locus governing the comparison between a
  convex function `f` and its closure `cl(f)`, namely the relative interior `ri[𝕜](epi f)` of the
  epigraph.
- `core/canonical`: the owner notions already present in the chapter are the convexity predicate
  `Function.IsConvex 𝕜`, the epigraph owner `epi`, Rockafellar's closure owner `cl(·)`, and the
  scalar-parameterized relative-interior notation `ri[𝕜](·)`.
- `bridge/view`: the prose claim that the comparison between `f` and `cl(f)` hinges on relative
  interiors is rendered as equality of the two epigraph relative interiors.

Domain-style sampling used here:
- `Function.IsConvex` from Theorem 4.2;
- `epi` from Definition 4.1;
- `ri[𝕜](·)` from Text 6.8;
- `cl(·)` and `closure_epi_eq_epi_lowerSemicontinuousHull` from Text 7.0.4.

Primitive data vs derived API:
- primitive input: a convex `WithBotTop 𝕜`-valued function `f`;
- primitive geometric output: closure-invariance of the epigraph relative interior
  `ri[𝕜](closure (epi f)) = ri[𝕜](epi f)`;
- derived closure-operator output: the common relative interior of `epi f` and `epi (cl(f))`.

Layer target: `source-facing`, stated directly in the chapter's epigraph and relative-interior
language rather than through a separate wrapper around the later comparison theorems.
-/

namespace Function.IsConvex

section Geometry

variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable {f : E → WithBotTop 𝕜}

/-- Primitive geometric owner form behind Remark 7.0.23: for a convex function, the relative
interior of the epigraph is invariant under ambient closure. -/
theorem ri_closure_epi_eq (hf : f.IsConvex 𝕜) :
    ri[𝕜](closure (epi f)) = ri[𝕜](epi f) := by
  simpa using hf.convex_epi.intrinsicInterior_closure_eq_intrinsicInterior

end Geometry

section LowerSemicontinuousHull

variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

variable {f : E → WithBotTop 𝕜}

-- Proof sketch: Text 7.0.4 identifies `epi (cl(f))` with `closure (epi f)`. Since `epi f` is
-- convex by `hf`, Theorem 6.3 gives invariance of relative interior under closure for that set,
-- yielding the claimed identity.
/-- Remark 7.0.23: for a convex function, the comparison between `f` and its closure `cl(f)` is
governed by the common relative interior of their epigraphs; equivalently,
`ri[𝕜](epi (cl(f))) = ri[𝕜](epi f)`. -/
theorem ri_epi_lowerSemicontinuousHull_eq
    (hf : f.IsConvex 𝕜) :
    ri[𝕜](epi (cl(f))) = ri[𝕜](epi f) := by
  calc
    ri[𝕜](epi (cl(f))) = ri[𝕜](closure (epi f)) := by
      simp [closure_epi_eq_epi_lowerSemicontinuousHull]
    _ = ri[𝕜](epi f) := hf.ri_closure_epi_eq

end LowerSemicontinuousHull

end Function.IsConvex

end
