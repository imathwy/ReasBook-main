import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_6

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [Field 𝕜] [LinearOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (1): for a convex function with `dom(f) ⊆ riDom[𝕜](f)`, the
relative interior `ri[𝕜]({x | f x ≤ α})` of the closed `α`-sublevel set is exactly the strict
`α`-sublevel set whenever that strict sublevel set is nonempty. -/
theorem intrinsicInterior_closedSublevel_eq_openSublevel (hf : f.IsConvex 𝕜) (α : 𝕜)
    (hdom_subset_riDom : dom(f) ⊆ riDom[𝕜](f))
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    ri[𝕜]({x : E | f x ≤ α}) = {x : E | f x < α} := by
  calc
    ri[𝕜]({x : E | f x ≤ α}) = riDom[𝕜](f) ∩ {x : E | f x < α} :=
      hf.intrinsicInterior_closedSublevel_eq_riDom_inter_openSublevel α hα
    _ = {x : E | f x < α} := by
      ext x
      constructor
      · intro hx
        exact hx.2
      · intro hx
        refine ⟨hdom_subset_riDom ?_, hx⟩
        rw [mem_effectiveDomain]
        exact lt_trans hx (WithTopBot.coe_lt_top α)

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (2), ambient-closure primitive bridge: if a convex function has nonempty
strict `α`-sublevel set and closed `α`-sublevel set, then the closure of the strict `α`-sublevel
set is the closed `α`-sublevel set. -/
theorem closure_openSublevel_eq_closedSublevel_of_isClosed
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    (hsublevel_closed : IsClosed {x : E | f x ≤ α})
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    closure {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  calc
    closure {x : E | f x < α} = {x : E | cl(f) x ≤ α} := by
      simpa using hf.closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα
    _ = closure {x : E | f x ≤ α} := by
      simpa using (hf.closure_closedSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα).symm
    _ = {x : E | f x ≤ α} := hsublevel_closed.closure_eq

/-- Corollary 7.6.1 (2), ambient-closure lower-semicontinuous bridge: if a lower semicontinuous
convex function has nonempty strict `α`-sublevel set, then the closure of the strict `α`-sublevel
set is the closed `α`-sublevel set. -/
theorem closure_openSublevel_eq_closedSublevel
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
    (hf_lsc : LowerSemicontinuous f)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    closure {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  calc
    closure {x : E | f x < α} = {x : E | cl(f) x ≤ α} := by
      simpa using hf.closure_openSublevel_eq_closedSublevel_lowerSemicontinuousHull α hα
    _ = {x : E | f x ≤ α} := by
      simp [lowerSemicontinuousHull_eq_self hf_lsc]

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [OrderTopology 𝕜]
  [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.6.1 (2), intrinsic-closure primitive form. -/
theorem intrinsicClosure_openSublevel_eq_closedSublevel_of_isClosed
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    (hsublevel_closed : IsClosed {x : E | f x ≤ α})
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    intrinsicClosure 𝕜 {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  have hclosure :
      closure ({x : E | f x < α} : Set E) = {x : E | f x ≤ α} :=
    hf.closure_openSublevel_eq_closedSublevel_of_isClosed α hsublevel_closed hα
  have hsubset_affineSpan :
      ({x : E | f x ≤ α} : Set E) ⊆ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
    rw [← hclosure]
    refine closure_minimal (subset_affineSpan 𝕜 ({x : E | f x < α} : Set E)) ?_
    exact (affineSpan 𝕜 ({x : E | f x < α} : Set E)).closed_of_finiteDimensional
  calc
    intrinsicClosure 𝕜 ({x : E | f x < α} : Set E) =
        closure ({x : E | f x < α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa using
        (intrinsicClosure_eq_closure_inter_affineSpan (𝕜 := 𝕜)
          ({x : E | f x < α} : Set E))
    _ = ({x : E | f x ≤ α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa [hclosure]
    _ = {x : E | f x ≤ α} :=
      Set.inter_eq_left.2 hsubset_affineSpan

/-- Corollary 7.6.1 (2), intrinsic-closure lower-semicontinuous bridge. -/
theorem intrinsicClosure_openSublevel_eq_closedSublevel
    (hf : f.IsConvex 𝕜) (α : 𝕜)
    [NoBotOrder 𝕜] [NoMinOrder 𝕜] [Nonempty 𝕜]
    (hf_lsc : LowerSemicontinuous f)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    intrinsicClosure 𝕜 {x : E | f x < α} =
      {x : E | f x ≤ α} := by
  have hclosure :
      closure ({x : E | f x < α} : Set E) = {x : E | f x ≤ α} :=
    hf.closure_openSublevel_eq_closedSublevel α hf_lsc hα
  have hsubset_affineSpan :
      ({x : E | f x ≤ α} : Set E) ⊆ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
    rw [← hclosure]
    refine closure_minimal (subset_affineSpan 𝕜 ({x : E | f x < α} : Set E)) ?_
    exact (affineSpan 𝕜 ({x : E | f x < α} : Set E)).closed_of_finiteDimensional
  calc
    intrinsicClosure 𝕜 ({x : E | f x < α} : Set E) =
        closure ({x : E | f x < α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa using
        (intrinsicClosure_eq_closure_inter_affineSpan (𝕜 := 𝕜)
          ({x : E | f x < α} : Set E))
    _ = ({x : E | f x ≤ α} : Set E) ∩ affineSpan 𝕜 ({x : E | f x < α} : Set E) := by
      simpa [hclosure]
    _ = {x : E | f x ≤ α} :=
      Set.inter_eq_left.2 hsubset_affineSpan

end Function.IsConvex

end
