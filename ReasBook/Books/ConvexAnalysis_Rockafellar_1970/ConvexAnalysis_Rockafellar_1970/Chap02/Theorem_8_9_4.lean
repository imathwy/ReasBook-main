import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_8_6_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ConvexERealFunction

section

/-!
Source/core/bridge triage:

  `rank[𝕜](f) = aff dim(dom f)` for a closed
  proper convex function by excluding nontrivial affine-line directions on which all translate
  profiles are constant.
- `core/canonical`: the owner abstractions already present upstream are
  `Function.lineal f`, `Function.lineality`, `Function.rank`, `dom(·)`,
  `Set.affineDim`, `Function.IsProper`, and `Function.IsConvex`.
- `bridge/view`: the owner-level equivalence `lineality[𝕜](f) = 0 ↔ ...` is the canonical
  bridge from
  `Function.lineal f` to the source's affine-line exclusion, while the displayed rank formula is
  the source-facing corollary obtained from `rank_eq`.

Domain-style sampling used here:
- `Function.lineality` and `Function.lineality_eq` from `Definition_8_9_2`;
- `Function.lineal` from `Definition_8_9_0`;
- `Function.forall_translate_profile_constant_iff_mem_constancySpace`
  from `Corollary_8_6_1`;
- `Function.mem_constancySpace_of_exists_upper_bound_along_line`
  from `Corollary_8_6_1`;
- `Function.rank` and `Function.rank_eq` from `Definition_8_9_2`;
- `dom(·)` from `Definition_4_4` together with `Set.affineDim` from `Definition_2_4_10`;
- `Function.constancySpace` and `Function.mem_constancySpace_iff_mem_recessionCone`
  from `Definiton_8_7_0`.

Primitive data vs derived API:
- primitive data: only the function `f : E → WithTopBot 𝕜`;
- owner-side derived API:
  `lineality[𝕜](f)`, `rank[𝕜](f)`, `dim[𝕜](dom(f))`, convexity, properness,
  and closedness;
- source-facing derived view retained here: the quantified affine-line exclusion
  `¬ ∃ y ≠ 0, ∃ x ∈ dom(f), ∀ t, f (x + t • y) = f x`.

Layer target:
- `bridge/view`: `lineality_eq_zero_iff_not_exists_affineLine`;
- `source-facing`: `rank_eq_dim_dom_iff_not_exists_affineLine`.
-/

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]

open scoped Rockafellar

variable (f : E → WithTopBot 𝕜)
variable [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction]

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] in
private theorem affDim_eq_zero_iff_not_exists_ne_zero_mem {C : Set E}
    [FiniteDimensional 𝕜 (affineSpan 𝕜 C).direction]
    (h0 : (0 : E) ∈ C) :
    dim[𝕜](C) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ C := by
  constructor
  · intro hC hy
    rcases hy with ⟨y, hyne, hy⟩
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    have h0A : (0 : E) ∈ A := (subset_affineSpan 𝕜 C) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hfin : Module.finrank 𝕜 A.direction = 0 := by
      rw [show dim[𝕜](C) = A.affineDim by rfl, AffineSubspace.affineDim, if_neg hAne] at hC
      exact_mod_cast hC
    have hdir : A.direction = ⊥ := Submodule.finrank_eq_zero.mp hfin
    have hyA : y ∈ A := (subset_affineSpan 𝕜 C) hy
    have hydir : y ∈ A.direction := by
      simpa using A.vsub_mem_direction hyA h0A
    have hy0 : y = 0 := by
      simpa [hdir] using hydir
    exact hyne hy0
  · intro hC
    let A : AffineSubspace 𝕜 E := affineSpan 𝕜 C
    have h0A : (0 : E) ∈ A := (subset_affineSpan 𝕜 C) h0
    have hAne : A ≠ ⊥ := by
      intro hbot
      have : (0 : E) ∉ (A : Set E) := by
        simp [hbot]
      exact this h0A
    have hsubset : C ⊆ ({0} : Set E) := by
      intro y hy
      by_contra hy0
      exact hC ⟨y, by simpa using hy0, hy⟩
    have hsubset0 : ({0} : Set E) ⊆ C := by
      intro y hy
      have hy0 : y = 0 := Set.mem_singleton_iff.mp hy
      simpa [hy0] using h0
    have hspan : affineSpan 𝕜 C = affineSpan 𝕜 ({0} : Set E) :=
      le_antisymm (affineSpan_mono 𝕜 hsubset) (affineSpan_mono 𝕜 hsubset0)
    have hdir : A.direction = ⊥ := by
      calc
        A.direction = (affineSpan 𝕜 ({0} : Set E)).direction := by
          simp [A, hspan]
        _ = vectorSpan 𝕜 ({0} : Set E) := by
          rw [direction_affineSpan 𝕜 ({0} : Set E)]
        _ = ⊥ := by
          rw [vectorSpan_singleton 𝕜 (0 : E)]
    rw [show dim[𝕜](C) = A.affineDim by rfl, AffineSubspace.affineDim, if_neg hAne, hdir]
    norm_num

omit [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] in
private theorem zero_mem_lineal
    (hf_proper : f.IsProper) (hf_convex : f.IsConvex 𝕜) :
    (0 : E) ∈ lin(f) := by
  have hconst :
      ∀ x : E, ∀ s t : 𝕜, f (x + s • (0 : E)) = f (x + t • (0 : E)) := by
    intro x s t
    simp
  have h0_lineal : (0 : E) ∈ lin(f) :=
    (Function.forall_translate_profile_constant_iff_mem_constancySpace
        f hf_convex hf_proper (0 : E)).1
      hconst
  exact h0_lineal

omit [FiniteDimensional 𝕜 (affineSpan 𝕜 lin(f)).direction] in
private theorem exists_affineLine_iff_exists_ne_zero_mem_lineal
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    (∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x) ↔
      ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) := by
  constructor
  · rintro ⟨y, hyne, x, hxdom, hline⟩
    have hfx_top : f x < (⊤ : WithTopBot 𝕜) := by
      simpa [mem_effectiveDomain] using hxdom
    have hline_le : ∀ t : 𝕜, f (x + t • y) ≤ f x := by
      intro t
      exact le_of_eq (hline t)
    refine ⟨y, hyne, ?_⟩
    exact
      Function.mem_constancySpace_of_exists_upper_bound_along_line
        (f := f) hf_convex hf_proper hf_closed y
        ⟨x, f x, hfx_top, hline_le⟩
  · rintro ⟨y, hyne, hylineal⟩
    have hconst :
        ∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y) :=
      (Function.forall_translate_profile_constant_iff_mem_constancySpace
          f hf_convex hf_proper y).2
        hylineal
    rcases hf_proper.nonempty_dom with ⟨x, hxdom⟩
    refine ⟨y, hyne, x, hxdom, ?_⟩
    intro t
    simpa using hconst x t (0 : 𝕜)

namespace Function

/-- Theorem 8.9.4, owner bridge: a closed proper convex function has zero lineality if and only if
`lin(f)` is trivial, equivalently it has no nontrivial affine-line direction through a
finite point on which `f` is constant. -/
theorem lineality_eq_zero_iff_not_exists_affineLine
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    lineality[𝕜](f) = 0 ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  have hzero_mem_lineal : (0 : E) ∈ lin(f) :=
    zero_mem_lineal (f := f) hf_proper hf_convex
  have hlineality :
      lineality[𝕜](f) = 0 ↔ ¬ ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) := by
    simpa [Function.lineality_eq (𝕜 := 𝕜) (f := f)] using
      (affDim_eq_zero_iff_not_exists_ne_zero_mem (C := lin(f)) hzero_mem_lineal)
  have hExists :
      (∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x) ↔
        ∃ y : E, y ≠ 0 ∧ y ∈ lin(f) :=
    exists_affineLine_iff_exists_ne_zero_mem_lineal (f := f) hf_closed hf_proper hf_convex
  exact hlineality.trans (not_congr hExists).symm

namespace IsClosedProperConvex

/-- Owner-bundled bridge form: the affine-line exclusion criterion can be used directly from
`hf : IsClosedProperConvex[𝕜] f` without repeatedly unpacking lower-semicontinuity, properness,
and convexity assumptions at call sites. -/
theorem lineality_eq_zero_iff_not_exists_affineLine
    (hf : Function.IsClosedProperConvex (𝕜 := 𝕜) f) :
    Function.lineality[𝕜](f) = 0 ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  exact
    Function.lineality_eq_zero_iff_not_exists_affineLine
      (f := f) hf.lowerSemicontinuous hf.proper hf.convex

end IsClosedProperConvex

variable [FiniteDimensional 𝕜 (affineSpan 𝕜 (dom(f))).direction]

-- Proof sketch: the owner bridge identifies the affine-line exclusion with
-- `lineality[𝕜](f) = 0`.
-- Combining that with `rank_eq`, the source identity
-- `rank[𝕜](f) = dim[𝕜](dom(f))` is exactly the same
-- vanishing-lineality condition, so the public theorem only needs the finite-dimensionality
-- instances already used by those owner invariants.
/-- Theorem 8.9.4: a closed proper convex function has rank equal to the affine dimension of its
effective domain if and only if it has no nontrivial affine-line direction through a finite point
on which `f` is constant. The public statement is organized at the owner level of `rank` and
`lineality`, so it assumes finite-dimensionality only for the affine spans of `dom f` and of the
space `lin(f)`. -/
theorem rank_eq_dim_dom_iff_not_exists_affineLine
    (hf_closed : LowerSemicontinuous f) (hf_proper : f.IsProper)
    (hf_convex : f.IsConvex 𝕜) :
    rank[𝕜](f) = dim[𝕜](dom(f)) ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  constructor
  · intro hrank
    have hlineality : lineality[𝕜](f) = 0 := by
      have hrank' : dim[𝕜](dom(f)) - lineality[𝕜](f) = dim[𝕜](dom(f)) := by
        simpa [Function.rank_eq (𝕜 := 𝕜) (f := f), Function.lineality] using hrank
      linarith
    exact (lineality_eq_zero_iff_not_exists_affineLine f hf_closed hf_proper hf_convex).1
      hlineality
  · intro hnoAffineLine
    have hlineality : lineality[𝕜](f) = 0 :=
      (lineality_eq_zero_iff_not_exists_affineLine f hf_closed hf_proper hf_convex).2
        hnoAffineLine
    rw [Function.rank_eq (𝕜 := 𝕜) (f := f)]
    simpa [Function.lineality, hlineality]

namespace IsClosedProperConvex

/-- Owner-bundled bridge form of `rank_eq_dim_dom_iff_not_exists_affineLine`. -/
theorem rank_eq_dim_dom_iff_not_exists_affineLine
    (hf : Function.IsClosedProperConvex (𝕜 := 𝕜) f) :
    Function.rank[𝕜](f) = dim[𝕜](dom(f)) ↔
      ¬ ∃ y : E, y ≠ 0 ∧ ∃ x : E, x ∈ dom(f) ∧ ∀ t : 𝕜, f (x + t • y) = f x := by
  exact
    Function.rank_eq_dim_dom_iff_not_exists_affineLine
      (f := f) hf.lowerSemicontinuous hf.proper hf.convex

end IsClosedProperConvex

end Function

end

end

end

end ConvexERealFunction
