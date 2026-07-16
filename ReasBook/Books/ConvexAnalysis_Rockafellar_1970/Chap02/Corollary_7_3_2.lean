import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Prop_4_4_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Corollary_7_3_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

universe u

variable
    {𝕜 : Type*} {E : Type u}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.2 says that if a convex function has a point of the closure of a
  convex set `C` lying strictly below a level `α`, and the relative interior of `C` lies in
  the effective domain of the function, then the same strict sublevel set already meets
  `ri[𝕜](C)`.
- `core/canonical`: the owner abstraction is `ConvexOn 𝕜 (Set.univ : Set E) f`,
  mathlib's `Convex 𝕜 C`, the closure operator `closure`, the relative interior operator
  `intrinsicInterior 𝕜`, and the chapter owner notation `riDom[𝕜](·)` for relative interiors of
  effective domains.
- `bridge/view`: Rockafellar's `ri C` is represented by the local source-facing notation
  `ri[𝕜](C) = intrinsicInterior 𝕜 C`, while the effective domain is expressed through the chapter
  owner `dom(f)`.
- Domain-style sampling used here: the owner predicate
  `ConvexOn 𝕜 (Set.univ : Set E) f`, the owner closure/relative-interior identity
  `Convex.intrinsicInterior_closure_eq_intrinsicInterior`, and the nearby strict-sublevel
  relative-interior result
  `Function.IsConvex.riDom_inter_nonempty_of_sublevel_nonempty` from
  Corollary 7.3.1.
- Primitive data vs derived API: the primitive inputs are the convex function `f`, the convex set
  `C`, the domain inclusion on `ri[𝕜](C)`, the level `α : WithTopBot 𝕜`, and a strict sublevel
  witness on `closure C`; the conclusion is the derived existence of a strict sublevel point on
  `ri[𝕜](C)`.
- Layer target: this item stays `source-facing`, and is expressed
  directly in the canonical convex-function/relative-interior language.
- Ambient-space refinement: the proof is coordinate-free and only uses the finite-dimensional
  ordered normed-field owner layer already fixed in Chapter 7.
-/

-- Proof sketch: apply Corollary 7.3.1 to the auxiliary function obtained from the restriction of
-- `f` to `closure C` by the canonical `Set.piecewise` extension with value `⊤` off `closure C`.
-- Its convexity is read through the restricted epigraph owner `epi[closure C] f`, and its
-- effective domain has relative interior `ri[𝕜](C)`, using
-- `Convex.intrinsicInterior_closure_eq_intrinsicInterior hC` together with the hypothesis
-- `ri[𝕜](C) ⊆ dom(f)`. Translate the resulting strict-sublevel point on `riDom[𝕜](g)` back to the
-- relative interior of that effective domain back to a point of `ri[𝕜](C)` for the original `f`.
/-- Corollary 7.3.2, intrinsic-closure existential owner form: if a strict `α`-sublevel witness
exists on `intrinsicClosure 𝕜 C`, and if `ri[𝕜](C)` lies in `dom(f)`, then a strict
`α`-sublevel witness exists on `ri[𝕜](C)`. -/
theorem exists_lt_on_ri_of_exists_lt_on_intrinsicClosure
    {C : Set E} (hf : f.IsConvex 𝕜) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ intrinsicClosure 𝕜 C, f x < α) :
    ∃ x ∈ ri[𝕜](C), f x < α := by
  classical
  let g : E → WithTopBot 𝕜 := (closure C).piecewise f ⊤
  have hEpi_g : epi g = epi[closure C] f := by
    ext p
    rcases p with ⟨x, μ⟩
    by_cases hx : x ∈ closure C
    · simp [g, epi, hx]
    · constructor
      · intro hp
        exfalso
        have htop :
            ¬ ((⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜)) := by
          have hμtop : (μ : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
            change (((μ : WithBot 𝕜) : WithTop (WithBot 𝕜)) < (⊤ : WithTop (WithBot 𝕜)))
            exact WithTop.coe_lt_top _
          exact not_le_of_gt hμtop
        have hgx : g x = ⊤ := by
          simp [g, hx]
        rw [mem_epi_iff] at hp
        rw [hgx] at hp
        exact htop hp
      · intro hp
        exact False.elim (hx hp.1)
  have hg_epi : Convex 𝕜 (epi g) := by
    rw [hEpi_g]
    rw [epi_restrict_eq_preimage_fst_inter]
    exact (hC.closure.linear_preimage (LinearMap.fst 𝕜 E 𝕜)).inter hf
  have hg : g.IsConvex 𝕜 := hg_epi
  obtain ⟨x, hxC, hxlt⟩ := hα
  have hxC' : x ∈ closure C := by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using hxC
  have hglt : g x < α := by
    simpa [g, hxC'] using hxlt
  obtain ⟨y, hy, hylt⟩ :=
    Function.IsConvex.exists_lt_on_riDom_of_exists_lt (f := g) hg α ⟨x, hglt⟩
  have hdom_eq : dom(g) = closure C ∩ dom(f) := by
    ext z
    by_cases hzC : z ∈ closure C
    · simp [g, hzC, mem_effectiveDomain]
    · constructor
      · intro hz
        exfalso
        change g z < ⊤ at hz
        have hz_top : g z = ⊤ := by
          simp [g, hzC]
        exact ((lt_irrefl (⊤ : WithTopBot 𝕜)) (hz_top ▸ hz)).elim
      · intro hz
        exact False.elim (hzC hz.1)
  have hg_convexDom : Convex 𝕜 dom(g) := by
    rw [effectiveDomain_eq_image_fst_epi g]
    simpa using Convex.linear_image (hs := hg)
      (f := LinearMap.fst 𝕜 E 𝕜)
  have hri_eq : riDom[𝕜](g) = ri[𝕜](C) := by
    have hclosure : closure dom(g) = closure C := by
      apply subset_antisymm
      · simpa [hdom_eq, closure_closure] using
          closure_mono (Set.inter_subset_left : closure C ∩ dom(f) ⊆ closure C)
      · calc
          closure C = closure (ri[𝕜](C)) := by
            simpa using hC.closure_intrinsicInterior_eq_closure.symm
          _ ⊆ closure dom(g) := by
            apply closure_mono
            intro z hz
            rw [hdom_eq]
            exact ⟨subset_closure (intrinsicInterior_subset hz), hdom hz⟩
    change intrinsicInterior 𝕜 dom(g) = ri[𝕜](C)
    calc
      intrinsicInterior 𝕜 dom(g) = intrinsicInterior 𝕜 (closure dom(g)) := by
        simpa using hg_convexDom.intrinsicInterior_closure_eq_intrinsicInterior.symm
      _ = intrinsicInterior 𝕜 (closure C) := by simp [hclosure]
      _ = ri[𝕜](C) := hC.intrinsicInterior_closure_eq_intrinsicInterior
  rw [hri_eq] at hy
  have hyC : y ∈ closure C := subset_closure (intrinsicInterior_subset hy)
  exact ⟨y, hy, by simpa [g, hyC] using hylt⟩

/-- Corollary 7.3.2, intrinsic-closure nonempty-intersection bridge. -/
theorem ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty
    {C : Set E} (hf : f.IsConvex 𝕜) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ intrinsicClosure 𝕜 C, f x < α) :
    (ri[𝕜](C) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hxC, hxlt⟩
  rcases
      exists_lt_on_ri_of_exists_lt_on_intrinsicClosure
        hf hC α hdom ⟨x, hxC, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

/-- Corollary 7.3.2, ambient-closure existential bridge. -/
theorem exists_lt_on_ri_of_exists_lt_on_closure
    {C : Set E} (hf : f.IsConvex 𝕜) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ closure C, f x < α) :
    ∃ x ∈ ri[𝕜](C), f x < α := by
  rcases hα with ⟨x, hx, hxlt⟩
  exact
    exists_lt_on_ri_of_exists_lt_on_intrinsicClosure hf hC α hdom
      ⟨x, by simpa [intrinsicClosure_eq_closure 𝕜 C] using hx, hxlt⟩

/-- Corollary 7.3.2, ambient-closure bridge for strict-open-sublevel intersections. -/
theorem ri_inter_nonempty_of_closure_inter_openSublevel_nonempty
    {C : Set E} (hf : f.IsConvex 𝕜) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ closure C, f x < α) :
    (ri[𝕜](C) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hx, hxlt⟩
  rcases exists_lt_on_ri_of_exists_lt_on_closure hf hC α hdom ⟨x, hx, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

end Function.IsConvex

end
