import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_8
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_12

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

/-
Source/core/bridge triage:
- `source-facing`: Lemma 7.3 identifies the relative interior of the epigraph of a convex function
  with the strict vertical region above the function over the relative interior of its effective
  domain.
- `core/canonical`: the owner notion is `ConvexOn 𝕜 (Set.univ : Set E) f`, together with the
  effective-domain owner `dom(·)`, the chapter epigraph owner `epi`, mathlib's
  `intrinsicInterior 𝕜`, and the product-fiber owner theorem
  `Convex.mem_ri_iff_mem_ri_base_and_fiber`.
  `ri[𝕜](epi f)` and `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`. This theorem is the
  epigraph specialization of the owner product-fiber statement from Theorem 6.8, with the base
  projection identified by `effectiveDomain_eq_image_fst_epi`. The source clause `μ < ∞` becomes
  automatic because the epigraph height coordinate is already a scalar `μ : 𝕜`.
- Domain-style sampling used here: the chapter owner `ConvexOn 𝕜 (Set.univ : Set E) f`,
  `epi` from Definition 4.1, and `dom(·)` from Definition 4.4, together with the projection
  bridge `effectiveDomain_eq_image_fst_epi`, the product relative-interior theorem
  `Convex.mem_ri_iff_mem_ri_base_and_fiber` from Theorem 6.8, and
  the upper-ray pullback theorem `ri_preimage_coe_Ici` from Text 6.12.
- Primitive data vs derived API: the primitive datum is only the function `f`; the epigraph and
  effective domain are canonical derived owner expressions and are kept unbundled.
- Layer target: this item is a source-facing theorem stated directly in the canonical
  `intrinsicInterior` language.
- Ambient-space refinement: the textbook `R^n` statement is only a coordinate model, so the public
  theorem is stated on the scalar-generic finite-dimensional normed-space owner layer and
  specializes to the real case.
-/

-- Proof sketch: specialize
-- `Convex.mem_ri_iff_mem_ri_base_and_fiber` to the convex
-- epigraph `epi f`, using `hf` to supply convexity. The projection of that epigraph to the base
-- is exactly `dom(f)`. For each fixed base point `x`, the fiber is the upper ray
-- `{μ : 𝕜 | f x ≤ μ}`, whose relative interior is the strict ray `{μ : 𝕜 | f x < μ}` whenever
-- `f x` is finite.
/- Lemma 7.3: for a convex function `f : E → WithTopBot 𝕜`, the relative interior of its epigraph
consists exactly of pairs `(x, μ)` such that `x` lies in `riDom[𝕜](f)` and `f x < μ`. Specializing
to `𝕜 = ℝ` recovers the textbook `R^n` statement with codomain `EReal = WithTopBot ℝ`. -/
namespace Function.IsConvexOn

@[simp] theorem mem_ri_epi_restrict_iff
    {f : E → WithTopBot 𝕜} {s : Set E} (hf : ConvexOn 𝕜 s f) {p : E × 𝕜} :
    p ∈ ri[𝕜](epi[s] f) ↔
      p.1 ∈ ri[𝕜](s ∩ dom(f)) ∧ f p.1 < p.2 := by
  rcases p with ⟨x, μ⟩
  have hEpi : Convex 𝕜 (epi[s] f) := by
    simpa using hf.convex_finiteHeight_epigraph
  have hmem :
      (x, μ) ∈ ri[𝕜](epi[s] f) ↔
        x ∈ ri[𝕜](Prod.fst '' epi[s] f) ∧
          μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi[s] f) :=
    hEpi.mem_ri_iff_mem_ri_base_and_fiber
  rw [← effectiveDomain_inter_eq_image_fst_epi (f := f) (S := s)] at hmem
  have hUpper :
      μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔ f x < μ := by
    have hUpper' :
        μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔
          μ ∈ {r : 𝕜 | f x < r} := by
      simpa using
        congrArg (fun t : Set 𝕜 => μ ∈ t) (ri_preimage_coe_Ici (a := f x))
    simpa using hUpper'
  constructor
  · intro hxμ
    rcases hmem.mp hxμ with ⟨hx, hμ⟩
    have hxs : x ∈ s := (intrinsicInterior_subset hx).1
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := by
      simpa [epi, hxs] using hμ
    exact ⟨hx, hUpper.mp hμ'⟩
  · rintro ⟨hx, hlt⟩
    have hxs : x ∈ s := (intrinsicInterior_subset hx).1
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := hUpper.mpr hlt
    have hμ : μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi[s] f) := by
      simpa [epi, hxs] using hμ'
    exact hmem.mpr ⟨hx, hμ⟩

theorem ri_epi_restrict_eq
    {f : E → WithTopBot 𝕜} {s : Set E} (hf : ConvexOn 𝕜 s f) :
    ri[𝕜](epi[s] f) = {p : E × 𝕜 | p.1 ∈ ri[𝕜](s ∩ dom(f)) ∧ f p.1 < p.2} := by
  ext p
  simpa using (Function.IsConvexOn.mem_ri_epi_restrict_iff (f := f) (s := s) hf (p := p))

end Function.IsConvexOn

namespace Function.IsConvex

@[simp] theorem mem_ri_epi_iff
    {f : E → WithTopBot 𝕜} (hf : Function.IsConvex 𝕜 f) {p : E × 𝕜} :
    p ∈ ri[𝕜](epi f) ↔
      p.1 ∈ riDom[𝕜](f) ∧ f p.1 < p.2 := by
  rcases p with ⟨x, μ⟩
  have hmem :
      (x, μ) ∈ ri[𝕜](epi f) ↔
        x ∈ ri[𝕜](Prod.fst '' epi f) ∧ μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi f) :=
    hf.mem_ri_iff_mem_ri_base_and_fiber
  rw [← effectiveDomain_eq_image_fst_epi (f := f)] at hmem
  have hUpper :
      μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔ f x < μ := by
    have hUpper' :
        μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔ μ ∈ {r : 𝕜 | f x < r} := by
      simpa using congrArg (fun t : Set 𝕜 => μ ∈ t) (ri_preimage_coe_Ici (a := f x))
    simpa using hUpper'
  constructor
  · intro hxμ
    rcases hmem.mp hxμ with ⟨hx, hμ⟩
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := by
      simpa [epi] using hμ
    exact ⟨hx, hUpper.mp hμ'⟩
  · rintro ⟨hx, hlt⟩
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := hUpper.mpr hlt
    have hμ : μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi f) := by
      simpa [epi] using hμ'
    exact hmem.mpr ⟨hx, hμ⟩

theorem ri_epi_eq
    {f : E → WithTopBot 𝕜} (hf : Function.IsConvex 𝕜 f) :
    ri[𝕜](epi f) = {p : E × 𝕜 | p.1 ∈ riDom[𝕜](f) ∧ f p.1 < p.2} := by
  ext p
  simpa using (Function.IsConvex.mem_ri_epi_iff (f := f) hf (p := p))

end Function.IsConvex

end
