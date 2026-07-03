import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_9_5 (from Chap02) -/
open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 9.5 studies precomposition `g ∘ A` of a convex function with a
  linear map, keeping the closedness clause as direct owner recall and adding the recession and
  closure formulas for the composed function.
- `core/canonical`: the owner abstractions already present in the project are
  `LowerSemicontinuous` for closedness, `Function.IsConvex` for convexity, the primitive
  codomain-side condition `∀ z, g z ≠ ⊥` for excluding `-∞`, `Function.recessionFunction`
  for `g₀⁺`, and
  `lowerSemicontinuousHull` for Rockafellar's closure `cl g`.
- `bridge/view`: the textbook phrases `A⁻¹(dom g) ≠ ∅` and `A⁻¹(ri dom g) ≠ ∅` are represented
  directly by the canonical owner hypotheses
  `(A ⁻¹' dom(g)).Nonempty` and `(A ⁻¹' riDom[𝕜](g)).Nonempty`.

Domain-style sampling used here:
- `LowerSemicontinuous.comp` from mathlib's semicontinuity API;
- `Function.IsConvex.comp_linearMap` from the chapter's composition owner API;
- `Function.IsConvex.cl_eq_of_riDom_eq_and_eqOn` from
  Corollary 7.3.4;
- the linear-preimage geometry owners from Chapter 6, namely
  `Convex.recessionCone_linear_preimage`, `Convex.intrinsicInterior_linear_preimage`, and
  `Convex.closure_linear_preimage`.

Primitive data vs derived API:
- primitive inputs: the linear map `A` and the function `g`;
- derived API: the owner-level closedness transfer for `g ∘ A`, together with the
  recession-function identity and the lower-semicontinuous-hull identity under the
  relative-interior nonemptiness condition.
- Ambient-space refinement: clause (2) only needs the module/topological layer already used by
  `recessionCone_linear_preimage`, so it is separated from clause (3), which genuinely needs the
  finite-dimensional ordered normed-field layer coming from the relative-interior/closure owners.
- Best owner abstraction: clause (1) is a direct recall on the ambient owner
  `LowerSemicontinuous`, while the genuinely new convexity-driven clauses belong on the canonical
  owner namespace `Function.IsConvex` rather than in an extra chapter-local wrapper namespace.
- Layer target: `source-facing`, with clause (1) kept as a pure canonical recall and clauses (2)
and (3) retained as the source-facing composition formulas because no earlier project theorem
already exposes those exact owner-level identities.
-/

section Closedness

/- Theorem 9.5 (1): precomposition of a lower-semicontinuous `WithTopBot 𝕜`-valued function with
a continuous map is the canonical owner theorem `LowerSemicontinuous.comp`. -/
recall LowerSemicontinuous.comp

end Closedness

namespace Function.IsConvex

section Recession

variable
    {𝕜 E F : Type*}
    [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜]
    [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
    [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]

variable (A : E →ₗ[𝕜] F) (g : F → WithTopBot 𝕜)

/-- Theorem 9.5 (2): if `g` is convex, closed, nowhere `⊥`, `A` is continuous linear, and
`g ∘ A` takes some finite value, represented by `(A ⁻¹' dom(g)).Nonempty`, then the
recession function of `g ∘ A` is the composite of the recession function of `g` with `A`. -/
-- Proof sketch: Theorem 5.7 gives convexity of `g ∘ A`, while part (1) gives its closedness.
-- Apply Corollary 8.3.4 to the scalar epigraph of `g`; since `epi (g ∘ A)` is the linear preimage
-- of `epi g` under `(x, μ) ↦ (A x, μ)`, the corresponding recession cones agree by preimage.
-- Reading off the vertical-infimum descriptions of those cones yields
-- `(g ∘ A)₀⁺ = g₀⁺ ∘ A`.
theorem recessionFunction_comp_linearMap_eq
    (hg_convex : g.IsConvex 𝕜)
    (hA_cont : Continuous A)
    (hg_ne_bot : ∀ z, g z ≠ (⊥ : WithTopBot 𝕜))
    (hg_closed : LowerSemicontinuous g)
    (hdom : (A ⁻¹' dom(g)).Nonempty) :
    (g ∘ A)₀⁺ = g₀⁺ ∘ A := by
  rcases hdom with ⟨x, hx⟩
  have hcomp_convex : (g ∘ A).IsConvex 𝕜 :=
    hg_convex.comp_linearMap A
  have hcomp_ne_bot : ∀ z, (g ∘ A) z ≠ (⊥ : WithTopBot 𝕜) := by
    intro z
    simpa [Function.comp] using hg_ne_bot (A z)
  have hcomp_closed : LowerSemicontinuous (g ∘ A) :=
    hg_closed.comp hA_cont
  ext y
  change Function.recessionFunction (g ∘ A) y = Function.recessionFunction g (A y)
  have hleft :=
    Function.recessionFunction_eq_sSup_differenceQuotients_at_point
      (g ∘ A) hcomp_convex hcomp_ne_bot hcomp_closed hx y
  have hright :=
    Function.recessionFunction_eq_sSup_differenceQuotients_at_point
      g hg_convex hg_ne_bot hg_closed hx (A y)
  rw [hleft, hright]
  simp [Function.comp, map_add, map_smul]

end Recession

section LowerSemicontinuousHull

variable
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]

variable (A : E →ₗ[𝕜] F) (g : F → WithTopBot 𝕜)

/-- Theorem 9.5 (3): if `g` is convex and `(A ⁻¹' riDom[𝕜](g)).Nonempty`, then the closure of
`g ∘ A` is the composite of the closure `cl(g)` with `A`. -/
-- Proof sketch: use Lemma 7.3 to rewrite the relative interior of the scalar epigraph of `g` in
-- terms of `riDom[𝕜](g)`. The hypothesis exactly says that the linear
-- preimage of that relative interior is nonempty, so Theorem 6.7 applies to the epigraph of `g`
-- and identifies the closure of `epi (g ∘ A)` with the preimage of `closure (epi g)`. Equivalently,
-- this is the linear-preimage specialization of the chapter owner theorem
-- `cl_eq_of_riDom_eq_and_eqOn`, with the geometry of the
-- effective domains supplied by Theorem 6.7. Translating that epigraph-closure identity back to
-- functions gives the hull formula.
theorem lowerSemicontinuousHull_comp_linearMap_eq
    (hg_convex : g.IsConvex 𝕜)
    (hri : (A ⁻¹' riDom[𝕜](g)).Nonempty) :
    cl(g ∘ A) = cl(g) ∘ A := by
  let L : E × 𝕜 →ₗ[𝕜] F × 𝕜 := A.prodMap (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜)
  have hepi_preimage : epi (g ∘ A) = L ⁻¹' epi g := by
    ext p
    rcases p with ⟨x, μ⟩
    simp [L, Function.comp]
  rcases hri with ⟨x, hx⟩
  have hx_dom : A x ∈ dom(g) := intrinsicInterior_subset hx
  rcases WithBotTop.exists_between_coe_of_lt (show g (A x) < ⊤ from hx_dom) with ⟨μ, hxμ, _⟩
  have hri_epi : (L ⁻¹' intrinsicInterior 𝕜 (epi g)).Nonempty := by
    refine ⟨(x, μ), ?_⟩
    change (A x, μ) ∈ intrinsicInterior 𝕜 (epi g)
    exact
      (hg_convex.mem_ri_epi_iff).2
        ⟨hx, hxμ⟩
  have hconv_epi : Convex 𝕜 (epi g) := by
    simpa [epi] using hg_convex.convex_epigraph
  have hclosure_preimage : closure (L ⁻¹' epi g) = L ⁻¹' closure (epi g) :=
    Convex.closure_linear_preimage hconv_epi L hri_epi
  have hpreimage_closure_epi : L ⁻¹' closure (epi g) = epi (cl(g) ∘ A) := by
    ext p
    rcases p with ⟨x, μ⟩
    constructor
    · intro hp
      have hp' : (A x, μ) ∈ epi cl(g) := by
        rw [← closure_epi_eq_epi_lowerSemicontinuousHull]
        simpa [L] using hp
      simpa [L, Function.comp] using hp'
    · intro hp
      have hp' : (A x, μ) ∈ epi cl(g) := by
        simpa [L, Function.comp] using hp
      rw [← closure_epi_eq_epi_lowerSemicontinuousHull] at hp'
      simpa [L] using hp'
  have hclosure_epi : closure (epi (g ∘ A)) = epi (cl(g) ∘ A) := by
    calc
      closure (epi (g ∘ A)) = closure (L ⁻¹' epi g) := by rw [hepi_preimage]
      _ = L ⁻¹' closure (epi g) := hclosure_preimage
      _ = epi (cl(g) ∘ A) := hpreimage_closure_epi
  have hepi : epi cl(g ∘ A) = epi (cl(g) ∘ A) := by
    calc
      epi cl(g ∘ A) = closure (epi (g ∘ A)) := by
        simpa using (closure_epi_eq_epi_lowerSemicontinuousHull (g ∘ A)).symm
      _ = epi (cl(g) ∘ A) := hclosure_epi
  simpa using congrArg Function.verticalInfimum hepi

end LowerSemicontinuousHull

end Function.IsConvex
