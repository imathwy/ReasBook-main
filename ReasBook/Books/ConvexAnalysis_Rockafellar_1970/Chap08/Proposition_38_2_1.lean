import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_24
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Proposition_6_29_2
import ConvexAnalysis_Rockafellar_1970.Chap08.Definition_38_0_1
import ConvexAnalysis_Rockafellar_1970.Chap08.Theorem_38_1

noncomputable section

open Function
open scoped Rockafellar

namespace Bifunction

section

universe u v

variable {U : Type u} {X : Type v}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

local notation "ri(" C ")" => intrinsicInterior ℝ C

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.2.1 compares the graph closure of the bifunction infimal
  convolution `F₁ D F₂` with the ordinary lower-semicontinuous hull of the slice
  `(F₁ u) □ (F₂ u)` at parameter values `u` in the relative interior of the bifunction domain.
- `core/canonical`: the existing owners are `Bifunction.infimalConvolution` with notation `D`,
  `Bifunction.dom`, `Bifunction.closure`, and the Chapter 2 function closure owner `cl(·)`.
- `bridge/view`: `cl F` is defined by graph closure and currying, so the proposition is a
  slice theorem relating that source-facing owner to the one-variable closure owner `cl(·)` on
  the slicewise infimal convolution.

Domain-style sampling used here:
- `Bifunction.closure` and `Bifunction.uncurry_closure` from `Chap06.Definition_6_29_24`;
- `Bifunction.uncurry_infimalConvolution_isConvex` and
  `Bifunction.dom_infimalConvolution_eq_inter` from `Chap08.Theorem_38_1`;
- `Bifunction.convex_dom` from `Chap06.Proposition_6_29_2`;
- `Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior` from `Chap02.Theorem_6_5`.

Primitive data vs derived API:
- primitive source data: convex bifunctions `F₁` and `F₂`;
- primitive owners reused directly: `F₁ D F₂`, `dom (F₁ D F₂)`, and
  `cl ((F₁ u) □ (F₂ u))`;
- source-facing closure owner reused directly: `cl (F₁ D F₂)`;
- derived API: the bridge reformulation from the source-facing qualification
  `u ∈ ri(dom F₁) ∩ ri(dom F₂)` to the owner-side qualification
  `u ∈ ri(dom (F₁ D F₂))`.

Codomain normalization:
- this item uses the chapter's canonical codomain `WithBotTop ℝ` rather than the alias `EReal`,
  because the closure, domain, and infimal-convolution owners imported here already live on that
  canonical layer.

Layer target: `source-facing`, stated directly on the existing bifunction owners and the canonical
one-variable closure owner.
-/

-- Proof sketch: first use `uncurry_infimalConvolution_isConvex` to see that `F₁ D F₂` is again a
-- convex bifunction on `U × X`. Then apply the chapter theorem identifying the graph closure of a
-- convex bifunction with the lower-semicontinuous hull of each slice on `ri(dom (F₁ D F₂))`,
-- and finally rewrite the slice `(F₁ D F₂) u` as `(F₁ u) □ (F₂ u)`.
/-- Bridge lemma: under the owner-side qualification `u ∈ ri (dom (F₁ D F₂))`, the `u`-slice of
the bifunction closure of the infimal convolution equals the lower-semicontinuous hull of the
slicewise infimal convolution. -/
theorem closure_infimalConvolution_slice_eq_sliceClosure_of_mem_ri_dom
    {F₁ F₂ : U → X → WithBotTop ℝ}
    (hF₁_convex : (uncurry F₁).IsConvex ℝ)
    (hF₂_convex : (uncurry F₂).IsConvex ℝ)
    {u : U} (hu : u ∈ ri(dom (F₁ D F₂))) :
    cl (F₁ D F₂) u = cl((F₁ u) □ (F₂ u)) := sorry

-- Proof sketch: identify `dom (F₁ D F₂)` with `dom F₁ ∩ dom F₂` through Theorem 38.1. Because
-- both domains are convex, Theorem 6.5 upgrades the source-facing hypothesis
-- `u ∈ ri(dom F₁) ∩ ri(dom F₂)` to `u ∈ ri(dom (F₁ D F₂))`. Then apply the bridge lemma above.
/-- Proposition 38.2.1: if `u ∈ ri (dom F₁) ∩ ri (dom F₂)`, then the `u`-slice of the bifunction
closure of `F₁ D F₂` equals the lower-semicontinuous hull of the slicewise infimal convolution
`(F₁ u) □ (F₂ u)`. -/
theorem closure_infimalConvolution_slice_eq_sliceClosure_of_mem_inter_ri_dom
    {F₁ F₂ : U → X → WithBotTop ℝ}
    (hF₁_convex : (uncurry F₁).IsConvex ℝ)
    (hF₂_convex : (uncurry F₂).IsConvex ℝ)
    {u : U} (hu : u ∈ ri(dom F₁) ∩ ri(dom F₂)) :
    cl (F₁ D F₂) u = cl((F₁ u) □ (F₂ u)) := by
  have hF₁_slice_convex : ∀ u, (F₁ u).IsConvex ℝ := hF₁_convex.slice_uncurry
  have hF₂_slice_convex : ∀ u, (F₂ u).IsConvex ℝ := hF₂_convex.slice_uncurry
  have hF₁_dom_convex : Convex ℝ (dom F₁) := convex_dom hF₁_convex
  have hF₂_dom_convex : Convex ℝ (dom F₂) := convex_dom hF₂_convex
  have hri_inter :
      ri(dom F₁ ∩ dom F₂) = ri(dom F₁) ∩ ri(dom F₂) := by
    let C : Bool → Set U := fun b ↦ cond b (dom F₁) (dom F₂)
    have hC_convex : ∀ b : Bool, Convex ℝ (C b) := by
      intro b
      cases b
      · simpa [C] using hF₂_dom_convex
      · simpa [C] using hF₁_dom_convex
    have hC_ri : (⋂ b : Bool, ri(C b)).Nonempty := by
      refine ⟨u, Set.mem_iInter.2 ?_⟩
      intro b
      cases b
      · simpa [C] using hu.2
      · simpa [C] using hu.1
    calc
      ri(dom F₁ ∩ dom F₂) = ri(⋂ b : Bool, C b) := by
        rw [Set.inter_eq_iInter]
      _ = ⋂ b : Bool, ri(C b) := by
        simpa [C] using
          Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior hC_convex hC_ri
      _ = ri(dom F₁) ∩ ri(dom F₂) := by
        ext x
        constructor
        · intro hx
          exact ⟨by simpa [C] using (Set.mem_iInter.1 hx) true,
            by simpa [C] using (Set.mem_iInter.1 hx) false⟩
        · rintro ⟨hx₁, hx₂⟩
          refine Set.mem_iInter.2 fun b ↦ ?_
          cases b
          · simpa [C] using hx₂
          · simpa [C] using hx₁
  have hu' : u ∈ ri(dom (F₁ D F₂)) := by
    rw [dom_infimalConvolution_eq_inter hF₁_slice_convex hF₂_slice_convex, hri_inter]
    exact hu
  exact closure_infimalConvolution_slice_eq_sliceClosure_of_mem_ri_dom
    hF₁_convex hF₂_convex hu'

end

end Bifunction
