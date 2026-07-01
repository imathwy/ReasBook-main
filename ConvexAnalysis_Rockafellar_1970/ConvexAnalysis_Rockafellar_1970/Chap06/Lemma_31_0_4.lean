import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_3

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {EStar : Type v} [AddCommMonoid EStar] [Module 𝕜 EStar] [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.4 is the all-polyhedral branch in Fenchel duality. This file keeps
  the qualification shape `riDom[𝕜](f) ∩ riDom[𝕜](g) ≠ ∅`.
- `core/canonical`: the reusable owners are `Function.IsConvex`, `Function.HasPolyhedralEpigraph`,
  `riDom[𝕜](·)`, `dom(·)`, `Function.IsProper`, and conjugate notation `f⋆` on the nondegenerate
  pairing layer `[HasLinearPairing E EStar 𝕜]`.
- `bridge/view`: the all-`riDom` qualification is reduced to the mixed qualification
  `riDom[𝕜](f) ∩ dom(g) ≠ ∅`, then the Chapter 31.0.3 mixed-qualification theorem is applied.

Primitive data vs derived API:
- primitive inputs for the canonical owner theorem: the functions `f`, `g`, convexity/properness
  data for `f`, polyhedrality data for `g`, pairing nondegeneracy, and the qualification point in
  `riDom[𝕜](f) ∩ riDom[𝕜](g)`;
- derived API kept here: the source scalar reparameterization
  `α = inf_x (f x - g x) ⟹ ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar`, and the source
  all-polyhedral `f` specialization;
- no extra wrapper owner is introduced: this file keeps the source-facing statement directly.

Layer target: `source-facing`, on the pairing-level canonical owner.
-/

/-- Canonical owner form of Lemma 31.0.4: if `f` is proper convex, `g` has polyhedral epigraph,
and `riDom[𝕜](f)` meets `riDom[𝕜](g)`, then the primal infimum `⨅ x, f x - g x` is bounded above
by a dual conjugate difference `g⋆ xStar - f⋆ xStar`. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  have hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty := by
    rcases hri with ⟨x, hxri⟩
    exact ⟨x, hxri.1, intrinsicInterior_subset hxri.2⟩
  exact
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri_dom hpair_nondegenerate

/-- Reparameterized form of Lemma 31.0.4 at scalar value `α = inf_x (f x - g x)` under the same
all-`riDom` qualification shape. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_riDom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  rcases
      exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
        hf_convex hf_proper hg_poly hri hpair_nondegenerate with
    ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

/-- Lemma 31.0.4 (source all-polyhedral specialization): if `f` and `g` are polyhedral
`WithTopBot 𝕜`-valued functions, `f` is proper, and `riDom[𝕜](f)` meets `riDom[𝕜](g)`, then any
scalar reparameterization `α = inf_x (f x - g x)` is dominated by a dual conjugate difference
`g⋆ xStar - f⋆ xStar`. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_poly : f.HasPolyhedralEpigraph)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hf_proper : f.IsProper)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  exact
    exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_riDom_nonempty_of_polyhedral
      hf_poly.isConvex hf_proper hg_poly hri hpair_nondegenerate hα

end
