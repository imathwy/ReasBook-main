import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_19_0_8

noncomputable section

open scoped Rockafellar

/-- Canonical owner alias for pairing nondegeneracy: reuse
`HasLinearPairing.Nondegenerate` directly on the chapter theorem surface. -/
abbrev PairingNondegenerate
    {𝕜 : Type*} [CommSemiring 𝕜]
    {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    {EStar : Type*} [AddCommMonoid EStar] [Module 𝕜 EStar]
    [HasLinearPairing E EStar 𝕜] : Prop :=
  HasLinearPairing.Nondegenerate E EStar 𝕜

section

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {EStar : Type*} [AddCommMonoid EStar] [Module 𝕜 EStar] [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.3 is the Fenchel-duality separation clause where `g` is polyhedral:
  if `f` is proper convex, `g` is polyhedral convex, `riDom(f)` meets `dom(g)`, and
  `α = inf_x (f x - g x)` is finite, then some dual point `xStar` satisfies
  `g⋆ xStar - f⋆ xStar ≥ α`.
- `core/canonical`: the chapter owners are `Function.IsConvex`, `Function.IsProper`,
  `Function.HasPolyhedralEpigraph`, `dom(·)`, `riDom(·)`, and `convexConjugate` notation `f⋆`.
- `bridge/view`: following the Chapter 31 pattern from Lemma 31.0.2, the owner-level payload is
  first exposed directly at the canonical value `⨅ x, f x - g x`, and the source scalar `α`
  then appears only in a thin reparameterization companion.

Domain-style sampling used here:
- `Function.HasPolyhedralEpigraph` from `Chap04.Text_19_0_8`;
- `Function.HasPolyhedralEpigraph.isClosedProperConvex` from `Chap04.Corollary_19_1_2`;
- `Set.IsPolyhedral.exists_hyperplane_strongly_separating_of_disjoint_nonempty` from
  `Chap04.Corollary_19_3_3`;
- `Set.IsPolyhedral.exists_separator_not_subset_right_iff_disjoint_ri` from
  `Chap04.Theorem_20_2`.

Primitive data vs derived API:
- primitive inputs: `f`, `g`, the convex/proper owner data for `f`, the polyhedral owner data for
  `g`, the mixed qualification point in `riDom[𝕜](f) ∩ dom(g)`, and the scalar primal-value
  witness `hα`, together with the pairing nondegeneracy owner `PairingNondegenerate`;
- derived API: existence of a dual point `xStar` satisfying the conjugate inequality
  `α ≤ g⋆ xStar - f⋆ xStar`.

Layer target: `source-facing`.

Ambient refinement:
- unlike the purely `riDom`-based Lemma 31.0.2, this polyhedral branch is justified in the
  repository through the Chapter 19/20 polyhedral closedness and separation owners, which live on
  finite-dimensional topological modules over an ordered topological field with linear pairing
  data;
- Chapter 20's separation owner
  `Set.IsPolyhedral.exists_separator_not_subset_right_iff_disjoint_ri`
  also requires the pairing nondegeneracy owner `PairingNondegenerate` (equivalently,
  injectivity of `HasLinearPairing.pairingLinear`), and without it the present
  Fenchel-duality statement is false;
- the main theorem therefore lives on the actual nondegenerate pairing owner
  `HasLinearPairing E EStar 𝕜`, rather than collapsing the dual variable to a self-pairing
  ambient copy of `E`.
-/

-- Proof sketch: form the translated hypograph set
-- `D = {(x, μ) | μ ≤ g x + α}` and separate it from the epigraph of `f` by the polyhedral
-- separation theorem. The qualification hypothesis excludes a vertical separator because
-- `riDom[𝕜](f)` meets `dom(g)`. Writing the resulting affine separator as
-- `μ = ⟪x, xStar⟫ₚ - αStar`, the same conjugate inequalities as in Lemma 31.0.2 give
-- `f⋆ xStar ≤ αStar` and `αStar + α ≤ g⋆ xStar`, hence `α ≤ g⋆ xStar - f⋆ xStar`.
/-- Owner-level payload for Lemma 31.0.3 on the canonical `WithTopBot 𝕜`
polyhedral-duality layer. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  sorry

/-- Lemma 31.0.3 (polyhedral `g` form): for proper convex `f` and polyhedral convex `g`, if
`riDom[𝕜](f)` meets `dom(g)` and `α = inf_x (f x - g x)` in `WithTopBot 𝕜`, then some dual
point `xStar` in the pairing-side space `EStar` satisfies `g⋆ xStar - f⋆ xStar ≥ α`, provided the
Chapter 20 pairing nondegeneracy owner `PairingNondegenerate`. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_dom_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri_dom : (riDom[𝕜](f) ∩ dom(g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α) :
    ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  rcases
      exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_dom_nonempty_of_polyhedral
        hf_convex hf_proper hg_poly hri_dom hpair_nondegenerate with
    ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

end
