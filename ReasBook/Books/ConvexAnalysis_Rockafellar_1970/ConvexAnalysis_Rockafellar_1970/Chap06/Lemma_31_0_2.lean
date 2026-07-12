import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable {E : Type u} {EStar : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommMonoid EStar] [Module 𝕜 EStar]
variable [HasLinearPairing E EStar 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 31.0.2 records the dual-attainment implication for the Fenchel
  pair from the relative-interior qualification
  `riDom[𝕜](f) ∩ riDom[𝕜](g) ≠ ∅`, first at the
  primal-value layer `⨅ x, f x - g x` and then at a named codomain value `α`.
- `core/canonical`: this revised item is narrowed to the proved polyhedral branch on the Chapter 31
  linear-pairing owner `[HasLinearPairing E EStar 𝕜]`, with the dual witness carrier exposed
  directly as `EStar`.
- `bridge/view`: the second theorem is only the codomain-value reparameterization of the first
  theorem, not an independent payload assumption.

Primary mathematical domain:
- finite-dimensional Fenchel duality on the nondegenerate linear-pairing owner
  `HasLinearPairing E EStar 𝕜`.

Domain-style sampling used here:
- `riDom` from `Chap01/Definition_4_4`;
- dual witnesses in `EStar`;
- the Fenchel conjugate owner `(·)⋆` from `Chap03/Defn_12_2`;
- `exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral` from
  `Chap06/Lemma_31_0_4`, used as the proved canonical owner-level bridge.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, and the qualification point in
  `riDom[𝕜](f) ∩ riDom[𝕜](g)`, together with the polyhedral and pairing-nondegeneracy inputs;
- derived API: existence of a dual witness for the conjugate inequality, and its
  reparameterization along a named value `α`.
-/

/-- Narrowed, proved owner-level primal-value form of Lemma 31.0.2 on the
`WithTopBot 𝕜` linear-pairing polyhedral layer with canonical pairing nondegeneracy
`PairingNondegenerate`. -/
theorem exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate) :
    ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar := by
  exact
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_riDom_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri hpair_nondegenerate

/-- Derived codomain-value reparameterization of the narrowed Lemma 31.0.2 form. -/
theorem exists_conjugate_difference_ge_of_iInf_sub_eq_of_riDom_inter_nonempty_of_polyhedral
    {f g : E → WithTopBot 𝕜}
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper)
    (hg_poly : g.HasPolyhedralEpigraph)
    (hri : (riDom[𝕜](f) ∩ riDom[𝕜](g)).Nonempty)
    (hpair_nondegenerate : PairingNondegenerate)
    {α : WithTopBot 𝕜} (hα : (⨅ x : E, f x - g x) = α)
    : ∃ xStar : EStar, α ≤ g⋆ xStar - f⋆ xStar := by
  have hmain : ∃ xStar : EStar, (⨅ x : E, f x - g x) ≤ g⋆ xStar - f⋆ xStar :=
    exists_conjugate_difference_ge_iInf_sub_of_riDom_inter_nonempty_of_polyhedral
      hf_convex hf_proper hg_poly hri hpair_nondegenerate
  rcases hmain with ⟨xStar, hxStar⟩
  exact ⟨xStar, hα ▸ hxStar⟩

end
