import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

universe u v

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable {F : I ⥤ TopCat.{max u v}} [∀ i : I, SpectralSpace ↥(F.obj i)]
variable {C : Cone F}

/- Domain-style sampling for cofiltered limits of spectral spaces:
- primary domain: inverse limits in `TopCat` of spectral spaces with spectral transition maps;
- sampled owner declarations:
  `SpectralSpace`,
  `IsSpectralMap`,
  `TopCat.isTopologicalBasis_cofiltered_limit`,
  `compact_open_eq_preimage_of_isLimit`;
- best owner abstraction: the cone-level spectrality theorem for an arbitrary limiting cone, with
  the chosen categorical limit treated only as derived inference support;
- primitive data: a cofiltered diagram `F`, spectral structures on the stages, a limiting cone
  `C`, and spectrality of the transition maps;
- derived API: spectrality of the limiting cone point and spectrality of its projection maps.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that an inverse limit of spectral spaces with spectral
  transition maps is spectral, together with the projection-map corollary;
- `core/canonical`: `SpectralSpace` and `IsSpectralMap` on the limiting cone data;
- `bridge/view`: the chosen-limit specialization, which should remain only an instance and not a
  second named owner theorem.
-/

-- Proof sketch: use the cofiltered-limit basis theorem in `TopCat` with the compact-open bases on
-- the stage spaces. The spectrality of the transition maps shows that pullbacks of compact opens
-- remain compact open, giving a compact-open basis on the limit; quasi-compactness comes from the
-- constructible-limit argument, and irreducible closed subsets get unique generic points by
-- passing to compatible generic points in the stages.
/-- Lemma 5.24.5: the inverse limit of a cofiltered diagram of spectral spaces with spectral
transition maps is a spectral topological space. -/
theorem spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (hC : IsLimit C)
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥C.pt := sorry

-- Proof sketch: once the limiting cone point is spectral, apply the compact-open description of
-- the cofiltered limit topology: any quasi-compact open in the limit is the pullback of a compact
-- open from a stage, and the inverse image of a compact open along a projection is exactly such a
-- basic compact open.
/-- Each projection from a limiting cone of a cofiltered diagram of spectral spaces is a spectral
map. -/
theorem isSpectralMap_projection_of_isLimit_of_cofiltered_spectral_diagram
    (hC : IsLimit C) (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) (i : I) :
    IsSpectralMap (C.π.app i) := sorry

instance
    (hF : ∀ ⦃j k : I⦄ (a : j ⟶ k), IsSpectralMap (F.map a)) :
    SpectralSpace ↥(limit F) :=
  spectralSpace_of_isLimit_of_cofiltered_spectral_diagram (limit.isLimit F) hF

end
