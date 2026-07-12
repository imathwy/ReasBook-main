import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits

section

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v u}} {C : Cone F}
variable [∀ j : J, SpectralSpace (F.obj j)]

/- Domain-style sampling for constructible descent in cofiltered limits of spectral spaces:
- primary domain: constructible subsets, compact opens, and spectral maps in inverse limits of
  spectral spaces;
- sampled owner-level declarations:
  `Topology.IsConstructible.empty_union_induction`,
  `IsSpectralMap.isConstructible_preimage`,
  `compact_open_eq_preimage_of_isLimit`,
  `spectralSpace_of_isLimit_of_cofiltered_spectral_diagram`;
- best owner abstraction: the predicate `Topology.IsConstructible` on subsets, together with the
  canonical `CompactOpens` owner for open constructible subsets and `Closeds` for the closed
  companion case;
- primitive-vs-derived split:
  primitive data: a subset of the limit together with the owner predicate `IsConstructible`;
  derived API: the compact-open and closed refinements of the descended stage subset.

Layer triage:
- `source-facing`: a constructible subset of the limit comes via pullback from some stage;
- `core/canonical`: the owner predicate `Topology.IsConstructible`, together with the chapter-level
  compact-open descent theorem and spectral-limit owner for the ambient spaces;
- `bridge/view`: the open and closed companion forms, which should use `CompactOpens` and
  `Closeds` rather than storing openness or closedness as primitive fields.
-/

-- Proof sketch: argue first for constructible opens by upgrading them to compact opens on the
-- spectral limit and descending them with `compact_open_eq_preimage_of_isLimit`; then pass
-- to constructible closed sets by complements, and finally write a general constructible set as a
-- finite union of intersections of constructible open and constructible closed subsets, descend
-- each piece to some stage, and use cofilteredness to dominate the finitely many indices by a
-- single object.
/-- Lemma 5.24.4: a constructible subset of the limit of a cofiltered diagram of spectral spaces
with spectral transition maps comes by pullback from a constructible subset on some stage. -/
theorem constructible_eq_preimage_of_isLimit
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) :
    ∃ (i : J) (Ei : Set (F.obj i)), IsConstructible Ei ∧ C.π.app i ⁻¹' Ei = E := sorry

-- Proof sketch: once the limit is spectral, an open constructible subset is compact open; then
-- apply the chapter-level compact-open owner theorem `compact_open_eq_preimage_of_isLimit`
-- to descend it directly to a stagewise compact open.
/-- If the constructible subset in Lemma 5.24.4 is open, then the descended constructible subset
can be chosen compact open. -/
theorem open_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_open : IsOpen E) :
    ∃ (i : J) (Ei : CompactOpens (F.obj i)), C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := sorry

-- Proof sketch: apply the open case to the complement of the constructible closed subset `E`, then
-- take complements on the corresponding stage.
/-- If the constructible subset in Lemma 5.24.4 is closed, then the descended constructible subset
can be chosen closed. -/
theorem closed_eq_preimage_of_isLimit_of_isConstructible
    (hC : IsLimit C)
    (hF : ∀ ⦃i j : J⦄ (a : j ⟶ i), IsSpectralMap (F.map a))
    {E : Set C.pt}
    (hE : IsConstructible E) (hE_closed : IsClosed E) :
    ∃ (i : J) (Ei : Closeds (F.obj i)),
      IsConstructible (Ei : Set (F.obj i)) ∧ C.π.app i ⁻¹' (Ei : Set (F.obj i)) = E := sorry

end
