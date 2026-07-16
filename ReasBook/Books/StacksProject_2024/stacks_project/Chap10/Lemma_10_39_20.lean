import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v

/- Domain-style sampling for Lemma 10.39.20:
- primary domain: filtered colimits of commutative `R`-algebras in `Under (CommRingCat.of R)`;
- sampled owner declarations:
  `RingHom.FaithfullyFlat`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `PrimeSpectrum.comap_surjective_of_faithfullyFlat`,
  `flat_of_isColimit_filtered_system`;
- best owner abstraction: filtered-colimit stability of the morphism property
  `fun f : A ⟶ B ↦ (hom f).FaithfullyFlat`, with the source-facing `Under` theorem below as a
  wrapper around that owner statement;
- primitive data: a filtered diagram `F`, a colimit cocone `c`, and the stagewise owner property
  `(hom (F.obj j).hom).FaithfullyFlat`;
- derived API: the source-facing cocone-point and chosen-colimit faithful-flatness conclusions.

Source/core/bridge triage:
- `source-facing`: faithful flatness of the structural map of a filtered colimit `R`-algebra;
- `core/canonical`: `RingHom.FaithfullyFlat` organized as a morphism property stable under filtered
  colimits;
- `bridge/view`: the `Under (CommRingCat.of R)` presentation, whose underlying ring diagram is the
  target of the owner stability statement.
-/

section

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ Under (CommRingCat.of R))

namespace RingHom.FaithfullyFlat

-- Proof sketch: use `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`. For flatness, forget
-- the diagram to `R`-modules and apply Lemma `10.39.3` to the underlying filtered colimit. For
-- surjectivity on prime spectra, pick any stage and lift a prime of `R` there via
-- `PrimeSpectrum.comap_surjective_of_faithfullyFlat`; then compose with the cocone map and rewrite
-- with `PrimeSpectrum.comap_comp_apply` and `Under.w`.
/-- Faithful flatness is stable under filtered colimits of commutative-ring morphisms. -/
instance isStableUnderFilteredColimits :
    CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits
      (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FaithfullyFlat) := by
  sorry

end RingHom.FaithfullyFlat

-- Proof sketch: view `F` as a natural transformation from the constant `R`-diagram to its
-- underlying `CommRingCat` diagram, then apply the owner instance
-- `RingHom.FaithfullyFlat.isStableUnderFilteredColimits`.
/-- Lemma 10.39.20: if `c` is a colimit cocone of a filtered diagram of faithfully flat
commutative `R`-algebras, then its cocone point is faithfully flat over `R`. This is the
canonical filtered-diagram formulation in `Under (CommRingCat.of R)`. -/
theorem faithfullyFlat_of_isColimit_filtered_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom c.pt.hom).FaithfullyFlat := by
  let cG := (Under.forget (CommRingCat.of R)).mapCocone c
  have hcG : IsColimit cG := Limits.isColimitOfPreserves (Under.forget (CommRingCat.of R)) hc
  let c₀ : Cocone ((Functor.const J).obj (CommRingCat.of R)) :=
    Limits.constCocone J (CommRingCat.of R)
  letI : IsConnected J := IsFiltered.isConnected J
  have hc₀ : IsColimit c₀ := Limits.isColimitConstCocone J (CommRingCat.of R)
  let η : (Functor.const J).obj (CommRingCat.of R) ⟶ F ⋙ Under.forget (CommRingCat.of R) :=
    { app := fun j ↦ (F.obj j).hom
      naturality := fun {j j'} f ↦ by
        simpa using (Under.w (F.map f)).symm }
  have hη :
      CategoryTheory.MorphismProperty.functorCategory
        (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FaithfullyFlat) J η :=
    fun j ↦ hF j
  let W : CategoryTheory.MorphismProperty CommRingCat :=
    fun {A B} (f : A ⟶ B) ↦ (hom f).FaithfullyFlat
  have hW : W.IsStableUnderColimitsOfShape J := inferInstance
  refine hW.condition
      ((Functor.const J).obj (CommRingCat.of R))
      (F ⋙ Under.forget (CommRingCat.of R))
      c₀ cG hc₀ hcG η hη c.pt.hom ?_
  intro j
  change (c₀.ι.app j) ≫ c.pt.hom = η.app j ≫ cG.ι.app j
  simpa [c₀, cG, η] using (Under.w (c.ι.app j)).symm

/-- Companion form of Lemma 10.39.20 for the chosen colimit object `colimit F`. -/
theorem faithfullyFlat_colimit_of_filtered_system
    [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FaithfullyFlat) :
    (hom (colimit F).hom).FaithfullyFlat := by
  simpa using faithfullyFlat_of_isColimit_filtered_system F (colimit.cocone F)
    (colimit.isColimit F) hF

end
