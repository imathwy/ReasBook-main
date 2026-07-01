import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty Limits
open CategoryTheory.Under
open CommRingCat
open CommRingCat.Hom

universe u v

section

/- Domain triage:
- primary domain: filtered colimits of commutative `R`-algebras in `Under (CommRingCat.of R)`;
- sampled owner declarations:
  * `RingHom.FormallyUnramified`
  * `RingHom.FormallyUnramified.stableUnderComposition`
  * `RingHom.FormallyUnramified.isStableUnderBaseChange`
  * `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`
- layer of this file: `bridge/view`;
- primitive data: a filtered diagram `F`, a colimit cocone `c`, and the stagewise owner property
  `RingHom.FormallyUnramified (F.obj j).hom.hom`;
- derived API: the cocone-point and chosen-colimit conclusions below.
-/

variable {R : Type u} [CommRing R]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ Under (CommRingCat.of R))

namespace RingHom.FormallyUnramified

/-- Formal unramifiedness is stable under filtered colimits of commutative-ring morphisms. -/
instance isStableUnderFilteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits
      (fun {A B : CommRingCat} (f : A ⟶ B) ↦ (hom f).FormallyUnramified) := by
  sorry

end RingHom.FormallyUnramified

-- Proof sketch: formal unramifiedness is the injectivity statement for lifting across square-zero
-- extensions. A map from the colimit `R`-algebra is determined by its composites with the stage
-- maps, and every element of the colimit comes from some stage because the index preorder is
-- directed. Hence two lifts that agree modulo a square-zero ideal already agree on each stage, so
-- the stagewise uniqueness hypotheses force them to coincide on the colimit.
/-- Lemma 10.148.6: in a directed system of commutative `R`-algebras, if every stage map
`R → S i` is formally unramified, then any colimit `R`-algebra of the system is formally
unramified over `R`. This is stated in the canonical category `Under (CommRingCat.of R)` of
commutative `R`-algebras. -/
theorem formallyUnramified_of_isColimit_filtered_system
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).FormallyUnramified) :
    (hom c.pt.hom).FormallyUnramified := by
  let W : MorphismProperty CommRingCat := fun {A B} (f : A ⟶ B) ↦ (hom f).FormallyUnramified
  let cG := (Under.forget (CommRingCat.of R)).mapCocone c
  have hcG : IsColimit cG := isColimitOfPreserves (Under.forget (CommRingCat.of R)) hc
  let c₀ : Cocone ((Functor.const J).obj (CommRingCat.of R)) :=
    constCocone J (CommRingCat.of R)
  letI : IsConnected J := IsFiltered.isConnected J
  have hc₀ : IsColimit c₀ := isColimitConstCocone J (CommRingCat.of R)
  let η : (Functor.const J).obj (CommRingCat.of R) ⟶ F ⋙ Under.forget (CommRingCat.of R) :=
    { app := fun j ↦ (F.obj j).hom
      naturality := fun {j j'} f ↦ by
        simpa using (Under.w (F.map f)).symm }
  have hη : W.functorCategory J η :=
    fun j ↦ hF j
  have hW : W.IsStableUnderColimitsOfShape J := inferInstance
  refine hW.condition
      ((Functor.const J).obj (CommRingCat.of R))
      (F ⋙ Under.forget (CommRingCat.of R))
      c₀ cG hc₀ hcG η hη c.pt.hom ?_
  intro j
  change (c₀.ι.app j) ≫ c.pt.hom = η.app j ≫ cG.ι.app j
  simpa [c₀, cG, η] using (Under.w (c.ι.app j)).symm

/-- Companion form of Lemma 10.148.6 for the chosen colimit object `colimit F`. -/
theorem formallyUnramified_colimit_of_filtered_system
    [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).FormallyUnramified) :
    (hom (colimit F).hom).FormallyUnramified := by
  simpa using formallyUnramified_of_isColimit_filtered_system F (colimit.cocone F)
    (colimit.isColimit F) hF

end
