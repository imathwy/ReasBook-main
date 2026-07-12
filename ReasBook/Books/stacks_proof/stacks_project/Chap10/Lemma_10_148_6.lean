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
  refine ⟨fun J _ _ ↦ ?_⟩
  refine ⟨fun X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ ↦ ?_⟩
  letI : Algebra c₁.pt c₂.pt := (hom φ).toAlgebra
  -- The source proof is stagewise uniqueness of infinitesimal lifts, then colimit extensionality.
  change (algebraMap c₁.pt c₂.pt).FormallyUnramified
  rw [RingHom.formallyUnramified_algebraMap]
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun B _ _ I hI g₁ g₂ hg ↦ ?_
  have hstage : ∀ j (x : X₂.obj j), g₁ ((hom (c₂.ι.app j)) x) = g₂ ((hom (c₂.ι.app j)) x) := by
    intro j x
    letI : Algebra (X₁.obj j) (X₂.obj j) := (hom (f.app j)).toAlgebra
    letI : Algebra (X₁.obj j) B := ((algebraMap c₁.pt B).comp (hom (c₁.ι.app j))).toAlgebra
    -- Each cocone leg packages a candidate global lift as a stagewise lift over `X₁.obj j`.
    let stageLift (g : c₂.pt →ₐ[c₁.pt] B) : X₂.obj j →ₐ[X₁.obj j] B :=
      { toRingHom := g.toRingHom.comp (hom (c₂.ι.app j))
        commutes' := fun y ↦ by
          -- The square `hφ j` identifies the stage algebra structure on the colimit leg.
          have hy :
              (hom (c₂.ι.app j)) ((hom (f.app j)) y) = (hom φ) ((hom (c₁.ι.app j)) y) := by
            exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hφ j)).symm y
          calc
            g ((hom (c₂.ι.app j)) ((hom (f.app j)) y))
                = g ((hom φ) ((hom (c₁.ι.app j)) y)) := by rw [hy]
            _ = algebraMap c₁.pt B ((hom (c₁.ι.app j)) y) := g.commutes _
            _ = ((algebraMap c₁.pt B).comp (hom (c₁.ι.app j))) y := rfl }
    have hfj : Algebra.FormallyUnramified (X₁.obj j) (X₂.obj j) := by
      have hfj' : (algebraMap (X₁.obj j) (X₂.obj j)).FormallyUnramified := by
        simpa [RingHom.algebraMap_toAlgebra] using hf j
      exact (RingHom.formallyUnramified_algebraMap (R := X₁.obj j) (S := X₂.obj j)).1 hfj'
    have hq :
        (Ideal.Quotient.mkₐ (X₁.obj j) I).comp (stageLift g₁) =
          (Ideal.Quotient.mkₐ (X₁.obj j) I).comp (stageLift g₂) := by
      -- The quotient equality of global lifts restricts to the same quotient equality on each stage.
      ext y
      simpa [stageLift] using AlgHom.congr_fun hg ((hom (c₂.ι.app j)) y)
    have hEq : stageLift g₁ = stageLift g₂ :=
      (Algebra.FormallyUnramified.iff_comp_injective.mp hfj) I hI hq
    exact congrFun (congrArg DFunLike.coe hEq) x
  -- A map out of the colimit is determined by its composites with the stage cocone legs.
  apply AlgHom.ext
  intro x
  have hglobal :
      CommRingCat.ofHom g₁.toRingHom = CommRingCat.ofHom g₂.toRingHom := by
    apply hc₂.hom_ext
    intro j
    apply CommRingCat.hom_ext
    ext y
    exact hstage j y
  have hring : g₁.toRingHom = g₂.toRingHom := by
    simpa using congrArg CommRingCat.Hom.hom hglobal
  exact congrFun (congrArg DFunLike.coe hring) x

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
@[stacks 07QE]
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
