import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap07.Lemma_7_44_2
import stacks_proof.stacks_project.Chap18.Definition_18_32_1
import stacks_proof.stacks_project.Chap18.Definition_18_40_9
import stacks_proof.stacks_project.Chap18.Lemma_18_40_8
import stacks_proof.stacks_project.Chap18.Lemma_18_40_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits CartesianMonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory

open SheafOfModules.RingedSite
open scoped RingedSiteUnits

/- Domain-style sampling for Lemma 18.40.11:
- primary domain: inverse image for locally ringed sites, with the units construction tracked on
  the source-facing units sheaf owner `\mathcal O^*` and only secondarily on its underlying
  units subsheaf;
- sampled owner declarations:
  `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSheaf`,
  `ringedSiteUnitsSubsheaf`,
  `ringedSiteUnitsSheafUnderlyingIso`,
  `sheaf_pullback_forget`,
  `unitsSquareCartesianForLocallyRingedMorphism`,
  `pullback_isLocallyRingedSite`;
- best owner abstractions:
  the inverse-image structure sheaf itself should be spoken about through the Chapter 18 owner
  `inverseImageStructureSheafForLocallyRingedMorphism`;
  clause `(1)` is source-facing and should compare the actual inverse-image units sheaf
  `F^{-1}(\mathcal O^*)` with the units sheaf `(F^{-1}\mathcal O)^*` of the inverse-image
  structure sheaf; the underlying-`Type` subsheaf comparison is only the internal bridge, via
  `ringedSiteUnitsSheafUnderlyingIso` on both sides and the Chapter 7 forget-compatibility owner
  `sheaf_pullback_forget`;
  the Chapter 18 cartesian-units owner
  `inverseImageUnitsCartesianForLocallyRingedMorphism`, specialized to the identity map on
  `F^{-1}\mathcal O`, is only a bridge/view reformulation of that comparison;
  clause `(2)` is already exactly the canonical preservation theorem
  `pullback_isLocallyRingedSite`;
- primitive data:
  the site morphism `IsMorphismOfSites K J F` presenting the inverse-image functor and the
  commutative structure sheaf `𝒪`;
- derived API:
  the inverse-image comparison between units sheaves, the corresponding cartesian-units
  reformulation for the identity map on `F^{-1}\mathcal O`, and the pullback preservation of
  local ringedness.

Source/core/bridge triage:
- `source-facing`: the claim that inverse image carries the units sheaf of `𝒪` to the units
  sheaf of `F^{-1}\mathcal O`, i.e. `F^{-1}(\mathcal O^*) ≅ (F^{-1}\mathcal O)^*`;
- `core/canonical`: `inverseImageStructureSheafForLocallyRingedMorphism`,
  `ringedSiteUnitsSheaf`,
  `ringedSiteUnitsSheafUnderlyingIso`, and
  `pullback_isLocallyRingedSite`;
- `bridge/view`: `sheaf_pullback_forget`, identifying the pullback of the underlying sheaf of
  sets with the underlying sheaf of the pulled-back units sheaf or structure sheaf, and
  `inverseImageUnitsCartesianForLocallyRingedMorphism` for the later locally ringed-morphism
  reformulation.
-/

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (F : D ⥤ C) [IsMorphismOfSites K J F]
variable [((F.sheafPushforwardContinuous CommRingCat.{max u v} K J).IsRightAdjoint)]
variable (𝒪 : Sheaf K CommRingCat.{max u v})

/-- Helper for Lemma 18.40.11: for the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O`, the inverse-image units square is cartesian. -/
theorem pullback_inverseImageUnitsCartesian :
    inverseImageUnitsCartesianForLocallyRingedMorphism
      F
      ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})
      𝒪
      (𝟙 ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})) := by
  intro U
  change
    unitsSquareCartesianForLocallyRingedMorphism
      (RingHom.id
        (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
          Sheaf J CommRingCat.{max u v}).1.obj (op U)))
  rw [unitsSquareCartesian_iff_isLocalHom]
  exact isLocalHom_id _

-- Proof sketch: clause `(1)` is source-facing as an inverse-image comparison for units sheaves,
-- and the canonical Chapter 18 bridge records the equivalent cartesian-units formulation for the
-- identity map on `F^{-1}\mathcal O`.
/-- Lemma 18.40.11 (1), bridge form: the inverse image of the units sheaf of `\mathcal O`
identifies with the units sheaf of `F^{-1}\mathcal O`, expressed via the cartesianness of the
inverse-image units square for the identity map on `F^{-1}\mathcal O`. -/
@[stacks 04KR]
theorem pullback_inverseImageUnitsIso :
    inverseImageUnitsCartesianForLocallyRingedMorphism
      F
      ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})
      𝒪
      (𝟙 ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})) :=
  pullback_inverseImageUnitsCartesian F 𝒪

-- Proof sketch: clause `(1)` identifies the inverse image of the units subsheaf with the units
-- subsheaf of the pulled-back structure sheaf, while Lemma `18.40.5` supplies that
-- `F^{-1}\mathcal O` is locally ringed whenever `\mathcal O` is. Thus the site-presented
-- morphism of topoi with `f^\sharp = \mathrm{id}` satisfies the Chapter 18 locally ringed
-- morphism owner.
/-- Companion for Lemma 18.40.11 (2): if `(\mathcal C, \mathcal O)` is locally ringed, then the morphism of
topoi induced by `F` together with the identity map
`f^\sharp : F^{-1}\mathcal O \to F^{-1}\mathcal O` is a morphism of locally ringed topoi. -/
theorem pullback_isMorphismOfLocallyRingedTopoi
    [IsLocallyRingedSite 𝒪] :
    letI :
        IsLocallyRingedSite
          (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
            Sheaf J CommRingCat.{max u v})) :=
      pullback_isLocallyRingedSite F
    IsMorphismOfLocallyRingedTopoi
      F
      ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})
      𝒪
      (𝟙 ((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
        Sheaf J CommRingCat.{max u v})) := by
  letI :
      IsLocallyRingedSite
        (((inverseImageStructureSheafForLocallyRingedMorphism F 𝒪) :
          Sheaf J CommRingCat.{max u v})) :=
    pullback_isLocallyRingedSite F
  exact ⟨pullback_inverseImageUnitsIso F 𝒪⟩

end CategoryTheory
