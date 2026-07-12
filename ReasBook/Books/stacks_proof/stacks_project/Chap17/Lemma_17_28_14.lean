import Mathlib
import StacksProject_2024.Chap06.Definition_6_26_1
import StacksProject_2024.Chap17.Lemma_17_3_1
import StacksProject_2024.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.Chap17.Lemma_17_28_12
import StacksProject_2024.Chap17.Lemma_17_28_13

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y S : RingedSpace.{u}}

/- Domain-style sampling for Lemma 17.28.14:
- primary domain: the transitivity sequence for relative differentials of composable morphisms of
  ringed spaces;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.Ω[_]`,
  `AlgebraicGeometry.RingedSpace.pullbackDifferentialsComparison`,
  `SheafOfModules.pullbackId`,
  `CategoryTheory.ShortComplex`;
- best owner abstraction:
  the source-facing short complex
  `f^*Ω[g] → Ω[f ≫ g] → Ω[f] → 0`, built from the canonical base-change comparison
  `pullbackDifferentialsComparison` together with the canonical identity-pullback isomorphism
  `SheafOfModules.pullbackId`;
- primitive data:
  only the composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`;
- derived API:
  the two transitivity morphisms, the named short complex they define, and its exactness and
  epimorphy.

Source/core/bridge triage:
- `source-facing`: the transitivity short complex together with its two companion morphisms;
- `core/canonical`: `Ω[_]`, `pullbackDifferentialsComparison`, `SheafOfModules.pullbackId`, and
  `ShortComplex`;
- `bridge/view`: the identity-base-change square and the stalkwise exactness criterion used in the
  proof sketch.

The former theorem `modulePullback_id_obj_differentials_eq` was duplicate bridge data: the
identity pullback is already canonically owned by `SheafOfModules.pullbackId`, so the public
surface should use that owner directly. The source-facing owner in this file is therefore the
transitivity short complex itself, with the individual comparison maps as companion data. -/

/-- The canonical map `f^*Ω_{Y/S} → Ω_{X/S}` in the transitivity sequence for relative
differentials. -/
def relativeDifferentialsTransitivityLeft
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (RingedSpace.Hom.pullback f).obj Ω[g] ⟶ Ω[f ≫ g] :=
  pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩

/-- The canonical map `Ω_{X/S} → Ω_{X/Y}` in the transitivity sequence for relative differentials.
-/
def relativeDifferentialsTransitivityRight
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Ω[f ≫ g] ⟶ Ω[f] :=
  (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g] ≫
    pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩

/-- Helper for Lemma 17.28.14: the structure-sheaf map on sections factors through the
pullback-pushforward adjunction unit and the inverse-image structure-sheaf morphism. -/
private theorem toRingCatSheafHom_app_eq_inverseImageStructureSheafHomComm_app
    {U : (TopologicalSpace.Opens Y)ᵒᵖ} (f : X ⟶ Y) (t : Y.presheaf.obj U) :
    ((RingedSpace.Hom.toRingCatSheafHom f).hom.app U) t =
      ((RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom.app
        ((TopologicalSpace.Opens.map f.hom.base).op.obj U))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
            Y.sheaf).hom.app U) t) := by
  -- Proof comment: unfold the adjunction unit on sections so the target becomes a base section
  -- seen by `d_map`.
  have happ :
      ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U) t =
        ((RingedSpace.Hom.inverseImageStructureSheafHomComm f).hom.app
          ((TopologicalSpace.Opens.map f.hom.base).op.obj U))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
              Y.sheaf).hom.app U) t) := by
    have happ' :
        ((RingedSpace.Hom.commRingSheafPushforwardMap f).hom.app U) =
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
                Y.sheaf) ≫
              (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).map
                (RingedSpace.Hom.inverseImageStructureSheafHomComm f)).hom.app U) := by
      simpa [RingedSpace.Hom.inverseImageStructureSheafHomComm] using
        congrArg
          (fun k : (SheafedSpace.sheaf Y ⟶
              (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj (SheafedSpace.sheaf X)) ↦
            k.hom.app U)
          (CategoryTheory.Adjunction.homEquiv_unit
            (adj := TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base)
            (f := RingedSpace.Hom.inverseImageStructureSheafHomComm f))
    exact congrArg (fun m ↦ m t) happ'
  simpa [RingedSpace.Hom.toRingCatSheafHom, RingedSpace.Hom.commRingSheafPushforwardMap] using
    happ

/-- Helper for Lemma 17.28.14: the direct comparison from `f^* \Omega_{Y/S}` to `\Omega_{X/Y}`
vanishes because relative differentials over `Y` kill sections pulled back from `Y`. -/
private theorem pullbackDifferentialsComparison_toRelativeBase_zero
    (f : X ⟶ Y) (g : Y ⟶ S) :
    pullbackDifferentialsComparison f g g f ⟨by simp⟩ = 0 := by
  -- Route correction: prove the missing section transport explicitly, then apply
  -- `pullbackDifferentialsComparison_unique` to the zero morphism.
  symm
  apply (pullbackDifferentialsComparison_unique f g g f ⟨by simp⟩ 0)
  intro U t
  -- Proof comment: after rewriting `f^\sharp(t)` through the adjunction unit, `d[f]` sees a base
  -- section and vanishes by the universal `d_map` axiom.
  change 0 =
    ((d[f]).app ((TopologicalSpace.Opens.map f.hom.base).op.obj U)).d
      ((RingedSpace.Hom.toRingCatSheafHom f).hom.app U t)
  rw [toRingCatSheafHom_app_eq_inverseImageStructureSheafHomComm_app (f := f) t]
  simpa using
    (ModuleCat.Derivation.d_map
      (PresheafOfModules.Derivation'.app d[f]
        ((TopologicalSpace.Opens.map f.hom.base).op.obj U))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.hom.base).unit.app
        Y.sheaf).hom.app U) t)).symm

-- Proof sketch: pass to stalks, where Lemma `17.28.12` identifies the two displayed sheaf maps
-- with the standard maps between Kähler differentials of local rings. The algebraic transitivity
-- sequence has zero composite, so the sheaf-level composite vanishes.
/-- The canonical transitivity morphisms on relative differentials compose to zero. -/
theorem relativeDifferentialsTransitivity_comp_zero
    (f : X ⟶ Y) (g : Y ⟶ S) :
    relativeDifferentialsTransitivityLeft f g ≫
      relativeDifferentialsTransitivityRight f g = 0 := by
  -- Proof comment: first normalize the identity-pullback coherence, then identify the displayed
  -- composite with the direct comparison already shown to vanish.
  have hbridge :
      (SheafOfModules.pullbackComp (RingedSpace.Hom.toRingCatSheafHom f)
          (RingedSpace.Hom.toRingCatSheafHom (𝟙 X))).symm.hom.app Ω[g] ≫
        (RingedSpace.Hom.pullback (𝟙 X)).map
          (pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩) =
      pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩ ≫
        (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g] := by
    have hpullbackComp :
        SheafOfModules.pullbackComp (RingedSpace.Hom.toRingCatSheafHom f)
            (RingedSpace.Hom.toRingCatSheafHom (𝟙 X)) =
          (RingedSpace.Hom.pullback f).isoWhiskerLeft
              (SheafOfModules.pullbackId X.ringCatSheaf) ≪≫
            (RingedSpace.Hom.pullback f).rightUnitor := by
      simpa [RingedSpace.Hom.toRingCatSheafHom] using
        (SheafOfModules.pullback_comp_id (RingedSpace.Hom.toRingCatSheafHom f))
    rw [hpullbackComp]
    have hnat :=
      NatIso.naturality_1 (SheafOfModules.pullbackId X.ringCatSheaf)
        (pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩)
    have hright :
        (pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩ ≫
            (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g]) ≫
          (SheafOfModules.pullbackId X.ringCatSheaf).hom.app Ω[f ≫ g] =
        pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩ := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩ ≫ k)
          (Iso.inv_hom_id_app (SheafOfModules.pullbackId X.ringCatSheaf) Ω[f ≫ g])
    refine (cancel_mono ((SheafOfModules.pullbackId X.ringCatSheaf).hom.app Ω[f ≫ g])).1 ?_
    exact Eq.trans (by simpa [Category.assoc] using hnat) hright.symm
  have hcomp :=
    pullbackDifferentialsComparison_comp
      f (𝟙 X) (𝟙 S) g g (f ≫ g) f
      ⟨by simp⟩ ⟨by simp⟩
  have hcomp' :
      pullbackDifferentialsComparison f g g f ⟨by simp⟩ =
        (pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩ ≫
            (SheafOfModules.pullbackId X.ringCatSheaf).inv.app Ω[f ≫ g]) ≫
          pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩ := by
    have hcomp₁ :
        pullbackDifferentialsComparison f g g f ⟨by simp⟩ =
          ((SheafOfModules.pullbackComp (RingedSpace.Hom.toRingCatSheafHom f)
                (RingedSpace.Hom.toRingCatSheafHom (𝟙 X))).symm.hom.app Ω[g] ≫
              (RingedSpace.Hom.pullback (𝟙 X)).map
                (pullbackDifferentialsComparison f (𝟙 S) g (f ≫ g) ⟨by simp⟩)) ≫
            pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩ := by
      simpa [Category.assoc] using hcomp
    exact Eq.trans hcomp₁ <|
      by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩)
            hbridge
  have hcomp'' :
      pullbackDifferentialsComparison f g g f ⟨by simp⟩ =
        relativeDifferentialsTransitivityLeft f g ≫
          relativeDifferentialsTransitivityRight f g := by
    simpa [relativeDifferentialsTransitivityLeft, relativeDifferentialsTransitivityRight,
      Category.assoc] using hcomp'
  rw [← hcomp'', pullbackDifferentialsComparison_toRelativeBase_zero (f := f) (g := g)]

/-- The canonical short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
in the transitivity sequence for relative differentials. -/
def relativeDifferentialsTransitivity
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ShortComplex (Modules X) :=
  ShortComplex.mk
    (relativeDifferentialsTransitivityLeft f g)
    (relativeDifferentialsTransitivityRight f g)
    (relativeDifferentialsTransitivity_comp_zero f g)

/-- Helper for Lemma 17.28.14: passing the transitivity complex to a stalk preserves the vanishing
of the composite of its two maps. -/
private theorem relativeDifferentialsTransitivity_stalk_comp_zero
    (f : X ⟶ Y) (g : Y ⟶ S) (x : X) :
    RingedSpace.moduleStalkHom x (relativeDifferentialsTransitivityLeft f g) ≫
      RingedSpace.moduleStalkHom x (relativeDifferentialsTransitivityRight f g) = 0 := by
  -- Proof comment: the stalk functor is functorial, so the stalk composite is the stalk of the
  -- already-vanishing sheaf-level composite.
  calc
    RingedSpace.moduleStalkHom x (relativeDifferentialsTransitivityLeft f g) ≫
        RingedSpace.moduleStalkHom x (relativeDifferentialsTransitivityRight f g) =
      RingedSpace.moduleStalkHom x
        (relativeDifferentialsTransitivityLeft f g ≫
          relativeDifferentialsTransitivityRight f g) := by
            change
              (RingedSpace.stalkModuleFunctor (X := X) x).map
                  (relativeDifferentialsTransitivityLeft f g) ≫
                (RingedSpace.stalkModuleFunctor (X := X) x).map
                  (relativeDifferentialsTransitivityRight f g) =
              (RingedSpace.stalkModuleFunctor (X := X) x).map
                (relativeDifferentialsTransitivityLeft f g ≫
                  relativeDifferentialsTransitivityRight f g)
            exact
              ((RingedSpace.stalkModuleFunctor (X := X) x).map_comp
                (relativeDifferentialsTransitivityLeft f g)
                (relativeDifferentialsTransitivityRight f g)).symm
    _ = RingedSpace.moduleStalkHom x 0 := by
          rw [relativeDifferentialsTransitivity_comp_zero]
    _ = 0 := by
          change (RingedSpace.stalkModuleFunctor (X := X) x).map (0 : _ ⟶ _) = 0
          exact (RingedSpace.stalkModuleFunctor (X := X) x).map_zero _ _

/-- Helper for Lemma 17.28.14: under the identity pullback-pushforward adjunction, the canonical
comparison map is the right transitivity morphism followed by the identity-pushforward
identification. -/
private theorem relativeDifferentialsTransitivityRight_bridge
    (f : X ⟶ Y) (g : Y ⟶ S) :
    ((SheafOfModules.pullbackPushforwardAdjunction
        (RingedSpace.Hom.toRingCatSheafHom (𝟙 X))).homEquiv Ω[f ≫ g] Ω[f])
      (pullbackDifferentialsComparison (𝟙 X) g (f ≫ g) f ⟨by simp⟩) =
        relativeDifferentialsTransitivityRight f g ≫
          (SheafOfModules.pushforwardId X.ringCatSheaf).hom.app Ω[f] := by
  -- Proof comment: for the identity map on `X`, both sides are literally the same sectionwise
  -- formula after unfolding the adjunction hom-equivalence.
  ext U x
  rfl

/-- Helper for Lemma 17.28.14: the right transitivity morphism sends the universal generator
`d_{X/S}(t)` to `d_{X/Y}(t)`. -/
private theorem relativeDifferentialsTransitivityRight_d
    (f : X ⟶ Y) (g : Y ⟶ S) {U : (TopologicalSpace.Opens X)ᵒᵖ}
    (t : X.presheaf.obj U) :
    (relativeDifferentialsTransitivityRight f g).val.app U
      (((d[f ≫ g]).app U).d t) =
        ((d[f]).app U).d t := by
  -- Proof comment: pass to the adjoint characterization of the identity-square comparison and
  -- then collapse the identity pushforward comparison.
  have hbridge := relativeDifferentialsTransitivityRight_bridge (f := f) (g := g)
  have hbridge_app := congrArg (fun k ↦ (k.val.app U) (((d[f ≫ g]).app U).d t)) hbridge
  have hid : (SheafOfModules.pushforwardId X.ringCatSheaf).hom.app Ω[f] = 𝟙 _ := by
    -- Proof comment: the direct image functor along `𝟙_X` is definitionally the identity on
    -- sections.
    ext V x
    rfl
  refine Eq.trans ?_
    (pullbackDifferentialsComparison_characterizing (𝟙 X) g (f ≫ g) f ⟨by simp⟩ (U := U) t)
  simpa [Category.assoc, hid] using hbridge_app.symm

/-- Helper for Lemma 17.28.14: if a morphism `τ : Ω_{X/S} ⟶ F` kills the left transitivity map,
then the induced `S`-relative derivation already vanishes on sections coming directly from
`Y`. -/
private theorem transitivityDescKillsRawBaseSections
    {F : X.Modules} (f : X ⟶ Y) (g : Y ⟶ S) (τ : Ω[f ≫ g] ⟶ F)
    (hτ : relativeDifferentialsTransitivityLeft f g ≫ τ = 0)
    {U : (TopologicalSpace.Opens Y)ᵒᵖ} (t : Y.presheaf.obj U) :
    (((d[f ≫ g]).postcomp τ.val).app ((TopologicalSpace.Opens.map f.hom.base).op.obj U)).d
      (((RingedSpace.Hom.toRingCatSheafHom f).hom.app U) t) = 0 := by
  -- Proof comment: evaluate the left-zero hypothesis on the generator `d[g](t)` and rewrite the
  -- left map by its characterizing formula.
  have hτ_app :=
    congrArg
      (fun k ↦
        (k.val.app ((TopologicalSpace.Opens.map f.hom.base).op.obj U))
          (((d[g]).app U).d t))
      hτ
  change
    τ.val.app ((TopologicalSpace.Opens.map f.hom.base).op.obj U)
        ((relativeDifferentialsTransitivityLeft f g).val.app
          ((TopologicalSpace.Opens.map f.hom.base).op.obj U)
          (((d[g]).app U).d t)) =
      0 at hτ_app
  rw [relativeDifferentialsTransitivityLeft,
    pullbackDifferentialsComparison_characterizing
      f (𝟙 S) g (f ≫ g) ⟨by simp⟩ (U := U) t] at hτ_app
  simpa using hτ_app

/-- Helper for Chap17 Lemma 17 28 14: the algebraic transitivity tail for Kähler differentials is
exact for every tower of commutative rings. -/
private theorem kaehlerDifferentialTransitivity_tail_exact
    {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C] :
    Function.Exact
      (KaehlerDifferential.mapBaseChange A B C)
      (KaehlerDifferential.map A B C C) := by
  -- Proof comment: this is exactly the standard Jacobi-Zariski exactness statement in the
  -- Kähler-differential tail.
  simpa using KaehlerDifferential.exact_mapBaseChange_map A B C

-- Proof sketch: check the statement on stalks. Lemma `17.28.12` identifies the stalk maps with
-- the usual transitivity maps for Kähler differentials of the local ring maps
-- `𝒪_{S,g(f(x))} → 𝒪_{Y,f(x)} → 𝒪_{X,x}`, and Algebra, Lemma `10.131.7` gives exactness and
-- surjectivity there. Then use the stalkwise criterion for exactness of sheaves of modules and for
-- epimorphy.
/-- Lemma 17.28.14: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ S`, the
canonical transitivity short complex
`f^*Ω_{Y/S} ⟶ Ω_{X/S} ⟶ Ω_{X/Y}`
is exact. -/
-- TODO: complete the sheaf-level cokernel route by promoting the current raw-section vanishing
-- statement to arbitrary sections of `f^{-1} 𝒪_Y`; once that descent lemma is in place,
-- `TopCat.Sheaf.relativeDifferentialDesc` packages the cokernel factorization and exactness is
-- formal from `ShortComplex.exact_of_g_is_cokernel`.
theorem relativeDifferentialsTransitivity_exact
    (f : X ⟶ Y) (g : Y ⟶ S) :
    (relativeDifferentialsTransitivity f g).Exact := by
  -- Route correction: the algebraic stalk route is now fully reduced to the textbook Kähler tail
  -- exactness in `kaehlerDifferentialTransitivity_tail_exact`; the only missing step is the
  -- explicit comparison between the two stalk maps here and the canonical
  -- `KaehlerDifferential.mapBaseChange` / `KaehlerDifferential.map`.
  -- Proof comment: by `RingedSpace.ringedSpaceModule_exact_iff_stalkwise_exact`, it is enough to
  -- identify the stalk short complex with the algebraic transitivity sequence at each `x : X`.
  -- TODO: add the two stalk naturality lemmas transporting
  -- `relativeDifferentialsTransitivityLeft/Right` through `relativeDifferentials_stalkIso`, then
  -- apply `kaehlerDifferentialTransitivity_tail_exact` pointwise.
  sorry

/-- The right map in the transitivity short complex for relative differentials is an epimorphism.
-/
theorem relativeDifferentialsTransitivity_epi
    (f : X ⟶ Y) (g : Y ⟶ S) :
    Epi ((relativeDifferentialsTransitivity f g).g) := by
  -- Proof comment: epimorphy is already forced by the generator formula for the right map, since
  -- equality after postcomposition with it gives equality after postcomposition with `d[f]`.
  refine ⟨?_⟩
  intro F α β hαβ
  apply TopCat.Sheaf.relativeDifferential_postcomp_injective
    (RingedSpace.Hom.inverseImageStructureSheafHomComm f)
  ext U t
  have happ := congrArg (fun k ↦ (k.val.app U) (((d[f ≫ g]).app U).d t)) hαβ
  calc
    α.val.app U (((d[f]).app U).d t) =
        α.val.app U ((relativeDifferentialsTransitivityRight f g).val.app U
          (((d[f ≫ g]).app U).d t)) := by
            rw [relativeDifferentialsTransitivityRight_d (f := f) (g := g) (U := U) t]
    _ = ((relativeDifferentialsTransitivityRight f g ≫ α).val.app U)
          (((d[f ≫ g]).app U).d t) := by
            rfl
    _ = ((relativeDifferentialsTransitivityRight f g ≫ β).val.app U)
          (((d[f ≫ g]).app U).d t) := happ
    _ = β.val.app U ((relativeDifferentialsTransitivityRight f g).val.app U
          (((d[f ≫ g]).app U).d t)) := by
            rfl
    _ = β.val.app U (((d[f]).app U).d t) := by
            rw [relativeDifferentialsTransitivityRight_d (f := f) (g := g) (U := U) t]

end AlgebraicGeometry.RingedSpace
