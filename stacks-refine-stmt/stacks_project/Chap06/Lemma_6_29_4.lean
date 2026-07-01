import Mathlib
import Mathlib.CategoryTheory.Sites.Limits
import stacks_project.Chap06.Lemma_6_21_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open TopCat.Presheaf.Pushforward renaming id → pushforwardId
open CategoryTheory.Limits TopCat.Sheaf

universe u v

noncomputable section

section

variable {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v})
variable (stageSheaf : ∀ j : I, TopCat.Sheaf (Type (max u v)) (F.obj j))
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶
    (TopCat.Sheaf.pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))

/- Domain-style sampling for Lemma 6.29.4:
- primary domain: compatible inverse systems of set-valued sheaves on a cofiltered diagram of
  spectral spaces, together with the comparison between stagewise sections over inverse-image opens
  and sections of the colimit sheaf on the inverse limit;
- sampled owner declarations:
  `CategoryTheory.CofilteredSiteDiagram`,
  `CategoryTheory.ColimitSiteStageFamily`,
  `CategoryTheory.colimitSiteStageFamilySectionsComparison`,
  `TopCat.Sheaf.pullbackPushforwardAdjunction`;
- owner abstraction: the chapter-wide compatible-family owner already lives at the site level, so
  this file should keep the source-facing topological inputs `stageSheaf`, `stageMap`, and their
  compatibilities separate, and use pullback-side maps only as a bridge to the canonical site-level
  comparison on compact-open basis sites;
- primitive data: the stage sheaves and the pushforward transition maps `stageMap`, together with
  their identity and cocycle compatibilities;
- derived API: the pullback-form transition maps, the over-category section diagram, the pulled-back
  colimit sheaf on the limit space, and the comparison map on quasi-compact opens.

Source/core/bridge triage:
- `source-facing`: the stage sheaves, the pushforward transition maps, and the topological
  comparison map on quasi-compact opens;
- `core/canonical`: the site-level owners
  `CategoryTheory.CofilteredSiteDiagram`,
  `CategoryTheory.ColimitSiteStageFamily`,
  and `CategoryTheory.colimitSiteStageFamilySectionsComparison`;
- `bridge/view`: the explicit topological over-category and pulled-back diagrams below, which are
  implementation devices translating the source-facing inverse-system data to the canonical owner
  layer. -/

/-- The canonical sheaf morphism
`(f_a)_* \mathcal F_a ⟶ (f_b)_* \mathcal F_b`
attached to a morphism `u : A ⟶ B` in `(Over i)ᵒᵖ`. -/
private theorem projectionPushforwardMap_eq
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    F.map B.unop.hom = F.map u.unop.left ≫ F.map A.unop.hom := by
  simpa [Functor.map_comp] using
    (congrArg (fun f ↦ F.map f) (Over.w u.unop)).symm

/-- The canonical sheaf morphism
`(f_a)_* \mathcal F_a ⟶ (f_b)_* \mathcal F_b`
attached to a morphism `u : A ⟶ B` in `(Over i)ᵒᵖ`. -/
private noncomputable def projectionPushforwardMap
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (TopCat.Sheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).obj
        (stageSheaf A.unop.left) ⟶
      (TopCat.Sheaf.pushforward (Type (max u v)) (F.map B.unop.hom)).obj
        (stageSheaf B.unop.left) :=
  ⟨((TopCat.Sheaf.pushforward (Type (max u v)) (F.map A.unop.hom)).map
      (stageMap u.unop.left)).1 ≫
    (TopCat.Presheaf.pushforwardEq
      (projectionPushforwardMap_eq F u)
      (stageSheaf B.unop.left).presheaf).inv⟩

end

private structure InverseLimitTypeSheafSystem
    {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v}) [IsCofiltered I]
    [∀ j : I, SpectralSpace ↥(F.obj j)] where
  stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i)
  stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶
      (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j)
  stageMap_id :
    ∀ i : I,
      stageMap (𝟙 i) =
        ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
          (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩
  stageMap_comp :
    ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
      stageMap (b ≫ a) =
        ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
          (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩

namespace InverseLimitTypeSheafSystem

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable {F : I ⥤ TopCat.{max u v}} [∀ j : I, SpectralSpace ↥(F.obj j)]
variable [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]

variable (setup : InverseLimitTypeSheafSystem F)

/-- The canonical pullback-form transition attached to `a : j ⟶ k`, derived from the source-facing
pushforward map `\varphi_a : \mathcal F_k ⟶ f_{a,*}\mathcal F_j` by the pullback-pushforward
adjunction. This is the bridge-level form used by the later colimit sheaf construction on the
inverse-limit space. -/
private noncomputable def stagePullbackMap {j k : I} (a : j ⟶ k) :
    ((pullback (Type (max u v)) (F.map a)).obj (setup.stageSheaf k)) ⟶ setup.stageSheaf j :=
  ((pullbackPushforwardAdjunction (Type (max u v)) (F.map a)).homEquiv _ _).symm
    (setup.stageMap a)

/-- The over-category diagram of pushforwarded stage sheaves on `X_i`. -/
private noncomputable def projectionPushforwardDiagram (i : I) :
    (Over i)ᵒᵖ ⥤ TopCat.Sheaf (Type (max u v)) (F.obj i) where
  obj A := (pushforward (Type (max u v)) (F.map A.unop.hom)).obj (setup.stageSheaf A.unop.left)
  map u := projectionPushforwardMap F setup.stageSheaf setup.stageMap u
  map_id A := by
    sorry
  map_comp u v := by
    sorry

/-- The canonical sections functor at the open `U_i` on the stage `X_i`. -/
private abbrev stageSectionFunctor (i : I) (Uᵢ : Opens (F.obj i)) :
    TopCat.Sheaf (Type (max u v)) (F.obj i) ⥤ Type (max u v) :=
  (CategoryTheory.sheafSections (Opens.grothendieckTopology (F.obj i)) (Type (max u v))).obj
    (op Uᵢ)

/-- The section type `\mathcal{F}_j(f_a^{-1}(U_i))` attached to an object `a : j ⟶ i` of
`Over i`, derived by evaluating the canonical pushforward-sheaf diagram at `U_i`. -/
private abbrev projectionOpenSectionValue (i : I) (Uᵢ : Opens (F.obj i))
    (A : (Over i)ᵒᵖ) : Type (max u v) :=
  (stageSectionFunctor i Uᵢ).obj ((setup.projectionPushforwardDiagram i).obj A)

/-- The over-category diagram `a : j ⟶ i ↦ \mathcal{F}_j(f_a^{-1}(U_i))`, obtained by evaluating
the canonical pushforward-sheaf diagram at `U_i`. -/
private noncomputable def projectionOpenSectionDiagram (i : I) (Uᵢ : Opens (F.obj i)) :
    (Over i)ᵒᵖ ⥤ Type (max u v) :=
  setup.projectionPushforwardDiagram i ⋙ stageSectionFunctor i Uᵢ

/-- The colimit `\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i))`. -/
noncomputable def projectionOpenSectionColimit (i : I) (Uᵢ : Opens (F.obj i)) :
    Type (max u v) :=
  colimit (setup.projectionOpenSectionDiagram i Uᵢ)

/-- The transition map on the pulled-back stage-sheaf diagram over the limit space. -/
private noncomputable def pulledBackDiagramMap {j k : I} (a : j ⟶ k) :
    ((pullback (Type (max u v)) (limit.π F k)).obj (setup.stageSheaf k)) ⟶
      ((pullback (Type (max u v)) (limit.π F j)).obj (setup.stageSheaf j)) :=
  ((eqToIso (congrArg (pullback (Type (max u v))) (limit.w F a))).inv.app (setup.stageSheaf k)) ≫
    ((pullbackComp (limit.π F j) (F.map a)).inv.app (setup.stageSheaf k)) ≫
      (pullback (Type (max u v)) (limit.π F j)).map (setup.stagePullbackMap a)

/-- Identity compatibility for the pulled-back stage-sheaf transition maps. -/
private theorem pulledBackDiagramMap_id (i : I) :
    setup.pulledBackDiagramMap (𝟙 i) = 𝟙 _ := by
  sorry

/-- Composition compatibility for the pulled-back stage-sheaf transition maps. -/
private theorem pulledBackDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    setup.pulledBackDiagramMap (a ≫ b) =
      setup.pulledBackDiagramMap b ≫ setup.pulledBackDiagramMap a := by
  sorry

/-- The canonical diagram `i ↦ p_i^{-1}\mathcal{F}_i` on the inverse-limit space. -/
private noncomputable def pulledBackDiagram : Iᵒᵖ ⥤ TopCat.Sheaf (Type (max u v)) (limit F) where
  obj i := (pullback (Type (max u v)) (limit.π F i.unop)).obj (setup.stageSheaf i.unop)
  map f := setup.pulledBackDiagramMap f.unop
  map_id i := setup.pulledBackDiagramMap_id i.unop
  map_comp f g := setup.pulledBackDiagramMap_comp g.unop f.unop

/-- The colimit sheaf
`\mathcal{F} = \mathop{\mathrm{colim}}_i p_i^{-1}\mathcal{F}_i`
on the inverse-limit space. -/
noncomputable def colimitSheaf : TopCat.Sheaf (Type (max u v)) (limit F) :=
  colimit setup.pulledBackDiagram

-- Proof sketch: the limit-cone identity `p_j ≫ f_a = p_i` identifies the iterated inverse image
-- of `U_i` along `p_j` and `f_a` with the direct inverse image along `p_i`.
/-- The open pulled back along `p_j` from `f_a^{-1}(U_i)` agrees with `p_i^{-1}(U_i)`. -/
private theorem limit_projection_preimage_eq {i j : I} (a : j ⟶ i)
    (Uᵢ : Opens (F.obj i)) :
    (Opens.map (limit.π F j)).obj ((Opens.map (F.map a)).obj Uᵢ) =
      (Opens.map (limit.π F i)).obj Uᵢ := by
  sorry

/-- The canonical map from a stage section over `f_a^{-1}(U_i)` to the corresponding section of
`p_j^{-1}\mathcal{F}_j` over `p_i^{-1}(U_i)`. -/
private noncomputable def projectionOpenSectionToPulledBackStageMap
    (i : I) (Uᵢ : Opens (F.obj i)) (A : (Over i)ᵒᵖ) :
    setup.projectionOpenSectionValue i Uᵢ A ⟶
      (((setup.pulledBackDiagram.obj (op A.unop.left)).presheaf).obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ))) :=
  let η :=
    (((pullbackPushforwardAdjunction (Type (max u v))
      (limit.π F A.unop.left)).unit.app (setup.stageSheaf A.unop.left)).1.app
        (op ((Opens.map (F.map A.unop.hom)).obj Uᵢ)))
  η ≫ eqToHom
    (congrArg
      (((setup.pulledBackDiagram.obj (op A.unop.left)).presheaf).obj)
      (congrArg op (limit_projection_preimage_eq A.unop.hom Uᵢ)))

/-- The cocone from the over-category diagram
`a : j ⟶ i ↦ \mathcal{F}_j(f_a^{-1}(U_i))`
to the sections of the colimit sheaf over `p_i^{-1}(U_i)`. -/
private noncomputable def projectionOpenSectionsComparisonCocone
    (i : I) (Uᵢ : Opens (F.obj i)) :
    Cocone (setup.projectionOpenSectionDiagram i Uᵢ) where
  pt := (setup.colimitSheaf.presheaf).obj
    (op ((Opens.map (limit.π F i)).obj Uᵢ))
  ι :=
    { app := fun A ↦
        setup.projectionOpenSectionToPulledBackStageMap i Uᵢ A ≫
          (colimit.ι setup.pulledBackDiagram (op A.unop.left)).1.app
            (op ((Opens.map (limit.π F i)).obj Uᵢ))
      naturality := fun {_ _} u ↦ by
        sorry }

/-- The canonical comparison map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i)) = \mathcal{F}(p_i^{-1}(U_i))`.
-/
noncomputable def projectionOpenSectionsComparison (i : I) (Uᵢ : Opens (F.obj i)) :
    setup.projectionOpenSectionColimit i Uᵢ ⟶
      (setup.colimitSheaf.presheaf).obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ)) := by
  change _ ⟶ (setup.projectionOpenSectionsComparisonCocone i Uᵢ).pt
  exact colimit.desc _ (setup.projectionOpenSectionsComparisonCocone i Uᵢ)

end InverseLimitTypeSheafSystem

namespace SpectralInverseLimit

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(F.obj j)]
variable (stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i))
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶
    (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))
variable (stageMap_id :
  ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
variable (stageMap_comp :
  ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
variable [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]

private noncomputable def setup : InverseLimitTypeSheafSystem F where
  stageSheaf := stageSheaf
  stageMap := stageMap
  stageMap_id := stageMap_id
  stageMap_comp := stageMap_comp

/-- The colimit `\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i))`. -/
noncomputable def projectionOpenSectionColimit (i : I) (Uᵢ : Opens (F.obj i)) :
    Type (max u v) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenSectionColimit i Uᵢ

/-- The colimit sheaf
`\mathcal{F} = \mathop{\mathrm{colim}}_i p_i^{-1}\mathcal{F}_i`
on the inverse-limit space. -/
noncomputable def colimitSheaf : TopCat.Sheaf (Type (max u v)) (limit F) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).colimitSheaf

/-- The canonical comparison map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i)) = \mathcal{F}(p_i^{-1}(U_i))`.
-/
noncomputable def projectionOpenSectionsComparison (i : I) (Uᵢ : Opens (F.obj i)) :
    projectionOpenSectionColimit F stageSheaf stageMap stageMap_id stageMap_comp i Uᵢ ⟶
      (colimitSheaf F stageSheaf stageMap stageMap_id stageMap_comp).presheaf.obj
        (op ((Opens.map (limit.π F i)).obj Uᵢ)) :=
  (setup F stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenSectionsComparison i Uᵢ

-- Proof sketch: restrict each `stageSheaf j` to the compact-open basis site of `F.obj j`, package
-- the resulting basis sites into the canonical Chapter 7 owner
-- `CategoryTheory.CofilteredSiteDiagram`, convert `stageMap` to the corresponding
-- `CategoryTheory.ColimitSiteStageFamily` transition maps via the pullback-pushforward adjunction,
-- identify the topological comparison map above with
-- `CategoryTheory.colimitSiteStageFamilySectionsComparison`, and apply the site-level bijectivity
-- theorem together with Lemma `6.29.3`.
private theorem projectionOpenSectionsComparison_isIso_viaSiteComparison
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    IsIso (projectionOpenSectionsComparison F stageSheaf stageMap stageMap_id stageMap_comp
      i Uᵢ) := by
  sorry

end

end SpectralInverseLimit

/-- Lemma 6.29.4: in the inverse-limit situation for spectral spaces and compatible type-valued
sheaves, if `U_i ⊆ X_i` is quasi-compact open, then the canonical map
`\mathop{\mathrm{colim}}_{a : j \to i} \mathcal{F}_j(f_a^{-1}(U_i)) \to
(\mathop{\mathrm{colim}}_j p_j^{-1}\mathcal{F}_j)(p_i^{-1}(U_i))`
is an isomorphism. -/
theorem spectralInverseLimit_projectionOpenSectionsComparison_isIso
    {I : Type u} [Category.{v} I] [IsCofiltered I]
    (F : I ⥤ TopCat.{max u v}) [∀ j : I, SpectralSpace ↥(F.obj j)]
    (stageSheaf : ∀ i : I, TopCat.Sheaf (Type (max u v)) (F.obj i))
    (stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶
        (pushforward (Type (max u v)) (F.map a)).obj (stageSheaf j))
    (stageMap_id :
      ∀ i : I,
        stageMap (𝟙 i) =
          ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
            (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
    (stageMap_comp :
      ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
        stageMap (b ≫ a) =
          ⟨(stageMap a ≫ (pushforward (Type (max u v)) (F.map a)).map (stageMap b)).1 ≫
            (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    [HasColimitsOfShape Iᵒᵖ (TopCat.Sheaf (Type (max u v)) (limit F))]
    (i : I) (Uᵢ : Opens (F.obj i)) (hUᵢ : IsCompact (Uᵢ : Set (F.obj i))) :
    IsIso (SpectralInverseLimit.projectionOpenSectionsComparison
      F stageSheaf stageMap stageMap_id stageMap_comp i Uᵢ) :=
  SpectralInverseLimit.projectionOpenSectionsComparison_isIso_viaSiteComparison
    F stageSheaf stageMap stageMap_id stageMap_comp hF i Uᵢ hUᵢ
