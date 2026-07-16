import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Topology.Sheaves.Functors
import StacksProject_2024.stacks_project.Chap06.Lemma_6_29_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace TopCat
open CategoryTheory.Limits
open TopCat.Sheaf
open TopCat.Presheaf.Pushforward renaming id → pushforwardId

noncomputable section

universe u v

namespace CategoryTheory
namespace Sheaf

/- Domain-style sampling for Lemma 20.19.3:
- primary domain: inverse limits of spectral spaces, compatible inverse systems of abelian sheaves,
  and cohomology on quasi-compact inverse-image opens;
- sampled owner declarations:
  `CompactOpens`,
  `TopCat.Sheaf.pushforward`,
  `Sheaf.cohomologyPresheafFunctor`,
  `SpectralInverseLimit.projectionOpenSectionsComparison`;
- best owner abstraction: the Chapter 6 namespace `SpectralInverseLimit` is already the owner for
  the inverse-limit colimit sheaf and its projection-open comparison morphisms, while the
  quasi-compact-open input should use the chapter's canonical owner `CompactOpens`; abelian
  cohomology lives over the additive sheaf owner on the limit space, and the pushforward/preimage
  cohomology identification should remain theorem-level via
  `pushforward_cohomologyOnOpen_isomorphic_preimage`;
- primitive data: the stage sheaves, the pushforward transition maps, and their identity and
  cocycle compatibilities;
- derived API: the projection-open cohomology diagram, the canonical comparison morphism, and the
  canonical abelian colimit sheaf on the inverse-limit space.

Source/core/bridge triage:
- `source-facing`: Lemma `20.19.3` and its global-open corollary;
- `core/canonical`: `CompactOpens`, `SpectralInverseLimit.colimitAbelianSheaf`,
  `SpectralInverseLimit.projectionOpenCohomologyComparison`, `TopCat.Sheaf.pushforward`,
  `pushforward_cohomologyOnOpen_isomorphic_preimage`, and `Sheaf.cohomologyPresheafFunctor`;
- `bridge/view`: the explicit `(Over i)ᵒᵖ` cohomology diagram and the pulled-back stage-sheaf
  diagram defining the abelian colimit sheaf. -/

namespace SpectralInverseLimit

section

variable {I : Type u} [Category.{v} I]
variable {F : I ⥤ TopCat.{max u v}}
variable (stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v})
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j))
variable (stageMap_id :
  ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
variable (stageMap_comp :
  ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)

/-- The canonical pushforward-sheaf diagram on `Xᵢ` attached to the inverse-limit system. -/
private theorem projectionPushforwardMap_eq
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    F.map B.unop.hom = F.map u.unop.left ≫ F.map A.unop.hom := by
  simpa [Functor.map_comp] using (congrArg (fun f ↦ F.map f) (Over.w u.unop)).symm

/-- The canonical morphism
`(fₐ)_* ℱₐ ⟶ (f_b)_* ℱ_b`
attached to a morphism `u : A ⟶ B` in `(Over i)ᵒᵖ`. -/
private noncomputable def projectionPushforwardMap
    {i : I} {A B : (Over i)ᵒᵖ} (u : A ⟶ B) :
    (pushforward AddCommGrpCat.{max u v} (F.map A.unop.hom)).obj (stageSheaf A.unop.left) ⟶
      (pushforward AddCommGrpCat.{max u v} (F.map B.unop.hom)).obj (stageSheaf B.unop.left) :=
  ⟨((pushforward AddCommGrpCat.{max u v} (F.map A.unop.hom)).map
      (stageMap u.unop.left)).1 ≫
    (TopCat.Presheaf.pushforwardEq
      (projectionPushforwardMap_eq u)
      (stageSheaf B.unop.left).presheaf).inv⟩

/-- The over-category diagram of pushforwarded stage sheaves on the stage `Xᵢ`. -/
private noncomputable def projectionPushforwardDiagram
    (stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v})
    (stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j))
    (_stageMap_id :
      ∀ i : I,
        stageMap (𝟙 i) =
          ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
            (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
    (_stageMap_comp :
      ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
        stageMap (b ≫ a) =
          ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
            (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
    (i : I) :
    (Over i)ᵒᵖ ⥤ (F.obj i).Sheaf AddCommGrpCat.{max u v} where
  obj A := (pushforward AddCommGrpCat.{max u v} (F.map A.unop.hom)).obj (stageSheaf A.unop.left)
  map u := projectionPushforwardMap stageSheaf stageMap u
  map_id := by
    intro A
    sorry
  map_comp := by
    intro A B C u v
    sorry

variable [∀ i : I, HasSheafify (Opens.grothendieckTopology (F.obj i)) AddCommGrpCat.{max u v}]
variable [∀ i : I, HasExt ((F.obj i).Sheaf AddCommGrpCat.{max u v})]

/-- For a fixed stage `i`, compact open `Uᵢ`, and degree `p`, the canonical over-category
diagram `a : j ⟶ i ↦ H^p(Uᵢ, (fₐ)_* ℱⱼ)`, i.e. the library-facing pushforward form of
`a : j ⟶ i ↦ H^p(fₐ⁻¹(Uᵢ), ℱⱼ)`. -/
noncomputable def projectionOpenCohomologyDiagram
    (stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v})
    (stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j))
    (stageMap_id :
      ∀ i : I,
        stageMap (𝟙 i) =
          ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
            (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
    (stageMap_comp :
      ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
        stageMap (b ≫ a) =
          ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
            (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    (Over i)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  projectionPushforwardDiagram stageSheaf stageMap stageMap_id stageMap_comp i ⋙
    cohomologyPresheafFunctor (Opens.grothendieckTopology (F.obj i)) p ⋙
      (evaluation (Opens (F.obj i))ᵒᵖ AddCommGrpCat.{max u v}).obj (op Ui.toOpens)

end

private structure InverseLimitAbelianSheafSystem
    {I : Type u} [Category.{v} I] (F : I ⥤ TopCat.{max u v}) [HasLimit F] where
  stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v}
  stageMap : ∀ {j k : I} (a : j ⟶ k),
      stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j)
  stageMap_id :
    ∀ i : I,
      stageMap (𝟙 i) =
        ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
          (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩
  stageMap_comp :
    ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
      stageMap (b ≫ a) =
        ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
          (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩

namespace InverseLimitAbelianSheafSystem

section

variable {I : Type u} [Category.{v} I]
variable {F : I ⥤ TopCat.{max u v}} [HasLimit F]
variable [HasColimitsOfShape Iᵒᵖ ((limit F).Sheaf AddCommGrpCat.{max u v})]
variable (setup : InverseLimitAbelianSheafSystem F)

/-- The pullback-form transition attached to `a : j ⟶ k`, derived from the source-facing
pushforward map by the pullback-pushforward adjunction. -/
private noncomputable def stagePullbackMap
    {j k : I} (a : j ⟶ k) :
    (pullback AddCommGrpCat.{max u v} (F.map a)).obj (setup.stageSheaf k) ⟶ setup.stageSheaf j :=
  ((pullbackPushforwardAdjunction AddCommGrpCat.{max u v} (F.map a)).homEquiv _ _).symm
    (setup.stageMap a)

/-- The transition map on the pulled-back stage-sheaf diagram over the inverse-limit space. -/
private noncomputable def pulledBackDiagramMap
    {j k : I} (a : j ⟶ k) :
    (pullback AddCommGrpCat.{max u v} (limit.π F k)).obj (setup.stageSheaf k) ⟶
      (pullback AddCommGrpCat.{max u v} (limit.π F j)).obj (setup.stageSheaf j) :=
  ((eqToIso (congrArg (pullback AddCommGrpCat.{max u v}) (limit.w F a))).inv.app
      (setup.stageSheaf k)) ≫
    ((pullbackComp (limit.π F j) (F.map a)).inv.app (setup.stageSheaf k)) ≫
      (pullback AddCommGrpCat.{max u v} (limit.π F j)).map (setup.stagePullbackMap a)

/-- Identity compatibility for the pulled-back stage-sheaf transition maps. -/
private theorem pulledBackDiagramMap_id (i : I) :
    setup.pulledBackDiagramMap (𝟙 i) = 𝟙 _ := by
  sorry

/-- Composition compatibility for the pulled-back stage-sheaf transition maps. -/
private theorem pulledBackDiagramMap_comp {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    setup.pulledBackDiagramMap (a ≫ b) =
      setup.pulledBackDiagramMap b ≫ setup.pulledBackDiagramMap a := by
  sorry

/-- The canonical diagram `i ↦ pᵢ⁻¹ℱᵢ` of abelian sheaves on the inverse-limit space. -/
private noncomputable def pulledBackDiagram :
    Iᵒᵖ ⥤ (limit F).Sheaf AddCommGrpCat.{max u v} where
  obj i := (pullback AddCommGrpCat.{max u v} (limit.π F i.unop)).obj (setup.stageSheaf i.unop)
  map f := setup.pulledBackDiagramMap f.unop
  map_id i := setup.pulledBackDiagramMap_id i.unop
  map_comp f g := setup.pulledBackDiagramMap_comp g.unop f.unop

/-- The colimit abelian sheaf `ℱ = colim i, pᵢ⁻¹ℱᵢ` on the inverse-limit space. -/
noncomputable def colimitAbelianSheaf :
    (limit F).Sheaf AddCommGrpCat.{max u v} :=
  colimit setup.pulledBackDiagram

/-- The canonical map from the pushforwarded stage sheaf over `Xᵢ` to the pushforward of the
colimit sheaf along `pᵢ`. -/
private noncomputable def projectionPushforwardToColimitSheafMap
    (i : I) (A : (Over i)ᵒᵖ) :
    (pushforward AddCommGrpCat.{max u v} (F.map A.unop.hom)).obj (setup.stageSheaf A.unop.left) ⟶
      (pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj setup.colimitAbelianSheaf :=
  (pushforward AddCommGrpCat.{max u v} (F.map A.unop.hom)).map
      (((pullbackPushforwardAdjunction AddCommGrpCat.{max u v} (limit.π F A.unop.left)).unit.app
        (setup.stageSheaf A.unop.left))) ≫
    eqToHom
      (congrArg
        (fun f ↦ (pushforward AddCommGrpCat.{max u v} f).obj
          (setup.pulledBackDiagram.obj (op A.unop.left)))
        (limit.w F A.unop.hom)) ≫
    (pushforward AddCommGrpCat.{max u v} (limit.π F i)).map
      (colimit.ι setup.pulledBackDiagram (op A.unop.left))

/-- The cocone from the stagewise cohomology diagram over `a : j ⟶ i` to the cohomology of the
pushforward of the canonical colimit sheaf along `pᵢ`. -/
private noncomputable def projectionOpenCohomologyComparisonCocone
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    Cocone
      (projectionOpenCohomologyDiagram
        setup.stageSheaf setup.stageMap setup.stageMap_id setup.stageMap_comp i Ui p) where
  pt := (((pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj
      setup.colimitAbelianSheaf).H' p Ui.toOpens)
  ι :=
    { app := fun A ↦
        ((cohomologyPresheafFunctor (Opens.grothendieckTopology (F.obj i)) p).map
          (setup.projectionPushforwardToColimitSheafMap i A)).app (op Ui.toOpens)
      naturality := fun {_ _} u ↦ by
        sorry }

/-- The canonical comparison map from the filtered colimit of the stagewise cohomology groups
over `a : j ⟶ i` to the cohomology of the pushforward of the canonical colimit sheaf along
`pᵢ`. -/
noncomputable def projectionOpenCohomologyComparison
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    colimit
        (projectionOpenCohomologyDiagram
          setup.stageSheaf setup.stageMap setup.stageMap_id setup.stageMap_comp i Ui p) ⟶
      (((pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj
        setup.colimitAbelianSheaf).H' p Ui.toOpens) := by
  change _ ⟶ (setup.projectionOpenCohomologyComparisonCocone i Ui p).pt
  exact colimit.desc _
    (setup.projectionOpenCohomologyComparisonCocone i Ui p)

end

end InverseLimitAbelianSheafSystem

section

variable {I : Type u} [Category.{v} I]
variable {F : I ⥤ TopCat.{max u v}} [HasLimit F]
variable (stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v})
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j))
variable (stageMap_id :
  ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
variable (stageMap_comp :
  ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
variable [HasColimitsOfShape Iᵒᵖ ((limit F).Sheaf AddCommGrpCat.{max u v})]

private noncomputable def setup : InverseLimitAbelianSheafSystem F where
  stageSheaf := stageSheaf
  stageMap := stageMap
  stageMap_id := stageMap_id
  stageMap_comp := stageMap_comp

/-- The filtered colimit of the stagewise cohomology groups over `a : j ⟶ i`, i.e.
`colim_a H^p(Uᵢ, (f_a)_* ℱ_j) = colim_a H^p(f_a⁻¹(Uᵢ), ℱ_j)`. -/
noncomputable def projectionOpenCohomologyColimit
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    AddCommGrpCat.{max u v} :=
  colimit
    (projectionOpenCohomologyDiagram
      stageSheaf stageMap stageMap_id stageMap_comp i Ui p)

/-- The colimit abelian sheaf `ℱ = colim i, pᵢ⁻¹ℱᵢ` on the inverse-limit space. -/
noncomputable def colimitAbelianSheaf :
    (limit F).Sheaf AddCommGrpCat.{max u v} :=
  (setup stageSheaf stageMap stageMap_id stageMap_comp).colimitAbelianSheaf

/-- The canonical comparison map from the filtered colimit of the stagewise cohomology groups
over `a : j ⟶ i` to the cohomology of the pushforward of the canonical colimit sheaf along
`pᵢ`. -/
noncomputable def projectionOpenCohomologyComparison
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    projectionOpenCohomologyColimit stageSheaf stageMap stageMap_id stageMap_comp i Ui p ⟶
      (((pushforward AddCommGrpCat.{max u v} (limit.π F i)).obj
        (colimitAbelianSheaf stageSheaf stageMap stageMap_id stageMap_comp)).H' p Ui.toOpens) :=
  (setup stageSheaf stageMap stageMap_id stageMap_comp).projectionOpenCohomologyComparison
    i Ui p

end

end SpectralInverseLimit

variable {X Y : TopCat.{u}}

variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
variable [HasSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

-- Proof sketch: pushforward along `f` is right adjoint to inverse image, and inverse image of
-- abelian sheaves is exact, so pushforward preserves injective resolutions. Since sections of
-- `f_* ℱ` on `U` are sections of `ℱ` on `f⁻¹(U)`, the derived functors
-- computing these two cohomology groups agree.
/-- The cohomology of the pushforward sheaf on an open `U ⊆ Y` identifies with the cohomology of
the original sheaf on the inverse-image open `f⁻¹(U)`. -/
theorem pushforward_cohomologyOnOpen_isomorphic_preimage
    (f : X ⟶ Y) (ℱ : X.Sheaf AddCommGrpCat.{u}) (U : Opens Y) (p : ℕ) :
    IsIsomorphic (((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj ℱ).H' p U)
      (ℱ.H' p ((Opens.map f).obj U)) := sorry

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
variable (F : I ⥤ TopCat.{max u v}) [HasLimit F]
variable [∀ j : I, SpectralSpace (F.obj j)]
variable [∀ i : I, HasSheafify (Opens.grothendieckTopology (F.obj i)) AddCommGrpCat.{max u v}]
variable [∀ i : I, HasExt ((F.obj i).Sheaf AddCommGrpCat.{max u v})]
variable [HasSheafify (Opens.grothendieckTopology (limit F : TopCat.{max u v})) AddCommGrpCat.{max u v}]
variable [HasExt.{max u v} (Sheaf (Opens.grothendieckTopology (limit F : TopCat.{max u v}))
  AddCommGrpCat.{max u v})]
variable (stageSheaf : ∀ i : I, (F.obj i).Sheaf AddCommGrpCat.{max u v})
variable (stageMap : ∀ {j k : I} (a : j ⟶ k),
  stageSheaf k ⟶ (pushforward AddCommGrpCat.{max u v} (F.map a)).obj (stageSheaf j))
variable (stageMap_id :
  ∀ i : I,
    stageMap (𝟙 i) =
      ⟨(pushforwardId (stageSheaf i).presheaf).inv ≫
        (TopCat.Presheaf.pushforwardEq (F.map_id i) (stageSheaf i).presheaf).inv⟩)
variable (stageMap_comp :
  ∀ {i j k : I} (a : j ⟶ i) (b : k ⟶ j),
    stageMap (b ≫ a) =
      ⟨(stageMap a ≫ (pushforward AddCommGrpCat.{max u v} (F.map a)).map (stageMap b)).1 ≫
        (TopCat.Presheaf.pushforwardEq (F.map_comp b a) (stageSheaf k).presheaf).inv⟩)
variable [HasColimitsOfShape Iᵒᵖ ((limit F).Sheaf AddCommGrpCat.{max u v})]

/-- Lemma 20.19.3: in the inverse-limit situation for spectral spaces and compatible abelian
sheaves with spectral transition maps, for every compact open `Uᵢ ⊆ Xᵢ` and every degree `p`, the
canonical comparison morphism from the filtered colimit of
`H^p(fₐ⁻¹(Uᵢ), ℱⱼ)` to the cohomology of the pushforward of the canonical inverse-limit colimit
sheaf along `pᵢ` is an isomorphism. -/
@[stacks 0A37]
instance spectralInverseLimit_projectionOpenCohomologyComparison_isIso
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    IsIso (SpectralInverseLimit.projectionOpenCohomologyComparison
      stageSheaf stageMap stageMap_id stageMap_comp i Ui p) := by
  sorry

-- Proof sketch: compose the canonical comparison to pushforward cohomology with the canonical
-- pushforward-to-preimage cohomology identification for the canonical colimit sheaf.
omit [IsCofiltered I] [∀ j : I, SpectralSpace (F.obj j)]
  [∀ i : I, HasExt ((F.obj i).Sheaf AddCommGrpCat.{max u v})] in
/-- Lemma 20.19.3 for the canonical colimit sheaf: in the inverse-limit situation for spectral
spaces and compatible abelian sheaves with spectral transition maps, if `Uᵢ ⊆ Xᵢ` is a compact
open, then the filtered colimit of the groups `H^p(fₐ⁻¹(Uᵢ), ℱⱼ)` is canonically isomorphic to the
cohomology of the inverse-image open `pᵢ⁻¹(Uᵢ)` of the canonical
inverse-limit colimit sheaf. -/
@[stacks 0A37]
theorem spectralInverseLimit_projectionOpenCohomologyColimitAbelianSheaf_isomorphic
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    IsIsomorphic
      (SpectralInverseLimit.projectionOpenCohomologyColimit
        stageSheaf stageMap stageMap_id stageMap_comp i Ui p)
      ((SpectralInverseLimit.colimitAbelianSheaf
          stageSheaf stageMap stageMap_id stageMap_comp).H' p
        ((Opens.map (limit.π F i)).obj Ui.toOpens)) := by
  let φ := SpectralInverseLimit.projectionOpenCohomologyComparison
    stageSheaf stageMap stageMap_id stageMap_comp i Ui p
  haveI : IsIso φ := by
    simpa [φ] using
      (spectralInverseLimit_projectionOpenCohomologyComparison_isIso
        F stageSheaf stageMap stageMap_id stageMap_comp hF i Ui p)
  rcases
      pushforward_cohomologyOnOpen_isomorphic_preimage
        (limit.π F i)
        (SpectralInverseLimit.colimitAbelianSheaf
          stageSheaf stageMap stageMap_id stageMap_comp)
        Ui.toOpens p with
    ⟨e⟩
  exact ⟨(asIso φ) ≪≫ e⟩

-- Proof sketch: first pass through the canonical colimit-sheaf target above, then transport along
-- the cohomology map induced by `colimitAbelianSheafIso.hom`.
omit [IsCofiltered I] [∀ j : I, SpectralSpace (F.obj j)]
  [∀ i : I, HasExt ((F.obj i).Sheaf AddCommGrpCat.{max u v})] in
/-- Lemma 20.19.3 in `IsIsomorphic` form: if `Uᵢ ⊆ Xᵢ` is a compact open, then the filtered
colimit of `H^p(fₐ⁻¹(Uᵢ), ℱⱼ)` is canonically isomorphic to `H^p(pᵢ⁻¹(Uᵢ), ℱ)` for any abelian
limit sheaf identified with the canonical inverse-limit colimit sheaf. -/
@[stacks 0A37]
theorem spectralInverseLimit_projectionOpenCohomology_isomorphic
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (limitSheaf : (limit F).Sheaf AddCommGrpCat.{max u v})
    (colimitAbelianSheafIso :
      SpectralInverseLimit.colimitAbelianSheaf
        stageSheaf stageMap stageMap_id stageMap_comp ≅ limitSheaf)
    (i : I) (Ui : CompactOpens (F.obj i)) (p : ℕ) :
    IsIsomorphic
      (SpectralInverseLimit.projectionOpenCohomologyColimit
        stageSheaf stageMap stageMap_id stageMap_comp i Ui p)
      (limitSheaf.H' p ((Opens.map (limit.π F i)).obj Ui.toOpens)) := by
  rcases
      spectralInverseLimit_projectionOpenCohomologyColimitAbelianSheaf_isomorphic
        F stageSheaf stageMap stageMap_id stageMap_comp hF i Ui p with
    ⟨e⟩
  let η :
      ((SpectralInverseLimit.colimitAbelianSheaf
          stageSheaf stageMap stageMap_id stageMap_comp).H' p
        ((Opens.map (limit.π F i)).obj Ui.toOpens)) ⟶
      (limitSheaf.H' p ((Opens.map (limit.π F i)).obj Ui.toOpens)) :=
    ((cohomologyPresheafFunctor (Opens.grothendieckTopology (limit F : TopCat.{max u v})) p).map
      colimitAbelianSheafIso.hom).app (op ((Opens.map (limit.π F i)).obj Ui.toOpens))
  letI : IsIso η := by
    infer_instance
  exact ⟨e ≪≫ asIso η⟩

-- Proof sketch: apply Lemma `20.19.3` to the top open `Uᵢ = Xᵢ`, which is quasi-compact for a
-- spectral space, and rewrite `pᵢ⁻¹(Xᵢ)` as the whole inverse-limit space `X`.
/-- The global cohomology of the limit sheaf is the filtered colimit of the stagewise global
cohomology groups in the inverse-limit situation of Lemma `20.19.3`, with spectral transition
maps. -/
theorem spectralInverseLimit_globalCohomology_isomorphic
    (hF : ∀ {j k : I} (a : j ⟶ k), IsSpectralMap (F.map a))
    (limitSheaf : (limit F).Sheaf AddCommGrpCat.{max u v})
    (colimitAbelianSheafIso :
      SpectralInverseLimit.colimitAbelianSheaf
        stageSheaf stageMap stageMap_id stageMap_comp ≅ limitSheaf)
    (i : I) (p : ℕ) :
    IsIsomorphic
      (SpectralInverseLimit.projectionOpenCohomologyColimit
        stageSheaf stageMap stageMap_id stageMap_comp i (⊤ : CompactOpens (F.obj i)) p)
      (limitSheaf.H' p (⊤ : Opens (limit F : TopCat.{max u v}))) := sorry

end Sheaf
end CategoryTheory
