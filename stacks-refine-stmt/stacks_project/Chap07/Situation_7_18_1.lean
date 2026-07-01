import Mathlib
import Mathlib.CategoryTheory.Sites.Finite
import stacks_project.Chap07.Definition_7_14_1
import stacks_project.Chap07.Lemma_7_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Limits
open CategoryTheory.SemiRepresentableFamily.Over
open Opposite

universe uI uC vC

/-
Domain-style sampling for Situation 7.18.1:
- primary domain: cofiltered inverse systems of sites, their stage morphisms of sites, and the
  cocone functors into the colimit site;
- sampled owner API:
  `CategoryTheory.Precoverage.finite`,
  `CategoryTheory.Precoverage.mem_finite_iff`,
  `Functor.IsContinuous`,
  `RepresentablyFlat`,
  `IsMorphismOfSites`,
  `GrothendieckTopology.HasFiniteRefinementProperty`;
- source/core/bridge triage:
  `source-facing`: the inverse system of sites itself;
  `core/canonical`: the diagram owner `Iᵒᵖ ⥤ Cat`, the stage Grothendieck topologies, and the
  site-morphism owner `IsMorphismOfSites` together with the canonical owner
  `CategoryTheory.Precoverage.finite` for literally finite covering families;
  `bridge/view`: the stage transition functors, stage cocone functors, and their objectwise images.

Primitive data are the index category, its cofilteredness, the contravariant category diagram, the
stage topologies, the objectwise finiteness of stage covering families, and the stage morphisms of
sites. The objectwise finite-refinement owner is derived from that stronger source-facing data and
should not remain primitive. The repeated functors `((S.diagram.map a.op).toFunctor)` and
`((colimit.ι S.diagram (op i)).toFunctor)` are derived API and should live under the owner rather
than as downstream ad hoc spellings.
-/
/-- A site whose covering families are literally finite at the precoverage layer has the
finite-refinement property on every object. This is the canonical bridge from the source-facing
finite-covering-family hypothesis to the downstream owner used later in the chapter. -/
theorem GrothendieckTopology.hasFiniteRefinementProperty_of_covering_mem_finite
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (hfinite :
      ∀ ⦃U : C⦄ {R : Presieve U},
        R ∈ J.toPrecoverage U → R ∈ Precoverage.finite C U)
    (U : C) :
    HasFiniteRefinementProperty J U := by
  refine
    { finite_refinement := fun R hR ↦ ?_ }
  have hRpre : R ∈ J.toPrecoverage U := by
    exact (GrothendieckTopology.mem_toPrecoverage_iff J R).2 hR
  have hRfinite : R.uncurry.Finite :=
    (Precoverage.mem_finite_iff.1 (hfinite hRpre))
  let 𝒱 : SemiRepresentableFamily.Over.{vC, uC, max uC vC} U :=
    ofArrows
      (fun i : R.uncurry ↦ i.1.1)
      (fun i : R.uncurry ↦ i.1.2)
  have h𝒱toPresieve : 𝒱.toPresieve = R := by
    simpa [𝒱, toPresieve] using presieve_of_uncurry_eq R
  have h𝒱toSieve : 𝒱.toSieve = Sieve.generate R := by
    simpa [toSieve] using congrArg Sieve.generate h𝒱toPresieve
  have h𝒱 : 𝒱.toSieve ∈ J U := by
    rw [h𝒱toSieve]
    exact hR
  refine ⟨𝒱, hRfinite.to_subtype, h𝒱, ?_⟩
  simpa [h𝒱toSieve]

/-- Situation 7.18.1: a cofiltered inverse system of sites, encoded by a contravariant diagram of
the underlying categories, whose stage Grothendieck topologies admit finite covering-family
presentations and whose transition functors define morphisms of sites. -/
structure CofilteredSiteDiagram where
  /-- The cofiltered index category `\mathcal I`. -/
  I : Type uI
  /-- The category structure on the index category. -/
  [smallCategoryI : SmallCategory I]
  /-- The cofilteredness hypothesis on the index category. -/
  [cofilteredI : IsCofiltered I]
  /-- The contravariant diagram of underlying categories `i ↦ \mathcal C_i`. -/
  diagram : Iᵒᵖ ⥤ Cat.{vC, uC}
  /-- The stage Grothendieck topology on each `\mathcal C_i`. -/
  stageTopology (i : I) : GrothendieckTopology (diagram.obj (op i))
  /-- Every source-facing covering family in each stage site is already finite, expressed through
  the canonical finite precoverage owner on the stage category. -/
  stageCovering_mem_finite {i : I} {X : diagram.obj (op i)} {R : Presieve X}
      (hR : R ∈ (stageTopology i).toPrecoverage X) :
      R ∈ Precoverage.finite (diagram.obj (op i)) X
  /-- Each transition functor `u_a : \mathcal C_j \to \mathcal C_i` defines the corresponding
  morphism of sites `f_a : (\mathcal C_i, J_i) \to (\mathcal C_j, J_j)`. -/
  transition_isMorphismOfSites {i j : I} (a : j ⟶ i) :
      IsMorphismOfSites (stageTopology i) (stageTopology j)
        (diagram.map a.op).toFunctor

/-- The index type of a cofiltered site diagram carries its stored small-category structure. -/
instance (S : CofilteredSiteDiagram.{uI, uC, vC}) : SmallCategory S.I :=
  S.smallCategoryI

/-- The index category of a cofiltered site diagram is cofiltered by the stored primitive data. -/
instance (S : CofilteredSiteDiagram.{uI, uC, vC}) : IsCofiltered S.I :=
  S.cofilteredI

/-- Each primitive transition functor in a cofiltered site diagram is a morphism of sites. -/
instance
    (S : CofilteredSiteDiagram.{uI, uC, vC}) {i j : S.I} (a : j ⟶ i) :
    IsMorphismOfSites (S.stageTopology i) (S.stageTopology j)
      (S.diagram.map a.op).toFunctor :=
  S.transition_isMorphismOfSites a

namespace CofilteredSiteDiagram

variable (S : CofilteredSiteDiagram.{uI, uC, vC})

/-- The stage category `\mathcal C_i` of the inverse system. This is a short owner-level name for
the repeatedly used object of the underlying `Cat`-valued diagram. -/
abbrev stage (i : S.I) := S.diagram.obj (op i)

/-- The stage category `\mathcal C_i` carries its canonical category structure from the
`Cat`-valued inverse-system diagram. -/
instance stageCategory (i : S.I) : Category (S.stage i) := inferInstance

/-- The stage transition functor `u_a : \mathcal C_i \to \mathcal C_j` attached to
`a : j ⟶ i`. This is the owner-level derived map underlying the later pullback functors on
sheaves. -/
abbrev stageFunctor {i j : S.I} (a : j ⟶ i) :
    S.stage i ⥤ S.stage j :=
  (S.diagram.map a.op).toFunctor

private theorem stageFunctor_id_eq (i : S.I) :
    S.stageFunctor (𝟙 i) = 𝟭 _ :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_id (op i))

private theorem stageFunctor_comp {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j) :
    S.stageFunctor (b ≫ a) = S.stageFunctor a ⋙ S.stageFunctor b :=
  congrArg Cat.Hom.toFunctor (S.diagram.map_comp a.op b.op)

/-- The source-facing finiteness of stage covering families induces the downstream finite-refinement
owner used later in the chapter. -/
instance stageTopology_hasFiniteRefinementProperty (i : S.I) (X : S.stage i) :
    (S.stageTopology i).HasFiniteRefinementProperty X := by
  refine GrothendieckTopology.hasFiniteRefinementProperty_of_covering_mem_finite ?_ X
  intro U R hR
  simpa [stage] using S.stageCovering_mem_finite hR

/-- The owner-level stage functor inherits the primitive transition-site morphism data stored in
the situation. -/
instance stageFunctor_isMorphismOfSites {i j : S.I} (a : j ⟶ i) :
    IsMorphismOfSites (S.stageTopology i) (S.stageTopology j) (S.stageFunctor a) := by
  simpa [stageFunctor] using S.transition_isMorphismOfSites a

/-- Every stage transition functor is continuous for the stage Grothendieck topologies. -/
instance stageFunctor_isContinuous {i j : S.I} (a : j ⟶ i) :
    Functor.IsContinuous (S.stageFunctor a) (S.stageTopology i) (S.stageTopology j) :=
  inferInstance

/-- The identity transition pullback is canonically the identity functor on stage sheaves. -/
noncomputable def stageSheafPullbackIdIso
    (A : Type*) [Category A] (i : S.I)
    [HasWeakSheafify (S.stageTopology i) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (𝟙 i)).op.HasLeftKanExtension F] :
    (S.stageFunctor (𝟙 i)).sheafPullback A (S.stageTopology i) (S.stageTopology i) ≅ 𝟭 _ :=
  let e := eqToIso (stageFunctor_id_eq S i)
  Adjunction.leftAdjointIdIso
    ((S.stageFunctor (𝟙 i)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology i))
    (Functor.sheafPushforwardContinuousId' e A (S.stageTopology i))

/-- Transition pullbacks compose in the canonical way. -/
noncomputable def stageSheafPullbackCompIso
    (A : Type*) [Category A]
    {i j k : S.I} (a : j ⟶ i) (b : k ⟶ j)
    [HasWeakSheafify (S.stageTopology j) A]
    [HasWeakSheafify (S.stageTopology k) A]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor a).op.HasLeftKanExtension F]
    [∀ F : (S.stage j)ᵒᵖ ⥤ A, (S.stageFunctor b).op.HasLeftKanExtension F]
    [∀ F : (S.stage i)ᵒᵖ ⥤ A, (S.stageFunctor (b ≫ a)).op.HasLeftKanExtension F] :
    (S.stageFunctor a).sheafPullback A (S.stageTopology i) (S.stageTopology j) ⋙
        (S.stageFunctor b).sheafPullback A (S.stageTopology j) (S.stageTopology k) ≅
      (S.stageFunctor (b ≫ a)).sheafPullback A (S.stageTopology i) (S.stageTopology k) :=
  let e := eqToIso (stageFunctor_comp S a b)
  Adjunction.leftAdjointCompIso
    ((S.stageFunctor a).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology j))
    ((S.stageFunctor b).sheafAdjunctionContinuous A
      (S.stageTopology j) (S.stageTopology k))
    ((S.stageFunctor (b ≫ a)).sheafAdjunctionContinuous A
      (S.stageTopology i) (S.stageTopology k))
    (Functor.sheafPushforwardContinuousComp' e.symm
      A (S.stageTopology i) (S.stageTopology j) (S.stageTopology k))

/-- The cocone functor from stage `i` to the colimit category of the inverse system. -/
noncomputable abbrev stageCoconeFunctor [HasColimit S.diagram] (i : S.I) :
    S.stage i ⥤ (colimit S.diagram : Cat.{vC, uC}) :=
  (colimit.ι S.diagram (op i)).toFunctor

/-- For an arrow `a : j ⟶ i`, the object `X ∈ \mathcal C_i` maps to `u_a(X) ∈ \mathcal C_j`. -/
abbrev overImage {i : S.I} (X : S.stage i) (A : (Over i)ᵒᵖ) :
    S.stage A.unop.left :=
  (S.stageFunctor A.unop.hom).obj X

end CofilteredSiteDiagram
