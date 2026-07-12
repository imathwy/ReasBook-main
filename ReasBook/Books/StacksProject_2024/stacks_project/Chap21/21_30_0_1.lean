import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Lemma_7_21_7
import StacksProject_2024.Chap18.Lemma_18_16_6
import StacksProject_2024.Chap07.Example_7_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- If `τ' ≤ τ`, then the induced localized topology over any object is again finer. -/
theorem comparisonOver_le (hle : τ' ≤ τ) (X : C) : τ'.over X ≤ τ.over X := by
  intro Y S hS
  exact hle _ hS

/-- The identity functor on `Over X` is continuous from the finer localized topology
`τ'.over X` to the coarser one `τ.over X`. -/
theorem comparisonOver_id_isContinuous
    (hle : τ' ≤ τ) (X : C) :
    Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) := by
  exact id_isContinuous_of_le (comparisonOver_le hle X)

/-- The identity functor on `Over X` is continuously reusable for the localized topology
comparison `τ' ≤ τ`. -/
instance comparisonOver_isContinuous
    (hle : τ' ≤ τ) (X : C) :
    Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
  comparisonOver_id_isContinuous hle X

/-- The identity functor on `Over X` is cocontinuous from the coarser localized topology
`τ.over X` to the finer one `τ'.over X`. -/
theorem comparisonOver_id_isCocontinuous
    (hle : τ' ≤ τ) (X : C) :
    Functor.IsCocontinuous (𝟭 (Over X)) (τ.over X) (τ'.over X) := by
  exact ⟨fun hS ↦ by simpa using hle _ hS⟩

variable {A : Type w} [Category A]

/-- The localized direct-image functor `f_{J,*}` on `A`-valued sheaves along `f : X ⟶ Y`. -/
noncomputable abbrev overMapPushforward
    (J : GrothendieckTopology C) (A : Type w) [Category A] {X Y : C} (f : X ⟶ Y)
    [HasPullbacksAlong f] :
    Sheaf (J.over X) A ⥤ Sheaf (J.over Y) A :=
  let _ : Functor.IsContinuous (Over.pullback f) (J.over Y) (J.over X) :=
    (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous (J.over X) (J.over Y)
  (Over.pullback f).sheafPushforwardContinuous A (J.over Y) (J.over X)

/-- If `f : X ⟶ Y` admits pullbacks, then the localized direct-image functor `f_{J,*}` on
abelian sheaves is additive whenever it agrees with the cocontinuous pushforward along
`Over.map f`. -/
instance overMapPushforward_additive
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    [Functor.Additive
      ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (J.over X) (J.over Y))] :
    Functor.Additive (J.overMapPushforward AddCommGrpCat.{max u v} f) := by
  let _ : Functor.IsContinuous (Over.pullback f) (J.over Y) (J.over X) :=
    (Over.mapPullbackAdj f).isContinuous_of_isCocontinuous (J.over X) (J.over Y)
  let e :
      (Over.pullback f).sheafPushforwardContinuous
          AddCommGrpCat.{max u v} (J.over Y) (J.over X) ≅
        (Over.map f).sheafPushforwardCocontinuous
          AddCommGrpCat.{max u v} (J.over X) (J.over Y) :=
    continuous_right_adjoint_sheafPushforwardContinuousIso_cocontinuousPushforward
      (Over.map f) (Over.pullback f) AddCommGrpCat.{max u v} (Over.mapPullbackAdj f)
  change Functor.Additive
    ((Over.pullback f).sheafPushforwardContinuous
      AddCommGrpCat.{max u v} (J.over Y) (J.over X))
  exact Functor.additive_of_iso e.symm

/-- Helper for localized topology comparison: the identity functor on `Over X` admits pointwise
left Kan extensions. -/
instance comparisonTopologyPullbackHasPointwiseLeftKanExtension
    (X : C) (F : (Over X)ᵒᵖ ⥤ A) :
    ((𝟭 (Over X)).op).HasPointwiseLeftKanExtension F := by
  intro U
  let T :
      IsTerminal (CostructuredArrow.mk (𝟙 U) : CostructuredArrow (𝟭 (Over X)).op U) :=
    CostructuredArrow.mkIdTerminal
  exact HasColimit.mk
    { cocone := _
      isColimit :=
        colimitOfDiagramTerminal T (CostructuredArrow.proj (𝟭 (Over X)).op U ⋙ F) }

/-- Helper for localized topology comparison: the identity functor on `Over X` admits left Kan
extensions. -/
instance comparisonTopologyPullbackHasLeftKanExtension
    (X : C) (F : (Over X)ᵒᵖ ⥤ A) :
    ((𝟭 (Over X)).op).HasLeftKanExtension F := by
  infer_instance

/-- The direct-image functor `ε_{X,*}` on `A`-valued sheaves for the localized comparison of the
topologies `τ` and `τ'`. -/
noncomputable abbrev comparisonTopologyPushforward
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) A ⥤ Sheaf (τ'.over X) A :=
  letI : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  (𝟭 (Over X)).sheafPushforwardContinuous A (τ'.over X) (τ.over X)

/-- The localized topology-comparison inverse image `ε_X⁻¹` on `A`-valued sheaves. -/
noncomputable abbrev comparisonTopologyPullback
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C) [HasWeakSheafify (τ.over X) A] :
    Sheaf (τ'.over X) A ⥤ Sheaf (τ.over X) A :=
  letI : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  letI :
      ((𝟭 (Over X)).sheafPushforwardContinuous A
        (τ'.over X) (τ.over X)).IsRightAdjoint :=
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (𝟭 (Over X)) A (τ'.over X) (τ.over X)).isRightAdjoint
  (𝟭 (Over X)).sheafPullback A (τ'.over X) (τ.over X)

/- Textbook notation for the localized topology-comparison inverse image `ε_X⁻¹`. -/
notation "ε[" hle "]_(" X ")⁻¹" => GrothendieckTopology.comparisonTopologyPullback _ hle X

/-- The localized topology-comparison adjunction `ε_X⁻¹ ⊣ ε_{X,*}` on `A`-valued sheaves. -/
noncomputable abbrev comparisonTopologyAdjunction
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C) [HasWeakSheafify (τ.over X) A] :
    ε[hle]_(X)⁻¹ ⊣ comparisonTopologyPushforward A hle X :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  (𝟭 (Over X)).sheafAdjunctionContinuous A (τ'.over X) (τ.over X)

/-- For the localized topology comparison, the adjunction unit
`ℱ ⟶ ε_{X,*}(ε_X⁻¹ ℱ)` is an isomorphism. -/
instance comparisonTopology_unit_isIso
    (A : Type w) [Category A] (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) A] (ℱ : Sheaf (τ'.over X) A) :
    IsIso ((comparisonTopologyAdjunction A hle X).unit.app ℱ) := by
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  simpa [comparisonTopologyAdjunction] using
    unit_isIso_sheafAdjunctionContinuous_of_fullyFaithful
      (τ'.over X) (τ.over X) (𝟭 (Over X)) ℱ

/-- The localized topology-comparison direct image `ε_{X,*}` on abelian sheaves. -/
noncomputable abbrev comparisonTopologyPushforwardAb
    (hle : τ' ≤ τ) (X : C) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ'.over X) AddCommGrpCat.{max u v} :=
  comparisonTopologyPushforward AddCommGrpCat.{max u v} hle X

/-- The localized topology-comparison inverse image `ε_X⁻¹` on abelian sheaves. -/
noncomputable abbrev comparisonTopologyPullbackAb
    (hle : τ' ≤ τ) (X : C) [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    Sheaf (τ'.over X) AddCommGrpCat.{max u v} ⥤
      Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  ε[hle]_(X)⁻¹

/-- The localized topology-comparison pushforward is additive on abelian sheaves. -/
instance comparisonTopologyPushforwardAb_additive
    (hle : τ' ≤ τ) (X : C) :
    Functor.Additive (comparisonTopologyPushforwardAb hle X) := by
  refine ⟨?_⟩
  intro ℱ 𝒢 f g
  ext U x
  rfl

/-- The localized topology-comparison pullback is additive on abelian sheaves. -/
instance comparisonTopologyPullbackAb_additive
    (hle : τ' ≤ τ) (X : C) [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    Functor.Additive (comparisonTopologyPullbackAb hle X) := by
  let u' : Over X ⥤ Over X := 𝟭 (Over X)
  let adj : u' ⊣ u' := by
    simpa [u'] using (Adjunction.id : 𝟭 (Over X) ⊣ 𝟭 (Over X))
  letI : Functor.IsContinuous u' (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  letI : Functor.IsCocontinuous u' (τ.over X) (τ'.over X) :=
    comparisonOver_id_isCocontinuous hle X
  letI (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : u'.op.HasLeftKanExtension F :=
    comparisonTopologyPullbackHasLeftKanExtension X F
  letI :
      Functor.Additive
        (u'.sheafPullbackCocontinuous AddCommGrpCat.{max u v} (τ.over X) (τ'.over X)) := by
    dsimp [Functor.sheafPullbackCocontinuous]
    infer_instance
  simpa [u', comparisonTopologyPullbackAb, comparisonTopologyPullback] using
    (Functor.additive_of_iso
      (sheafPullbackIso_sheafPullbackCocontinuous_of_leftAdjoint
        u' u' adj AddCommGrpCat.{max u v}).symm)

/-- The localized topology-comparison pullback preserves finite limits on abelian sheaves. -/
instance comparisonTopologyPullbackAb_preservesFiniteLimits
    (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    PreservesFiniteLimits (comparisonTopologyPullbackAb hle X) := by
  let u' : Over X ⥤ Over X := 𝟭 (Over X)
  let adj : u' ⊣ u' := by
    simpa [u'] using (Adjunction.id : 𝟭 (Over X) ⊣ 𝟭 (Over X))
  let _ : Functor.IsContinuous u' (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  let _ (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : u'.op.HasLeftKanExtension F :=
    comparisonTopologyPullbackHasLeftKanExtension X F
  let hExact :
      exactFunctor
        (Sheaf (τ'.over X) AddCommGrpCat.{max u v})
        (Sheaf (τ.over X) AddCommGrpCat.{max u v})
        (comparisonTopologyPullbackAb hle X) := by
    simpa [u', comparisonTopologyPullbackAb, comparisonTopologyPullback] using
      sheafPullback_addCommGrp_exact_of_leftAdjoint u' u' adj
  exact (exactFunctor_iff _).1 hExact |>.1

/-- The localized topology-comparison pullback preserves finite colimits on abelian sheaves. -/
instance comparisonTopologyPullbackAb_preservesFiniteColimits
    (hle : τ' ≤ τ) (X : C)
    [HasWeakSheafify (τ.over X) AddCommGrpCat.{max u v}]
    [HasSheafify (τ.over X) AddCommGrpCat.{max u v}] :
    PreservesFiniteColimits (comparisonTopologyPullbackAb hle X) := by
  let u' : Over X ⥤ Over X := 𝟭 (Over X)
  let adj : u' ⊣ u' := by
    simpa [u'] using (Adjunction.id : 𝟭 (Over X) ⊣ 𝟭 (Over X))
  let _ : Functor.IsContinuous u' (τ'.over X) (τ.over X) :=
    comparisonOver_id_isContinuous hle X
  let _ (F : (Over X)ᵒᵖ ⥤ AddCommGrpCat.{max u v}) : u'.op.HasLeftKanExtension F :=
    comparisonTopologyPullbackHasLeftKanExtension X F
  let hExact :
      exactFunctor
        (Sheaf (τ'.over X) AddCommGrpCat.{max u v})
        (Sheaf (τ.over X) AddCommGrpCat.{max u v})
        (comparisonTopologyPullbackAb hle X) := by
    simpa [u', comparisonTopologyPullbackAb, comparisonTopologyPullback] using
      sheafPullback_addCommGrp_exact_of_leftAdjoint u' u' adj
  exact (exactFunctor_iff _).1 hExact |>.2

end

end GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable {A : Type w} [Category A]
variable (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)

/- Domain-style sampling for 21.30.0.1:
- primary domain: change of Grothendieck topology on slice sites and its compatibility with
  relocalization along `f : X ⟶ Y`;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `GrothendieckTopology.overMapPullback`,
  `id_isContinuous_of_le`,
  `Functor.leftUnitor`,
  `Functor.rightUnitor`;
- source/core/bridge triage:
  `source-facing`: the compatibility of the topology-comparison morphisms `ε_X`, `ε_Y` with the
    relocalization morphisms attached to `f`;
  `core/canonical`: the sheaf-composition owner
    `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the specialization of that owner to the identity functors
    `𝟭 (Over X)` and `𝟭 (Over Y)` between the over-topologies `τ'.over _` and `τ.over _`,
    packaged below as the source-facing comparison functors.

Primitive data are only the comparison hypothesis `hle : τ' ≤ τ` and the morphism `f : X ⟶ Y`.
The localized topology-change pushforwards are already canonical sheaf pushforwards for the
identity functors on `Over X` and `Over Y`; the only local API worth keeping is the stable
source-facing owner name `ε_{X,*}`/`ε_X⁻¹` for downstream Chapter `21.30` use, together with the
specialized comparison isomorphism below.
-/

/- 21.30.0.1: the compatibility of `ε_X`, `ε_Y`, and relocalization along `f` is the canonical
specialization of `Functor.sheafPushforwardContinuousComp'` to the two identity functors on the
slice categories. -/
recall Functor.sheafPushforwardContinuousComp'

/- In Lean, the comparison `f_τ^{-1} ⋙ ε_X ≅ ε_Y ⋙ f_{τ'}^{-1}` is exactly the composite of the
left- and right-unitor specializations of the sheaf-composition owner theorem. -/
noncomputable abbrev overMapPullbackCompComparisonTopologyPushforward :
    τ.overMapPullback A f ⋙ GrothendieckTopology.comparisonTopologyPushforward A hle X ≅
      GrothendieckTopology.comparisonTopologyPushforward A hle Y ⋙ τ'.overMapPullback A f :=
  let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
    GrothendieckTopology.comparisonOver_id_isContinuous hle X
  let _ : Functor.IsContinuous (𝟭 (Over Y)) (τ'.over Y) (τ.over Y) :=
    GrothendieckTopology.comparisonOver_id_isContinuous hle Y
  let _ : (Over.map f).IsContinuous (τ'.over X) (τ.over Y) :=
    Functor.isContinuous_comp (𝟭 (Over X)) (Over.map f) (τ'.over X) (τ.over X) (τ.over Y)
  (Functor.sheafPushforwardContinuousComp'
      (Functor.leftUnitor (Over.map f)) A
      (τ'.over X) (τ.over X) (τ.over Y)) ≪≫
    (Functor.sheafPushforwardContinuousComp'
      (Functor.rightUnitor (Over.map f)) A
      (τ'.over X) (τ'.over Y) (τ.over Y)).symm

end

end CategoryTheory
