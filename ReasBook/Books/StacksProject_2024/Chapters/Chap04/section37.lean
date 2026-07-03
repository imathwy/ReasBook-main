import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_4_37_1 (from Chap04) -/
universe w v₁ v₂ u

namespace CategoryTheory
namespace Pseudofunctor.CoGrothendieck

open HasFibers
open Opposite
open scoped CategoryTheory.Bicategory

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/- Domain-style sampling for Example 4.37.1:
- primary domain: co-Grothendieck constructions of contravariant groupoid-valued functors and
  categories fibred in groupoids.
- inspected owner-level declarations:
  `Pseudofunctor.CoGrothendieck.forget`,
  `HasFibers.inducedFunctor`,
  `IsFibredInGroupoids`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`.
- best owner abstraction: `IsFibredInGroupoids` on the canonical projection
  `forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')`; the groupoid-valued presheaf is primitive
  data, while the fibred-in-groupoids structure is derived.
- primitive data: `F : 𝒞ᵒᵖ ⥤ Grpd`.
- derived API: the source-facing theorem `groupoidPresheafProjection_isFibredInGroupoids` and
  the resulting canonical `IsFibredInGroupoids` instance on the projection.

Source/core/bridge triage:
- `source-facing`: Example 4.37.1, asserting that the split category attached to a presheaf of
  groupoids is fibred in groupoids over the base.
- `core/canonical`: `Pseudofunctor.CoGrothendieck.forget`, `HasFibers.inducedFunctor`, and
  `IsFibredInGroupoids`.
- `bridge/view`: the passage from `F : 𝒞ᵒᵖ ⥤ Grpd` to the underlying `Cat`-valued pseudofunctor
  `(F ⋙ Grpd.forgetToCat).toPseudofunctor'`. -/

/- Example 4.37.1: for a presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd`, the associated category
`𝒮_F` over `𝒞` is the canonical projection `forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')`
from the
co-Grothendieck construction of the underlying `Cat`-valued pseudofunctor. -/
example (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    ∫ᶜ ((F ⋙ Grpd.forgetToCat).toPseudofunctor') ⥤ 𝒞
    :=
  forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')

private instance groupoidPresheafProjection_fiber_isGroupoid
    (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) (U : 𝒞) :
    IsGroupoid ((forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')).Fiber U) := by
  let p := forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')
  haveI : IsGroupoid (Fib p U) := by
    change IsGroupoid (F.obj (op U))
    infer_instance
  simpa [p] using
    (isGroupoid_of_reflects_iso (HasFibers.inducedFunctor p U).asEquivalence.symm.functor :
      IsGroupoid (p.Fiber U))

-- Proof sketch: the co-Grothendieck construction attached to `(F ⋙ Grpd.forgetToCat)` is
-- fibered by the canonical cartesian lifts from `FiberedCategory.Grothendieck`. Since each fiber
-- category is a groupoid because `F` lands in `Grpd`, Lemma 4.35.2 upgrades this to a category
-- fibred in groupoids.
/-- Example 4.37.1: for a presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd`, the canonical projection
`forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor') : 𝒮_F ⥤ 𝒞` is fibred in groupoids. -/
theorem groupoidPresheafProjection_isFibredInGroupoids
    (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    IsFibredInGroupoids (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) inferInstance ?_
  intro U
  infer_instance

instance (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    IsFibredInGroupoids (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) :=
  groupoidPresheafProjection_isFibredInGroupoids F

end Pseudofunctor.CoGrothendieck
end CategoryTheory

/-! ### Definition_4_37_2 (from Chap04) -/
universe v₁ v₂ u₁ u₂

open Opposite
open scoped CategoryTheory.Bicategory

namespace CategoryTheory

namespace Functor

open BasedFunctor
open HasFibers
open Pseudofunctor
open Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/- Domain-style sampling for Definition 4.37.2:
- primary domain: split fibred categories over a fixed base whose split model comes from a
  groupoid-valued presheaf via the co-Grothendieck construction.
- inspected owner-level declarations:
  `Functor.IsSplitFibredCategory`,
  `IsFibredInGroupoids`,
  `Pseudofunctor.CoGrothendieck.groupoidPresheafProjection_isFibredInGroupoids`,
  `HasFibers.inducedFunctor`.
- best owner abstraction: the source-facing notion is the conjunction of the existing owners
  `Functor.IsSplitFibredCategory p` and `IsFibredInGroupoids p`; the textbook groupoid-valued
  model is bridge/view data, not a separate owner.
- primitive data: only the upstream split and fibred-in-groupoids owner predicates on `p`.
- derived API: the textbook existence of a presheaf `F : Cᵒᵖ ⥤ Grpd` whose co-Grothendieck model
  is isomorphic over `C` to `p`.

Source/core/bridge triage:
- `source-facing`: the conjunction `Functor.IsSplitFibredCategory p ∧ IsFibredInGroupoids p`.
- `core/canonical`: the owner predicates `Functor.IsSplitFibredCategory p` and
  `IsFibredInGroupoids p`.
- `bridge/view`: the textbook existential model by a groupoid-valued presheaf, the canonical
  example `groupoidPresheafProjection_isFibredInGroupoids`, and the fibre-identification
  equivalence `HasFibers.inducedFunctor`. -/

section

variable (p : S ⥤ C)

/- Definition 4.37.2: a functor `p : S ⥤ C` is split fibred in groupoids exactly when it
satisfies the existing owner predicates `p.IsSplitFibredCategory` and `IsFibredInGroupoids p`.
The groupoid-valued presheaf model constructed below is companion bridge data, not a separate
owner. -/
#check (p.IsSplitFibredCategory ∧ IsFibredInGroupoids p)

end

namespace IsSplitFibredCategory

/-- If `p` is split fibred and fibred in groupoids, then `p` admits the textbook
groupoid-valued split model over `C`. -/
theorem exists_groupoidPresheafModel
    (p : S ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        ∃ eInv : BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) ⥤ᵇ
            BasedCategory.ofFunctor p,
          e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
            eInv ⋙ e =
              𝟙 (BasedCategory.ofFunctor
                (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor'))) := by
  rcases (inferInstance : p.IsSplitFibredCategory).existsCoGrothendieckModel with ⟨F, e, eInv, hη, hε⟩
  let pF := CoGrothendieck.forget (F.toPseudofunctor')
  have hpF_fiber (U : C) : IsGroupoid (pF.Fiber U) := by
    letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
      simpa using (inferInstance : IsGroupoid (p.Fiber U))
    let he : e.IsEquivalenceOverBase :=
      BasedFunctor.IsEquivalenceOverBase.mkPrime
        eInv
        (eqToIso hη.symm)
        (eqToIso hε)
    exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase e he U
  let FObjGrpd : ∀ U : Cᵒᵖ, Grpd.{v₂, u₂} := fun U ↦ by
    let G := HasFibers.inducedFunctor pF (unop U)
    letI : G.ReflectsIsomorphisms := inferInstance
    letI : IsGroupoid (pF.Fiber (unop U)) := hpF_fiber (unop U)
    letI : IsGroupoid (F.obj U) := by
      simpa [pF] using (isGroupoid_of_reflects_iso G)
    letI : Groupoid (F.obj U) := Groupoid.ofIsGroupoid
    exact Grpd.of (F.obj U)
  let FGrpd : Cᵒᵖ ⥤ Grpd.{v₂, u₂} :=
    { obj := FObjGrpd
      map := fun f ↦ by
        exact (F.map f).toFunctor
      map_id := fun U ↦ by
        change (F.map (𝟙 U)).toFunctor = 𝟭 (F.obj U)
        exact congrArg Cat.Hom.toFunctor (F.map_id U)
      map_comp := fun f g ↦ by
        change (F.map (f ≫ g)).toFunctor = (F.map f).toFunctor ⋙ (F.map g).toFunctor
        exact congrArg Cat.Hom.toFunctor (F.map_comp f g) }
  have hforget :
      CoGrothendieck.forget ((FGrpd ⋙ Grpd.forgetToCat).toPseudofunctor') = pF := by
    rfl
  refine ⟨FGrpd, ?_, ?_, ?_⟩
  · cases hforget
    exact e
  · cases hforget
    exact eInv
  · cases hforget
    exact ⟨hη, hε⟩

/-- Owner-level bridge: a split category fibred in groupoids is equivalent over the base to the
canonical co-Grothendieck model of a groupoid-valued presheaf. -/
theorem exists_groupoidPresheafModel_over_base
    (p : S ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  rcases IsSplitFibredCategory.exists_groupoidPresheafModel p with
    ⟨F, e, eInv, hη, hε⟩
  refine ⟨F, e, ?_⟩
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      eInv
      (eqToIso hη.symm)
      (eqToIso hε)

end IsSplitFibredCategory

/-- Companion specification for Definition 4.37.2: the owner-level conjunction
`p.IsSplitFibredCategory ∧ IsFibredInGroupoids p` is equivalent to the textbook existence of a
groupoid-valued presheaf model whose co-Grothendieck construction is isomorphic over `C` to
`p`. -/
theorem splitFibredCategory_and_fibredInGroupoids_iff_exists_groupoidPresheafModel
    {p : S ⥤ C} :
    (p.IsSplitFibredCategory ∧ IsFibredInGroupoids p) ↔
      ∃ F : Cᵒᵖ ⥤ Grpd.{v₂, u₂},
        ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
            BasedCategory.ofFunctor
              (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
          ∃ eInv : BasedCategory.ofFunctor
              (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) ⥤ᵇ
              BasedCategory.ofFunctor p,
            e ⋙ eInv = 𝟙 (BasedCategory.ofFunctor p) ∧
              eInv ⋙ e =
                𝟙 (BasedCategory.ofFunctor
                  (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor'))) := by
  constructor
  · rintro ⟨hpSplit, hpGroupoids⟩
    letI := hpSplit
    letI := hpGroupoids
    exact IsSplitFibredCategory.exists_groupoidPresheafModel p
  · rintro ⟨F, e, eInv, hη, hε⟩
    let hpSplit : p.IsSplitFibredCategory := ⟨⟨(F ⋙ Grpd.forgetToCat), e, eInv, hη, hε⟩⟩
    let pF := CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')
    let hpGroupoids : IsFibredInGroupoids p := by
      letI : IsFibredInGroupoids pF := groupoidPresheafProjection_isFibredInGroupoids F
      exact
        isFibredInGroupoids_of_isFibered_and_fiber_groupoid p
          hpSplit.isFibered
          fun U ↦ by
            letI : IsGroupoid (pF.Fiber U) := IsFibredInGroupoids.fiber_isGroupoid U
            letI : IsGroupoid ((BasedCategory.ofFunctor pF).p.Fiber U) := by
              simpa using (inferInstance : IsGroupoid (pF.Fiber U))
            let heInv : eInv.IsEquivalenceOverBase :=
              BasedFunctor.IsEquivalenceOverBase.mkPrime
                e
                (eqToIso hε.symm)
                (eqToIso hη)
            exact
              BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase
                eInv heInv U
    exact ⟨hpSplit, hpGroupoids⟩

end Functor
end CategoryTheory

/-! ### Lemma_4_37_3 (from Chap04) -/
universe v₁ v₂ u₁ u₂ u₃

open Opposite
open scoped CategoryTheory.Bicategory

namespace CategoryTheory

open BasedFunctor
open HasFibers
open Pseudofunctor
open Pseudofunctor.CoGrothendieck

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type (max u₁ u₂)} [Category.{max v₁ v₂} S]

namespace IsFibredInGroupoids

/-- Helper for Lemma 4.37.3: the strictification comparison equivalence in
`FibredCategoryOver C` induces an equivalence over the base on the underlying based functors. -/
private theorem strictification_comparison_isEquivalenceOverBase
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver C) (e : FibredCategoryOver.ofFunctor p ≌ Y) :
    ((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
      BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory).IsEquivalenceOverBase := by
  -- Forget the sub-`2`-category structure on the unit and counit to recover a based equivalence.
  let etaIso :
      𝟙 (BasedCategory.ofFunctor p) ≅
        (((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
            BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory) ⋙
          ((e.inv.obj.obj : Y.obj ⟶ (FibredCategoryOver.ofFunctor p).obj) :
            Y.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor p)) := by
    simpa using
      Functor.mapIso
        (((fibredCategoryOverSubTwoCategory C).hom
          (FibredCategoryOver.ofFunctor p)
          (FibredCategoryOver.ofFunctor p)).inclusion)
        e.unit
  let epsIso :
      (((e.inv.obj.obj : Y.obj ⟶ (FibredCategoryOver.ofFunctor p).obj) :
          Y.toBasedCategory ⥤ᵇ BasedCategory.ofFunctor p) ⋙
        ((e.hom.obj.obj : (FibredCategoryOver.ofFunctor p).obj ⟶ Y.obj) :
          BasedCategory.ofFunctor p ⥤ᵇ Y.toBasedCategory)) ≅
        𝟙 Y.toBasedCategory := by
    simpa using
      Functor.mapIso
        (((fibredCategoryOverSubTwoCategory C).hom Y Y).inclusion)
        e.counit
  let eBased : BasedCategory.ofFunctor p ≌ Y.toBasedCategory :=
    Bicategory.Equivalence.mkOfAdjointifyCounit etaIso epsIso
  exact BasedFunctor.hom_isEquivalenceOverBase eBased

/-- Helper for Lemma 4.37.3: the based strictification equivalence over the base transports the
groupoid structure on each fiber from `p` to the strictified target. -/
private theorem strictification_target_fiber_isGroupoid
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver.{v₁, u₁, max u₁ (max u₂ v₁), max v₁ v₂} C)
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p)
    (hF : F.IsEquivalenceOverBase) (U : C) :
    IsGroupoid (Y.p.Fiber U) := by
  -- Transport the source fiber groupoid structure across the strictification equivalence.
  letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
    simpa using (inferInstance : IsGroupoid (p.Fiber U))
  exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase F hF U

/-- Helper for Lemma 4.37.3: the strictification target is again fibred in groupoids once each
fiber has been transported from the source. -/
private theorem strictification_target_isFibredInGroupoids
    (p : S ⥤ C) [IsFibredInGroupoids p]
    (Y : FibredCategoryOver.{v₁, u₁, max u₁ (max u₂ v₁), max v₁ v₂} C)
    (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p)
    (hF : F.IsEquivalenceOverBase) :
    IsFibredInGroupoids Y.p := by
  -- Upgrade fiberwise groupoids on the strictification target using Lemma 4.35.2.
  exact
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid Y.p inferInstance
      (fun U ↦ strictification_target_fiber_isGroupoid p Y F hF U)

/-- Helper for Lemma 4.37.3: a split category fibred in groupoids admits the expected
groupoid-valued co-Grothendieck model over the base. -/
private theorem split_groupoidPresheafModel_over_base
    {T : Type u₃} [Category.{max v₁ v₂} T]
    (p : T ⥤ C) [p.IsSplitFibredCategory] [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, u₃},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (CoGrothendieck.forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  -- Unpack the split Cat-valued model and then upgrade each fiber to a small groupoid.
  rcases (inferInstance : p.IsSplitFibredCategory).existsCoGrothendieckModel with
    ⟨F, e, eInv, hη, hε⟩
  let pF := CoGrothendieck.forget (F.toPseudofunctor')
  have hpF_fiber (U : C) : IsGroupoid (pF.Fiber U) := by
    -- Transport the source fiber groupoids across the given equivalence over the base.
    letI : IsGroupoid ((BasedCategory.ofFunctor p).p.Fiber U) := by
      simpa using (inferInstance : IsGroupoid (p.Fiber U))
    let he : e.IsEquivalenceOverBase :=
      BasedFunctor.IsEquivalenceOverBase.mkPrime
        eInv
        (eqToIso hη.symm)
        (eqToIso hε)
    exact BasedFunctor.fiber_isGroupoid_of_isEquivalenceOverBase e he U
  let FObjGrpd : ∀ U : Cᵒᵖ, Grpd.{max v₁ v₂, u₃} := fun U ↦ by
    -- Identify the model fiber with `F.obj U` and use that transported groupoid structure.
    let G := HasFibers.inducedFunctor pF (unop U)
    letI : G.ReflectsIsomorphisms := inferInstance
    letI : IsGroupoid (pF.Fiber (unop U)) := hpF_fiber (unop U)
    letI : IsGroupoid (F.obj U) := by
      simpa [pF] using (isGroupoid_of_reflects_iso G)
    letI : Groupoid (F.obj U) := Groupoid.ofIsGroupoid
    exact Grpd.of (F.obj U)
  let FGrpd : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, u₃} :=
    { obj := FObjGrpd
      map := fun f ↦ by
        exact (F.map f).toFunctor
      map_id := fun U ↦ by
        change (F.map (𝟙 U)).toFunctor = 𝟭 (F.obj U)
        exact congrArg Cat.Hom.toFunctor (F.map_id U)
      map_comp := fun f g ↦ by
        change (F.map (f ≫ g)).toFunctor = (F.map f).toFunctor ⋙ (F.map g).toFunctor
        exact congrArg Cat.Hom.toFunctor (F.map_comp f g) }
  have hforget :
      CoGrothendieck.forget ((FGrpd ⋙ Grpd.forgetToCat).toPseudofunctor') = pF := by
    rfl
  refine ⟨FGrpd, ?_⟩
  cases hforget
  refine ⟨e, ?_⟩
  exact
    BasedFunctor.IsEquivalenceOverBase.mkPrime
      eInv
      (eqToIso hη.symm)
      (eqToIso hε)

/-- Lemma 4.37.3: every category fibred in groupoids `p : S ⥤ C` is equivalent over `C` to the
split category attached to a contravariant groupoid-valued presheaf on `C`. -/
theorem exists_groupoidPresheafModel_over_base
    (p : S ⥤ C) [IsFibredInGroupoids p] :
    ∃ F : Cᵒᵖ ⥤ Grpd.{max v₁ v₂, max u₁ (max u₂ v₁)},
      ∃ e : BasedCategory.ofFunctor p ⥤ᵇ
          BasedCategory.ofFunctor
            (Pseudofunctor.CoGrothendieck.forget
              ((F ⋙ Grpd.forgetToCat).toPseudofunctor')),
        e.IsEquivalenceOverBase := by
  -- Route correction: strictify only to obtain a split model over `C`, then apply the already
  -- proved split-case theorem from Definition 4.37.2 to that target and compose the equivalences.
  have hsplit :
      ∃ (Y : FibredCategoryOver.{v₁, u₁, max u₁ (max u₂ v₁), max v₁ v₂} C)
        (e : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor Y.p),
        e.IsEquivalenceOverBase ∧ Functor.IsSplitFibredCategory Y.p :=
    exists_split_fibred_category_over_base p
  rcases hsplit with ⟨Y, e, hStrict, hYsplit⟩
  have hYgroupoids : IsFibredInGroupoids Y.p :=
    strictification_target_isFibredInGroupoids p Y e hStrict
  letI := hYsplit
  letI := hYgroupoids
  -- Apply the split-case groupoid model to the strictified target and pull it back to `p`.
  rcases split_groupoidPresheafModel_over_base Y.p with ⟨F, eY, hY⟩
  refine ⟨F, e ⋙ eY, ?_⟩
  exact BasedFunctor.IsEquivalenceOverBase.comp hStrict hY

end IsFibredInGroupoids

end CategoryTheory
