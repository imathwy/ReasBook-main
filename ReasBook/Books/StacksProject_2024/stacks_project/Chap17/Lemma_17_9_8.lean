import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small
import StacksProject_2024.Chap17.Definition_17_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v u'

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

local notation "ModR" => SheafOfModules R
local notation "Pft" => (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R))

/-- Helper for Lemma 17.9.8: restricting an `R`-module sheaf to `J.over X` is the canonical
pushforward functor along the identity comparison `R ⟶ (forget X)_* (R.over X)`. -/
abbrev overRestrictionFunctor (X : C) : ModR ⥤ SheafOfModules (R.over X) :=
  SheafOfModules.pushforward
    (CategoryTheory.CategoryStruct.id
      (((CategoryTheory.Over.forget X).sheafPushforwardContinuous RingCat (J.over X) J).obj R))

/- Domain-style sampling for Lemma 17.9.8:
- primary domain: categorical smallness of finite type sheaves of modules over a sheaf of rings;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.Small`,
  `ObjectProperty.EssentiallySmall`,
  `ObjectProperty.EssentiallySmall.exists_small`;
- best owner abstraction:
  the `ObjectProperty` view of `SheafOfModules.IsFiniteType` on `SheafOfModules R`;
- primitive data: the canonical owner predicate `SheafOfModules.IsFiniteType`;
- derived API: its isomorphism-closure instance, together with the generic
  `ObjectProperty.Small ⟹ ObjectProperty.EssentiallySmall` machinery and the representative-set
  theorem obtained from `ObjectProperty.EssentiallySmall.exists_small`.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claim that finite type modules admit a set-sized family of
  representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.IsClosedUnderIsomorphisms Pft` and the preexisting generic
  `ObjectProperty.EssentiallySmall Pft` instance synthesized from upstream smallness data;
- `bridge/view`: a small object property `P` with
  `(SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R)) = P.isoClosure`;
- ringed-space specialization: take `R = RingedSpace.ringCatSheaf X`. -/

/-- Finite-type sheaves of modules are stable under isomorphisms. -/
instance finiteTypeModuleProperty_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms Pft where
  of_iso := by
    intro M N e hM
    rcases hM.exists_localGeneratorsData with ⟨σ, hσ⟩
    let τ : N.LocalGeneratorsData :=
      { I := σ.I
        X := σ.X
        coversTop := σ.coversTop
        generators := fun i ↦
          let F : SheafOfModules.{u, v, u', u} R ⥤
              SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
            overRestrictionFunctor (R := R) (σ.X i)
          (σ.generators i).ofEpi (Functor.mapIso F e).hom }
    have hτ : τ.IsFiniteType := by
      refine SheafOfModules.LocalGeneratorsData.IsFiniteType.mk ?_
      intro i
      -- Each local generating family is transported along the restricted isomorphism.
      let F : SheafOfModules.{u, v, u', u} R ⥤
          SheafOfModules.{u, v, max u' v, u} (R.over (σ.X i)) :=
        overRestrictionFunctor (R := R) (σ.X i)
      refine SheafOfModules.GeneratingSections.IsFiniteType.mk ?_
      simpa [SheafOfModules.GeneratingSections.ofEpi, F] using
        ((hσ.isFiniteType i).finite : Finite (σ.generators i).I)
    exact ⟨τ, hτ⟩

end

section

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

local notation "ModR" => SheafOfModules R
local notation "Pft" => (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules R))

-- Proof sketch: apply the canonical `ObjectProperty.EssentiallySmall.exists_small` API to the
-- finite-type owner property, using the upstream `EssentiallySmall` instance synthesized from the
-- existing smallness data, then choose one object from each isomorphism class in the skeleton of
-- the resulting small full subcategory.
/-- Lemma 17.9.8: for a sheaf of rings `R`, there is a set of finite type `R`-module sheaves
containing exactly one representative of each isomorphism class of finite type modules. Applied to
`R = RingedSpace.ringCatSheaf X`, this recovers the ringed-space statement in the text. -/
theorem exists_set_of_finiteType_module_representatives
    : ∃ S : Set ModR,
      (∀ 𝒩 ∈ S, 𝒩.IsFiniteType) ∧
      ∀ (ℱ : ModR) [ℱ.IsFiniteType],
        ∃! 𝒩 : ModR, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℱ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{max (max (u + 1) u') v} Pft
  let F : Skeleton P.FullSubcategory ⥤ ModR :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set ModR := Set.range F.obj
  refine ⟨S, ?_, ?_⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨q, rfl⟩
    let Y : P.FullSubcategory := (fromSkeleton P.FullSubcategory).obj q
    have hY : P Y.1 := Y.2
    have hY' : Pft Y.1 := by
      simpa [hP] using (ObjectProperty.le_isoClosure P _ hY)
    simpa [F, Y] using hY'
  intro ℱ hℱ'
  letI : ℱ.IsFiniteType := hℱ'
  have hℱ : P.isoClosure ℱ := by
    rw [← hP]
    infer_instance
  rw [ObjectProperty.prop_isoClosure_iff] at hℱ
  rcases hℱ with ⟨M, hM, ⟨e⟩⟩
  let Y : P.FullSubcategory := ⟨M, hM⟩
  refine ⟨F.obj (toSkeleton Y), ?_, ?_⟩
  · constructor
    · exact ⟨toSkeleton Y, rfl⟩
    · exact ⟨(P.ι.mapIso (fromSkeletonToSkeletonIso Y)) ≪≫ e.symm⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨⟨q, rfl⟩, ⟨e'⟩⟩
    have hq : q = toSkeleton Y := by
      rw [← toSkeleton_fromSkeleton_obj q]
      exact (toSkeleton_eq_toSkeleton_iff).2 ⟨P.isoMk (e' ≪≫ e)⟩
    simpa using congrArg F.obj hq

end

end SheafOfModules
