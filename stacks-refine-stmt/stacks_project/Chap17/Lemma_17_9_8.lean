import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Small
import stacks_project.Chap17.Lemma_17_9_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u v u'

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

local notation "ModR" => SheafOfModules R
local notation "Pft" => SheafOfModules.isFiniteType R

/- Domain-style sampling for Lemma 17.9.8:
- primary domain: categorical smallness of finite type sheaves of modules over a sheaf of rings;
- inspected owner declarations:
  `SheafOfModules.IsFiniteType`,
  `SheafOfModules.isFiniteType`,
  `ObjectProperty.EssentiallySmall`,
  `ObjectProperty.EssentiallySmall.exists_small`;
- best owner abstraction:
  `SheafOfModules.isFiniteType R`;
- primitive data: the canonical owner predicate `SheafOfModules.IsFiniteType`;
- derived API: small subproperties whose iso-closure recovers that owner property.

Source/core/bridge triage:
- `source-facing`: the Stacks Project claim that finite type modules admit a set-sized family of
  representatives up to isomorphism;
- `core/canonical`: `ObjectProperty.EssentiallySmall
    (SheafOfModules.isFiniteType R)`;
- `bridge/view`: a small object property `P` with
  `SheafOfModules.isFiniteType R = P.isoClosure`;
- ringed-space specialization: take `R = RingedSpace.ringCatSheaf X`. -/

-- Proof sketch: finite type module sheaves are obtained by gluing quotient sheaves of
-- finite free modules along set-sized coverings and gluing data, so the finite-type object
-- property `SheafOfModules.IsFiniteType` is essentially small.
/-- Core/canonical companion to Lemma 17.9.8: finite type sheaves of modules over `R` form an
essentially small object property. -/
instance finiteTypeModuleProperty_essentiallySmall :
    ObjectProperty.EssentiallySmall Pft := by
  sorry

-- Proof sketch: apply the canonical `ObjectProperty.EssentiallySmall.exists_small` API to the
-- finite-type owner property, then choose one object from each isomorphism class in the skeleton
-- of the resulting small full subcategory.
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})] in
/-- Lemma 17.9.8: for a sheaf of rings `R`, there is a set of finite type `R`-module sheaves
containing exactly one representative of each isomorphism class of finite type modules. Applied to
`R = RingedSpace.ringCatSheaf X`, this recovers the ringed-space statement in the text. -/
theorem exists_set_of_finiteType_module_representatives :
    ∃ S : Set ModR,
      (∀ 𝒩 ∈ S, 𝒩.IsFiniteType) ∧
      ∀ (ℱ : ModR) [ℱ.IsFiniteType],
        ∃! 𝒩 : ModR, 𝒩 ∈ S ∧ Nonempty (𝒩 ≅ ℱ) := by
  obtain ⟨P, _, hP⟩ :=
    ObjectProperty.EssentiallySmall.exists_small.{u} Pft
  let F : Skeleton P.FullSubcategory ⥤ ModR :=
    fromSkeleton P.FullSubcategory ⋙ P.ι
  let S : Set ModR := Set.range F.obj
  refine ⟨S, ?_, ?_⟩
  · intro 𝒩 h𝒩
    rcases h𝒩 with ⟨q, rfl⟩
    let Y : P.FullSubcategory := (fromSkeleton P.FullSubcategory).obj q
    have hY : P Y.1 := Y.2
    have : P.isoClosure Y.1 := ObjectProperty.le_isoClosure P _ hY
    simpa [F, Y, hP] using this
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
