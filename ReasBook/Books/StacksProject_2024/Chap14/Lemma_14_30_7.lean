import Mathlib
import stacks_project.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Arrow
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open Simplicial
open SSet.modelCategoryQuillen

universe u v₁ v₂

attribute [local instance] Cardinal.fact_isRegular_aleph0

section

/-
Domain-style sampling for Lemma 14.30.7:
- primary domain: filtered colimits of simplicial-set morphisms carrying a right lifting property;
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `CategoryTheory.MorphismProperty.IsStableUnderFilteredColimits`,
  `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`,
  `CategoryTheory.MorphismProperty.colimitsOfShape_le`,
  `CategoryTheory.Arrow.preservesColimitsOfShape_leftFunc`,
  `CategoryTheory.Arrow.preservesColimitsOfShape_rightFunc`.
- best owner abstraction: the morphism property `I.rlp`;
- primitive-vs-derived split:
  primitive data: an arbitrary filtered arrow diagram `F` and the stagewise owner property
    `I.rlp ((F.obj j).hom)`;
  derived API: the cocone-point conclusion for an arbitrary colimit cocone in `Arrow SSet`.

Source/core/bridge triage:
- `source-facing`: filtered colimits of trivial Kan fibrations of simplicial sets;
- `core/canonical`: the owner property `I.rlp`;
- `bridge/view`: the cocone-point theorem below. -/

-- Proof sketch: rewrite trivial Kan fibrations as the morphisms in `I.rlp`, i.e. the maps with
-- the right lifting property against all boundary inclusions. Filtered colimits in `SSet` are
-- computed degreewise in `Type`, and filtered colimits of sets commute with the finite limits that
-- describe the simplices of boundaries, so any compatible family of stagewise lifts produces a
-- lift for the colimit arrow.
/-- Helper for Lemma 14.30.7: every simplicial boundary is finitely presentable. -/
lemma boundary_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u} (∂Δ[n] : SSet.{u}) := by
  infer_instance

/-- Helper for Lemma 14.30.7: every standard simplex is finitely presentable. -/
lemma simplex_isFinitelyPresentable (n : ℕ) :
    IsFinitelyPresentable.{u} (Δ[n] : SSet.{u}) := by
  infer_instance

/-- Helper for Lemma 14.30.7: a standard simplex is finitely presentable at the larger universe
needed for the filtered small-model descent. -/
lemma simplex_isFinitelyPresentable_large (n : ℕ) :
    IsFinitelyPresentable.{max u v₁ v₂} (Δ[n] : SSet.{u}) := by
  -- View `Δ[n]` through the lifted Yoneda embedding so the evaluation functor computes the
  -- relevant hom-sets in a universe where the filtered colimit shape is allowed.
  change IsCardinalPresentable.{max u v₁ v₂} (Δ[n] : SSet.{u}) Cardinal.aleph0
  rw [isCardinalPresentable_iff_isCardinalAccessible_uliftCoyoneda_obj.{max v₁ v₂}]
  constructor
  intro J _ _
  let e :
      uliftCoyoneda.{max v₁ v₂}.obj (op (Δ[n] : SSet.{u})) ≅
        (evaluation _ (Type u)).obj (op (SimplexCategory.mk n)) ⋙
          uliftFunctor.{max v₁ v₂, u} :=
    NatIso.ofComponents
      (fun P ↦
        Equiv.toIso ((Equiv.ulift.trans SSet.yonedaEquiv).trans Equiv.ulift.symm))
      (by
        intro P Q f
        ext x
        rfl)
  exact CategoryTheory.Limits.preservesColimitsOfShape_of_natIso e.symm

/-- Helper for Lemma 14.30.7: a lifting square against a boundary inclusion and a filtered-colimit
arrow already comes from one stage of the diagram. -/
lemma boundary_stagewise_square_of_filtered_colimit_square
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (X₁ X₂ : J ⥤ SSet.{u}) (c₁ : Cocone X₁) (c₂ : Cocone X₂)
    (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)
    (f : X₁ ⟶ X₂) (φ : c₁.pt ⟶ c₂.pt)
    (hφ : ∀ j, c₁.ι.app j ≫ φ = f.app j ≫ c₂.ι.app j)
    (n : ℕ) {t : (∂Δ[n] : SSet.{u}) ⟶ c₁.pt} {b : Δ[n] ⟶ c₂.pt}
    (hsq : t ≫ φ =
      (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b)) :
    ∃ (j : J) (u : (∂Δ[n] : SSet.{u}) ⟶ X₁.obj j) (v : Δ[n] ⟶ X₂.obj j),
      u ≫ c₁.ι.app j = t ∧
      v ≫ c₂.ι.app j = b ∧
      u ≫ f.app j =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v) := by
  -- Route correction: the intended proof descends the square through a small model of `J`.
  -- The remaining blocker is the boundary analogue of `simplex_isFinitelyPresentable_large`.
  -- Once `∂Δ[n]` is available as `IsFinitelyPresentable.{max u v₁ v₂}`, the stagewise factorization
  -- and equalization can follow the existing essentially-small filtered-colimit API.
  sorry

/-- Helper for Lemma 14.30.7: the structure map of an arrow-valued cocone commutes with each stage
arrow after projecting to source and target simplicial sets. -/
lemma arrow_cocone_hom_naturality
    {J : Type v₁} [Category.{v₂} J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (j : J) :
    (Arrow.leftFunc.mapCocone c).ι.app j ≫ c.pt.hom =
      (F.obj j).hom ≫ (Arrow.rightFunc.mapCocone c).ι.app j := by
  -- Read the cocone component in `Arrow SSet` as a commutative square in `SSet`.
  simpa using Arrow.w (c.ι.app j)

instance : IsStableUnderFilteredColimits (I.rlp : MorphismProperty SSet.{u}) := by
  constructor
  intro J _ _
  constructor
  intro X₁ X₂ c₁ c₂ hc₁ hc₂ f hf φ hφ
  intro A B g hg
  have hg' :
      ∃ n, Arrow.mk g =
        Arrow.mk (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) := by
    simpa [I, MorphismProperty.ofHoms_iff] using hg
  obtain ⟨n, hg'⟩ := hg'
  let p : (∂Δ[n] : SSet.{u}) ⟶ Δ[n] := (∂Δ[n]).ι
  have hp : HasLiftingProperty p φ := by
    -- Route correction: instead of reconstructing the colimit degreewise, descend the lifting
    -- square to one finite stage and lift there.
    rw [Arrow.hasLiftingProperty_iff]
    intro ψ
    obtain ⟨j, u, v, hu, hv, hsquare⟩ :=
      boundary_stagewise_square_of_filtered_colimit_square X₁ X₂ c₁ c₂ hc₁ hc₂ f φ hφ n ψ.w
    have hj : HasLiftingProperty p (f.app j) :=
      hf j _ (boundary_ι_mem_I n)
    let sqStage : CommSq u p (f.app j) v := CommSq.mk hsquare
    let liftStage : Δ[n] ⟶ X₁.obj j := sqStage.lift
    have hright_stage : liftStage ≫ f.app j = v := by
      simpa [liftStage] using sqStage.fac_right
    have hfac_right : (liftStage ≫ c₁.ι.app j) ≫ φ = v ≫ c₂.ι.app j := by
      -- The stagewise filler remains a filler after composing into the colimit cocone.
      calc
        (liftStage ≫ c₁.ι.app j) ≫ φ = liftStage ≫ (c₁.ι.app j ≫ φ) := by
          simp [Category.assoc]
        _ = liftStage ≫ (f.app j ≫ c₂.ι.app j) := by
          exact congrArg (fun k ↦ liftStage ≫ k) (hφ j)
        _ = (liftStage ≫ f.app j) ≫ c₂.ι.app j := by
          simp [Category.assoc]
        _ = v ≫ c₂.ι.app j := by
          exact congrArg (fun k ↦ k ≫ c₂.ι.app j) hright_stage
    -- Lift at stage `j`, then compose with the colimit cocone to obtain a lift upstairs.
    refine ⟨{ l := liftStage ≫ c₁.ι.app j, fac_left := ?_, fac_right := ?_ }⟩
    · calc
        p ≫ (liftStage ≫ c₁.ι.app j) = (p ≫ liftStage) ≫ c₁.ι.app j := by
          simp [Category.assoc]
        _ = u ≫ c₁.ι.app j := by
          simpa [liftStage, Category.assoc] using
            congrArg (fun k ↦ k ≫ c₁.ι.app j) sqStage.fac_left
        _ = ψ.left := hu
    · exact hfac_right.trans (by simpa using hv)
  -- Finally transport the lifting property back from the identified boundary inclusion.
  letI : HasLiftingProperty p φ := hp
  exact HasLiftingProperty.of_arrow_iso_left (eqToIso hg'.symm) φ

theorem boundaryInclusions_rlp_colimit_of_filtered_diagram
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, I.rlp ((F.obj j).hom)) :
    I.rlp (c.pt.hom) := by
  let X₁ : J ⥤ SSet.{u} := F ⋙ Arrow.leftFunc
  let X₂ : J ⥤ SSet.{u} := F ⋙ Arrow.rightFunc
  let c₁ : Cocone X₁ := Arrow.leftFunc.mapCocone c
  let c₂ : Cocone X₂ := Arrow.rightFunc.mapCocone c
  let η : X₁ ⟶ X₂ :=
    Functor.whiskerLeft F (Comma.natTrans (𝟭 SSet.{u}) (𝟭 SSet.{u}))
  -- Package the stagewise trivial-Kan-fibration hypotheses as a morphism-property statement
  -- on the natural transformation between the source and target diagrams.
  have hη : (I.rlp : MorphismProperty SSet.{u}).functorCategory J η := by
    intro j
    simpa [η] using hF j
  -- The cocone equations in `Arrow SSet` give the compatibility needed by `colimitsOfShape.mk'`.
  have hφ : ∀ j, c₁.ι.app j ≫ c.pt.hom = η.app j ≫ c₂.ι.app j := by
    intro j
    simpa [X₁, X₂, c₁, c₂, η] using arrow_cocone_hom_naturality F c j
  have hcolims : IsColimit c₁ × IsColimit c₂ := by
    -- TODO: project the arrow-valued colimit cocone to source and target cocones without assuming
    -- ambient `HasColimitsOfShape J SSet`; this is the remaining wrapper-level blocker.
    sorry
  let W : MorphismProperty SSet.{u} := I.rlp
  have hW : W.IsStableUnderColimitsOfShape J := inferInstance
  exact hW.condition X₁ X₂ c₁ c₂ hcolims.1 hcolims.2 η hη c.pt.hom hφ

end
