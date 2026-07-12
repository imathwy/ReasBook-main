import Mathlib
import StacksProject_2024.Chap14.Definition_14_30_1

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
  `CategoryTheory.MorphismProperty.colimitsOfShape.mk'`.
- best owner abstraction: the morphism property `I.rlp`;
- primitive-vs-derived split:
  primitive data: an arbitrary filtered arrow diagram `F` and the stagewise owner property
    `I.rlp ((F.obj j).hom)`;
  derived API: the cocone-point conclusion for an arbitrary colimit cocone in `Arrow SSet`.

Source/core/bridge triage:
- `source-facing`: filtered colimits of trivial Kan fibrations of simplicial sets;
- `core/canonical`: the owner property `I.rlp`;
- `bridge/view`: the cocone-point theorem below. -/

-- Proof sketch: descend one boundary lifting square to a finite stage of the filtered diagram.
-- The boundary map is controlled by its finitely many codimension-one faces, so filtered colimits
-- of sets are enough once those face simplices have been moved to one common stage.

/-- Helper for Lemma 14.30.7: each codimension-one face of `Δ[n + 1]` factors through the
boundary. -/
private theorem stdSimplex_face_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.face {j}ᶜ ≤ SSet.boundary (n + 1) := by
  -- The boundary is the supremum of the codimension-one faces.
  rw [SSet.boundary_eq_iSup]
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j

/-- Helper for Lemma 14.30.7: the range of the `j`-th codimension-one face map lies in the
boundary. -/
private theorem stdSimplex_face_range_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    Subfunctor.range (SSet.stdSimplex.δ j) ≤ SSet.boundary (n + 1) := by
  -- Rewrite the face range into the standard face subcomplex.
  simpa [SSet.stdSimplex.range_δ] using stdSimplex_face_le_boundary (n := n) j

/-- Helper for Lemma 14.30.7: the `j`-th codimension-one face of the boundary simplex
`∂Δ[n + 1]`. -/
private def boundary_face (n : ℕ) (j : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subfunctor.lift (SSet.stdSimplex.δ j) (stdSimplex_face_range_le_boundary (n := n) j)

/-- Helper for Lemma 14.30.7: composing the boundary face inclusion with the boundary embedding
recovers the standard face map. -/
@[simp, reassoc]
private theorem boundary_face_ι (n : ℕ) (j : Fin (n + 2)) :
    boundary_face n j ≫ (∂Δ[n + 1]).ι = SSet.stdSimplex.δ j := by
  -- The lifted face map is defined by factoring `stdSimplex.δ j` through the boundary.
  simp [boundary_face]

/-- Helper for Lemma 14.30.7: morphisms out of a boundary simplex are determined by their
restrictions to the codimension-one faces. -/
private theorem boundary_hom_ext {n : ℕ} {S : SSet.{u}}
    (σ₁ σ₂ : (∂Δ[n + 1] : SSet.{u}) ⟶ S)
    (h :
      ∀ j : Fin (n + 2),
        boundary_face n j ≫ σ₁ = boundary_face n j ≫ σ₂) :
    σ₁ = σ₂ := by
  -- Equality on the generating face subcomplexes forces equality on the whole boundary.
  rw [← Subfunctor.equalizer_eq_iff]
  refine le_antisymm (Subfunctor.equalizer_le σ₁ σ₂) ?_
  simpa [SSet.boundary_eq_iSup] using
    (show (⨆ j : Fin (n + 2), SSet.stdSimplex.face {j}ᶜ) ≤ Subfunctor.equalizer σ₁ σ₂ from by
      simp only [iSup_le_iff]
      intro j
      rw [← SSet.stdSimplex.ofSimplex_yonedaEquiv_δ]
      rw [SSet.Subcomplex.ofSimplex_le_iff]
      refine (Subfunctor.mem_equalizer_iff σ₁ σ₂ (SSet.yonedaEquiv (boundary_face n j))).2 ?_
      -- Convert equality of maps `Δ[n] ⟶ S` into equality of the corresponding simplices.
      simpa [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv (h j))

/-- Helper for Lemma 14.30.7: a lifting square against a boundary inclusion and an arrow-valued
small filtered colimit already comes from one stage of the diagram. -/
private lemma boundary_stagewise_square_of_arrow_filtered_colimit_square_small
    {w} {J : Type w} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (n : ℕ)
    {t : (∂Δ[n] : SSet.{u}) ⟶ c.pt.left}
    {b : Δ[n] ⟶ c.pt.right}
    (hsq :
      t ≫ c.pt.hom =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b)) :
    ∃ (j : J) (u : (∂Δ[n] : SSet.{u}) ⟶ (F.obj j).left) (v : Δ[n] ⟶ (F.obj j).right),
      u ≫ (c.ι.app j).left = t ∧
      v ≫ (c.ι.app j).right = b ∧
      u ≫ (F.obj j).hom =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v) := by
  haveI : SSet.Finite (∂Δ[n] : SSet.{u}) := by infer_instance
  haveI : SSet.Finite (Δ[n] : SSet.{u}) := by infer_instance
  haveI : IsFinitelyPresentable (∂Δ[n] : SSet.{u}) := by infer_instance
  haveI : IsFinitelyPresentable (Δ[n] : SSet.{u}) := by infer_instance
  let cLeft : Cocone (F ⋙ Arrow.leftFunc) := Arrow.leftFunc.mapCocone c
  let cRight : Cocone (F ⋙ Arrow.rightFunc) := Arrow.rightFunc.mapCocone c
  have hcLeft : IsColimit cLeft := isColimitOfPreserves Arrow.leftFunc hc
  have hcRight : IsColimit cRight := isColimitOfPreserves Arrow.rightFunc hc
  -- Factor the boundary map and the simplex map through finite stages of the left and right
  -- colimit cocones.
  obtain ⟨jLeft, uLeft, huLeft⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcLeft t
  obtain ⟨jRight, vRight, hvRight⟩ := IsFinitelyPresentable.exists_hom_of_isColimit hcRight b
  let j₀ : J := IsFiltered.max jLeft jRight
  let toLeft : jLeft ⟶ j₀ := IsFiltered.leftToMax jLeft jRight
  let toRight : jRight ⟶ j₀ := IsFiltered.rightToMax jLeft jRight
  let u₀ : (∂Δ[n] : SSet.{u}) ⟶ (F.obj j₀).left := uLeft ≫ (F.map toLeft).left
  let v₀ : Δ[n] ⟶ (F.obj j₀).right := vRight ≫ (F.map toRight).right
  have hu₀ : u₀ ≫ (c.ι.app j₀).left = t := by
    -- Move the left-stage factorization to the common filtered stage.
    have hleft :
        (F.map toLeft).left ≫ (c.ι.app j₀).left = (c.ι.app jLeft).left := by
      exact congrArg Arrow.Hom.left (c.w toLeft)
    have hu₀_aux : uLeft ≫ (F.map toLeft).left ≫ (c.ι.app j₀).left = t := by
      have hmove : uLeft ≫ (F.map toLeft).left ≫ (c.ι.app j₀).left =
          uLeft ≫ (c.ι.app jLeft).left := by
        simpa [Category.assoc] using congrArg (fun k ↦ uLeft ≫ k) hleft
      have hstage : uLeft ≫ (c.ι.app jLeft).left = t := by
        simpa [cLeft] using huLeft
      exact hmove.trans hstage
    simpa [u₀, Category.assoc] using hu₀_aux
  have hv₀ : v₀ ≫ (c.ι.app j₀).right = b := by
    -- Move the right-stage factorization to the same common filtered stage.
    have hright :
        (F.map toRight).right ≫ (c.ι.app j₀).right = (c.ι.app jRight).right := by
      exact congrArg Arrow.Hom.right (c.w toRight)
    have hv₀_aux : vRight ≫ (F.map toRight).right ≫ (c.ι.app j₀).right = b := by
      have hmove : vRight ≫ (F.map toRight).right ≫ (c.ι.app j₀).right =
          vRight ≫ (c.ι.app jRight).right := by
        simpa [Category.assoc] using congrArg (fun k ↦ vRight ≫ k) hright
      have hstage : vRight ≫ (c.ι.app jRight).right = b := by
        simpa [cRight] using hvRight
      exact hmove.trans hstage
    simpa [v₀, Category.assoc] using hv₀_aux
  have hsq₀ :
      (u₀ ≫ (F.obj j₀).hom) ≫ (c.ι.app j₀).right =
        ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫ (c.ι.app j₀).right) := by
    -- The original commutative square still commutes after moving both factors to `j₀`.
    have hleftcol :
        (u₀ ≫ (F.obj j₀).hom) ≫ (c.ι.app j₀).right = t ≫ c.pt.hom := by
      calc
        (u₀ ≫ (F.obj j₀).hom) ≫ (c.ι.app j₀).right = (u₀ ≫ (c.ι.app j₀).left) ≫ c.pt.hom := by
          simpa [Category.assoc] using congrArg (fun k ↦ u₀ ≫ k) (Arrow.w (c.ι.app j₀))
        _ = t ≫ c.pt.hom := by
          simpa [Category.assoc] using congrArg (fun k ↦ k ≫ c.pt.hom) hu₀
    have hrightcol :
        ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫ (c.ι.app j₀).right) =
          ((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ ((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ k) hv₀
    exact hleftcol.trans (hsq.trans hrightcol.symm)
  -- Equalize the remaining square relation later in the filtered system on the right side.
  obtain ⟨k, α, β, hEq⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hcRight
    (u₀ ≫ (F.obj j₀).hom) (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) hsq₀
  let j : J := IsFiltered.coeq α β
  let γ : k ⟶ j := IsFiltered.coeqHom α β
  let u : (∂Δ[n] : SSet.{u}) ⟶ (F.obj j).left := u₀ ≫ (F.map (α ≫ γ)).left
  let v : Δ[n] ⟶ (F.obj j).right := v₀ ≫ (F.map (β ≫ γ)).right
  have hu : u ≫ (c.ι.app j).left = t := by
    -- Pushing the left factor forward along the cocone leaves the map to the colimit unchanged.
    have hleft :
        (F.map (α ≫ γ)).left ≫ (c.ι.app j).left = (c.ι.app j₀).left := by
      exact congrArg Arrow.Hom.left (c.w (α ≫ γ))
    have hu_aux : u₀ ≫ (F.map (α ≫ γ)).left ≫ (c.ι.app j).left = t := by
      have hmove : u₀ ≫ (F.map (α ≫ γ)).left ≫ (c.ι.app j).left =
          u₀ ≫ (c.ι.app j₀).left := by
        simpa [Category.assoc] using congrArg (fun k ↦ u₀ ≫ k) hleft
      exact hmove.trans hu₀
    simpa [u, Category.assoc] using hu_aux
  have hv : v ≫ (c.ι.app j).right = b := by
    -- The same cocone naturality argument works on the right side.
    have hright :
        (F.map (β ≫ γ)).right ≫ (c.ι.app j).right = (c.ι.app j₀).right := by
      exact congrArg Arrow.Hom.right (c.w (β ≫ γ))
    have hv_aux : v₀ ≫ (F.map (β ≫ γ)).right ≫ (c.ι.app j).right = b := by
      have hmove : v₀ ≫ (F.map (β ≫ γ)).right ≫ (c.ι.app j).right =
          v₀ ≫ (c.ι.app j₀).right := by
        simpa [Category.assoc] using congrArg (fun k ↦ v₀ ≫ k) hright
      exact hmove.trans hv₀
    simpa [v, Category.assoc] using hv_aux
  have hEq' :
      (u₀ ≫ (F.obj j₀).hom) ≫ (F.map (α ≫ γ)).right =
        ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫ (F.map (β ≫ γ)).right) := by
    -- Compose the stagewise equality with a coequalizer map so both transports land in `j`.
    calc
      (u₀ ≫ (F.obj j₀).hom) ≫ (F.map (α ≫ γ)).right =
          (((u₀ ≫ (F.obj j₀).hom) ≫ (F.map α).right) ≫ (F.map γ).right) := by
        simp [Functor.map_comp, Category.assoc]
      _ = ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫ (F.map β).right) ≫
            (F.map γ).right := by
        exact congrArg (fun q ↦ q ≫ (F.map γ).right) hEq
      _ = ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫
            (F.map (β ≫ γ)).right) := by
        simp [Functor.map_comp, Category.assoc]
  refine ⟨j, u, v, hu, hv, ?_⟩
  -- Rewrite the transported equality using the commutative square attached to `F.map (α ≫ γ)`.
  calc
    u ≫ (F.obj j).hom = u₀ ≫ ((F.map (α ≫ γ)).left ≫ (F.obj j).hom) := by
      simp [u, Category.assoc]
    _ = u₀ ≫ ((F.obj j₀).hom ≫ (F.map (α ≫ γ)).right) := by
      rw [Arrow.w (F.map (α ≫ γ))]
    _ = (u₀ ≫ (F.obj j₀).hom) ≫ (F.map (α ≫ γ)).right := by
      simp [Category.assoc]
    _ = ((((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v₀) ≫ (F.map (β ≫ γ)).right) := hEq'
    _ = (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v) := by
      simp [v, Category.assoc]

/-- Helper for Lemma 14.30.7: whiskering a colimiting arrow cocone along the standard
`ULiftHom (ULift J)` equivalence preserves its colimit property. -/
private lemma ulift_reindexed_arrow_cocone_isColimit
    {J : Type v₁} [Category.{v₂} J]
    (e : J ≌ CategoryTheory.ULiftHom (ULift J))
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c) :
    IsColimit (c.whisker e.inverse) := by
  -- Equivalence functors are final, so whiskering preserves the colimit cocone.
  exact (Functor.Final.isColimitWhiskerEquiv e.inverse c).symm hc

/-- Helper for Lemma 14.30.7: a lifting square against a boundary inclusion and an arrow-valued
filtered colimit already comes from one stage of the diagram. -/
private lemma boundary_stagewise_square_of_arrow_filtered_colimit_square
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (n : ℕ)
    {t : (∂Δ[n] : SSet.{u}) ⟶ c.pt.left}
    {b : Δ[n] ⟶ c.pt.right}
    (hsq :
      t ≫ c.pt.hom =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b)) :
    ∃ (j : J) (u : (∂Δ[n] : SSet.{u}) ⟶ (F.obj j).left) (v : Δ[n] ⟶ (F.obj j).right),
      u ≫ (c.ι.app j).left = t ∧
      v ≫ (c.ι.app j).right = b ∧
      u ≫ (F.obj j).hom =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ v) := by
  -- Route correction: reindex through the standard `ULiftHom (ULift J)` equivalence instead of
  -- searching for an ad hoc small filtered model of `J`.
  let e : J ≌ CategoryTheory.ULiftHom (ULift J) := CategoryTheory.ULiftHomULiftCategory.equiv J
  let E : CategoryTheory.ULiftHom (ULift J) ⥤ J := e.inverse
  letI : IsFiltered (CategoryTheory.ULiftHom (ULift J)) :=
    CategoryTheory.IsFiltered.of_equivalence e
  have hc' : IsColimit (c.whisker E) :=
    ulift_reindexed_arrow_cocone_isColimit e F c hc
  have hsq' :
      t ≫ (c.whisker E).pt.hom =
        (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n]) ≫ b) := by
    -- The whiskered cocone has the same cocone point, so the original square is unchanged.
    simpa [E] using hsq
  -- Apply the small-category descent to the reindexed diagram.
  obtain ⟨j', u, v, hu, hv, huv⟩ :=
    boundary_stagewise_square_of_arrow_filtered_colimit_square_small
      (F := E ⋙ F) (c := c.whisker E) hc' n hsq'
  refine ⟨E.obj j', u, v, ?_, ?_, ?_⟩
  · -- Read the descended left factor back in the original filtered diagram.
    simpa [E] using hu
  · -- The descended simplex factor is also definitionally unchanged after reindexing.
    simpa [E] using hv
  · -- The stagewise commutative square already lives in the original diagram after reindexing.
    simpa [E] using huv

theorem boundaryInclusions_rlp_colimit_of_filtered_diagram
    {J : Type v₁} [Category.{v₂} J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, I.rlp ((F.obj j).hom)) :
    I.rlp (c.pt.hom) := by
  intro X Y g hg
  have hg' :
      ∃ n, Arrow.mk g =
        Arrow.mk (((∂Δ[n]).ι : (∂Δ[n] : SSet.{u}) ⟶ Δ[n])) := by
    simpa [I, MorphismProperty.ofHoms_iff] using hg
  obtain ⟨n, hg'⟩ := hg'
  let p : (∂Δ[n] : SSet.{u}) ⟶ Δ[n] := (∂Δ[n]).ι
  have hp : HasLiftingProperty p c.pt.hom := by
    rw [Arrow.hasLiftingProperty_iff]
    intro ψ
    -- Descend the boundary square to one finite stage and lift there.
    obtain ⟨j, u, v, hu, hv, hsquare⟩ :=
      boundary_stagewise_square_of_arrow_filtered_colimit_square
        F c hc n ψ.w
    have hj : HasLiftingProperty p (F.obj j).hom :=
      hF j _ (boundary_ι_mem_I n)
    let sqStage : CommSq u p (F.obj j).hom v := CommSq.mk hsquare
    let liftStage : Δ[n] ⟶ (F.obj j).left := sqStage.lift
    have hright_stage : liftStage ≫ (F.obj j).hom = v := by
      simpa [liftStage] using sqStage.fac_right
    have hfac_right :
        (liftStage ≫ (c.ι.app j).left) ≫ c.pt.hom = v ≫ (c.ι.app j).right := by
      -- The stagewise filler remains a filler after composing into the cocone point.
      calc
        (liftStage ≫ (c.ι.app j).left) ≫ c.pt.hom =
            liftStage ≫ ((c.ι.app j).left ≫ c.pt.hom) := by
          simp [Category.assoc]
        _ = liftStage ≫ ((F.obj j).hom ≫ (c.ι.app j).right) := by
          exact congrArg (fun k ↦ liftStage ≫ k) (Arrow.w (c.ι.app j))
        _ = (liftStage ≫ (F.obj j).hom) ≫ (c.ι.app j).right := by
          simp [Category.assoc]
        _ = v ≫ (c.ι.app j).right := by
          exact congrArg (fun k ↦ k ≫ (c.ι.app j).right) hright_stage
    -- Compose the stagewise filler into the cocone point.
    refine ⟨{ l := liftStage ≫ (c.ι.app j).left, fac_left := ?_, fac_right := ?_ }⟩
    · calc
        p ≫ (liftStage ≫ (c.ι.app j).left) = (p ≫ liftStage) ≫ (c.ι.app j).left := by
          simp [Category.assoc]
        _ = u ≫ (c.ι.app j).left := by
          simpa [liftStage, Category.assoc] using
            congrArg (fun k ↦ k ≫ (c.ι.app j).left) sqStage.fac_left
        _ = ψ.left := hu
    · exact hfac_right.trans (by simpa using hv)
  -- Transport the lifting property back across the identified boundary inclusion.
  letI : HasLiftingProperty p c.pt.hom := hp
  exact HasLiftingProperty.of_arrow_iso_left (eqToIso hg'.symm) (c.pt.hom)

end
