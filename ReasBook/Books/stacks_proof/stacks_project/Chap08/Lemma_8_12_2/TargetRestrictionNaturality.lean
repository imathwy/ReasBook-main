import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.TargetRestriction
import stacks_proof.stacks_project.Chap08.Lemma_8_2_3.PullbackComparisonNaturality

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: the strict target-restriction comparison is compatible with the
chosen cartesian maps to the original restricted pullback. -/
theorem pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (pullbackProjection_targetRestrictionIso u p a X).hom.1 ≫
      (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
        pullbackProjection_targetFiberMap u p X =
        pullbackProjection_targetFiberMap u p
          (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≫
          ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd := by
  -- Both composites are the second component of the canonical cartesian comparison in the
  -- categorical pullback.
  let γ := pullbackProjection_targetFiberComparisonHom u p X
  letI : IsIso (pullbackProjection_targetFiberMap u p
      (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X)) :=
    pullbackProjection_targetFiberMap_isIso u p _
  letI : IsIso γ := pullbackProjection_targetFiberComparisonHom_isIso u p X
  letI : IsIso γ.1 := by
    change IsIso ((Functor.Fiber.fiberInclusion :
      (CategoricalPullback.π₁ u p).Fiber U ⥤ CategoricalPullback u p).map γ)
    infer_instance
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) (asIso γ.1).hom := by
    change (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) γ.1
    exact γ.2
  letI : (CategoricalPullback.π₁ u p).IsCartesian a
      (pullbackProjection_ofTargetRestrictionAmbientHom u p a
        (pullbackProjection_targetFiberObj u p X)) :=
    pullbackProjection_ofTargetRestrictionAmbientHom_isCartesian u p a
      (pullbackProjection_targetFiberObj u p X)
  letI : (CategoricalPullback.π₁ u p).IsCartesian a
      (pullbackProjection_ofTargetRestrictionAmbientHom u p a
          (pullbackProjection_targetFiberObj u p X) ≫ (asIso γ.1).hom) := by
    infer_instance
  letI : (CategoricalPullback.π₁ u p).IsStronglyCartesian a
      ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X) :=
    (canonicalPullbackChoice (CategoricalPullback.π₁ u p)).isStronglyCartesian a X
  letI : (CategoricalPullback.π₁ u p).IsHomLift a
      ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X) := inferInstance
  dsimp [pullbackProjection_targetRestrictionIso, pullbackProjection_targetFiberFunctor,
    pullbackProjection_targetFiberCounitIso, pullbackProjection_targetFiberCounitHom]
  change ((pullbackProjection_targetFiberHom u p _).1 ≫
      pullbackProjection_targetFiberMap u p (pullbackProjection_ofTargetFiberObj u p
        (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X)))) ≫
      (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
        pullbackProjection_targetFiberMap u p X =
      pullbackProjection_targetFiberMap u p
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≫
        ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd
  rw [pullbackProjection_targetFiberHom_fac]
  simp only [Category.assoc]
  apply (cancel_epi (pullbackProjection_targetFiberMap u p
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X))).2
  have hfac := Functor.IsCartesian.fac (CategoricalPullback.π₁ u p) a
    (pullbackProjection_ofTargetRestrictionAmbientHom u p a (pullbackProjection_targetFiberObj u p X) ≫
      (asIso γ.1).hom)
    ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X)
  exact congrArg CategoricalPullback.Hom.snd hfac

/-- Helper for Chap08 Lemma 8 12 2: the inverse target-restriction comparison recovers the
target pullback arrow after postcomposition with the restricted pullback component. -/
theorem pullbackProjection_targetRestrictionIso_inv_comp_targetFiberMap_comp_restriction_snd
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
        pullbackProjection_targetFiberMap u p
          (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≫
        ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd =
      (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
        pullbackProjection_targetFiberMap u p X := by
  -- Precompose the hom-side compatibility by the inverse comparison and cancel the iso pair.
  let e := pullbackProjection_targetRestrictionIso u p a X
  have hhom := pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap u p a X
  calc
    e.inv.1 ≫
        pullbackProjection_targetFiberMap u p
          (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≫
        ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd =
        e.inv.1 ≫
          (e.hom.1 ≫
            (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
            pullbackProjection_targetFiberMap u p X) := by
      rw [hhom]
    _ =
        (e.inv.1 ≫ e.hom.1) ≫
          (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
          pullbackProjection_targetFiberMap u p X := by
      simp only [Category.assoc]
    _ =
        (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X) ≫
          pullbackProjection_targetFiberMap u p X := by
      have hinv :
          e.inv.1 ≫ e.hom.1 =
            𝟙 (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
              (pullbackProjection_targetFiberObj u p X)).1 := by
        exact congrArg Subtype.val e.inv_hom_id
      rw [hinv]
      cat_disch

/-- Helper for Chap08 Lemma 8 12 2: target-restriction comparison is natural for vertical
morphisms in a pullback-projection fiber. -/
theorem pullbackProjection_targetRestrictionIso_naturality_over_vertical
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (pullbackProjection_targetRestrictionIso u p a X).inv ≫
        (pullbackProjection_targetFiberFunctor u p V).map
          (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
            a.op.toLoc).toFunctor.map φ) ≫
        (pullbackProjection_targetRestrictionIso u p a Y).hom =
      (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.map
        ((pullbackProjection_targetFiberFunctor u p U).map φ)) := by
  let lhs :
      ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X) ⟶
        ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p Y) :=
    (pullbackProjection_targetRestrictionIso u p a X).inv ≫
      (pullbackProjection_targetFiberFunctor u p V).map
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
          a.op.toLoc).toFunctor.map φ) ≫
      (pullbackProjection_targetRestrictionIso u p a Y).hom
  let rhs :
      ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X) ⟶
        ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p Y) :=
    (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.map
      ((pullbackProjection_targetFiberFunctor u p U).map φ))
  change lhs = rhs
  apply Functor.Fiber.hom_ext
  change lhs.1 = rhs.1
  let tailX :=
    (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p X)
  let tailY :=
    (canonicalPullbackChoice p).map (u.map a) (pullbackProjection_targetFiberObj u p Y)
  let sourceX :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
      a.op.toLoc).toFunctor.obj X)
  let sourceY :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
      a.op.toLoc).toFunctor.obj Y)
  let sourceφ :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
      a.op.toLoc).toFunctor.map φ)
  let sourceTailX := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd
  let sourceTailY := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a Y).snd
  let targetMapX := pullbackProjection_targetFiberMap u p X
  let targetMapY := pullbackProjection_targetFiberMap u p Y
  let sourceTargetMapX := pullbackProjection_targetFiberMap u p sourceX
  let sourceTargetMapY := pullbackProjection_targetFiberMap u p sourceY
  letI : p.IsStronglyCartesian (u.map a) tailY :=
    (canonicalPullbackChoice p).isStronglyCartesian (u.map a)
      (pullbackProjection_targetFiberObj u p Y)
  letI : p.IsCartesian (u.map a) tailY := inferInstance
  have htailY : p.IsCartesian (u.map a) tailY := by
    exact inferInstance
  have hlhs : p.IsHomLift (𝟙 (u.obj V)) lhs.1 := by
    simpa [lhs] using lhs.2
  have hrhs : p.IsHomLift (𝟙 (u.obj V)) rhs.1 := by
    simpa [rhs] using rhs.2
  apply
    @Functor.IsCartesian.ext D S _ _ p _ _ _ _
      (u.map a) tailY htailY _ lhs.1 rhs.1 hlhs hrhs
  letI : IsIso targetMapY := pullbackProjection_targetFiberMap_isIso u p Y
  apply (cancel_mono targetMapY).1
  have hhomY :
      (pullbackProjection_targetRestrictionIso u p a Y).hom.1 ≫ tailY ≫ targetMapY =
        sourceTargetMapY ≫ sourceTailY := by
    simpa [tailY, targetMapY, sourceTargetMapY, sourceTailY, sourceY] using
      pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap u p a Y
  have hinvX :
      (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ sourceTargetMapX ≫
          sourceTailX =
        tailX ≫ targetMapX := by
    simpa [tailX, targetMapX, sourceTargetMapX, sourceTailX, sourceX] using
      pullbackProjection_targetRestrictionIso_inv_comp_targetFiberMap_comp_restriction_snd u p a X
  have hsource :
      sourceφ.1.snd ≫ sourceTailY = sourceTailX ≫ φ.1.snd := by
    simpa [sourceφ, sourceTailX, sourceTailY] using
      congrArg CategoricalPullback.Hom.snd
        (FibredCategoryMor.canonical_pullbackFunctor_map_fac
          (p := CategoricalPullback.π₁ u p) (f := a) (φ := φ))
  have hmapSource :
      ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫ sourceTargetMapY =
        sourceTargetMapX ≫ sourceφ.1.snd := by
    simpa [pullbackProjection_targetFiberFunctor, sourceφ, sourceTargetMapX, sourceTargetMapY]
      using pullbackProjection_targetFiberHom_fac u p sourceφ
  have hmapTarget :
      rhs.1 ≫ tailY = tailX ≫ (pullbackProjection_targetFiberHom u p φ).1 := by
    simpa [rhs, tailX, tailY, pullbackProjection_targetFiberFunctor] using
      FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := p) (f := u.map a)
        (φ := (pullbackProjection_targetFiberFunctor u p U).map φ)
  have hfinal :
      (tailX ≫ targetMapX) ≫ φ.1.snd =
        (rhs.1 ≫ tailY) ≫ targetMapY := by
    calc
      (tailX ≫ targetMapX) ≫ φ.1.snd =
          tailX ≫ (targetMapX ≫ φ.1.snd) := by
          simp only [Category.assoc]
      _ =
          tailX ≫ ((pullbackProjection_targetFiberHom u p φ).1 ≫ targetMapY) := by
          rw [← pullbackProjection_targetFiberHom_fac]
      _ =
          (tailX ≫ (pullbackProjection_targetFiberHom u p φ).1) ≫ targetMapY := by
          simp only [Category.assoc]
      _ = (rhs.1 ≫ tailY) ≫ targetMapY := by
          rw [← hmapTarget]
          rfl
  have hlhs_underlying :
      lhs.1 =
        (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
          ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫
          (pullbackProjection_targetRestrictionIso u p a Y).hom.1 := by
    rfl
  -- After postcomposition, both sides are the same route through the source restriction of `X`;
  -- we name the prefix normalization before appending the final target-fiber compatibility step.
  have hprefix :
      (lhs.1 ≫ tailY) ≫ targetMapY =
        (tailX ≫ targetMapX) ≫ φ.1.snd := by
    calc
      (lhs.1 ≫ tailY) ≫ targetMapY =
          ((pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
              ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫
              (pullbackProjection_targetRestrictionIso u p a Y).hom.1) ≫ tailY ≫
            targetMapY := by
            rw [hlhs_underlying]
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
            ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫
            ((pullbackProjection_targetRestrictionIso u p a Y).hom.1 ≫ tailY ≫
              targetMapY) := by
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
            ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫
            (sourceTargetMapY ≫ sourceTailY) := by
            simpa only [Category.assoc] using
              congrArg
                (fun k ↦
                  (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
                    ((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫ k)
                hhomY
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
            (((pullbackProjection_targetFiberFunctor u p V).map sourceφ).1 ≫
              sourceTargetMapY) ≫ sourceTailY := by
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫
            (sourceTargetMapX ≫ sourceφ.1.snd) ≫ sourceTailY := by
            exact
              congrArg
                (fun k ↦
                  (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ k ≫ sourceTailY)
                hmapSource
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ sourceTargetMapX ≫
            (sourceφ.1.snd ≫ sourceTailY) := by
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ sourceTargetMapX ≫
            (sourceTailX ≫ φ.1.snd) := by
            simpa only [Category.assoc] using
              congrArg
                (fun k ↦
                  (pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ sourceTargetMapX ≫ k)
                hsource
      _ =
          ((pullbackProjection_targetRestrictionIso u p a X).inv.1 ≫ sourceTargetMapX ≫
            sourceTailX) ≫ φ.1.snd := by
            simp only [Category.assoc]
      _ =
          (tailX ≫ targetMapX) ≫ φ.1.snd := by
            rw [hinvX]
            rfl
  exact hprefix.trans hfinal

/-- Helper for Chap08 Lemma 8 12 2: the hom-side form of target-restriction naturality moves a
vertical morphism past the target-restriction comparison. -/
theorem pullbackProjection_targetRestrictionIso_hom_naturality_over_vertical
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    {X Y : (CategoricalPullback.π₁ u p).Fiber U} (φ : X ⟶ Y) :
    (pullbackProjection_targetFiberFunctor u p V).map
          (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
            a.op.toLoc).toFunctor.map φ) ≫
        (pullbackProjection_targetRestrictionIso u p a Y).hom =
      (pullbackProjection_targetRestrictionIso u p a X).hom ≫
        (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.map
          ((pullbackProjection_targetFiberFunctor u p U).map φ)) := by
  -- Start from the inverse-conjugation form and precompose by the comparison isomorphism.
  let eX := pullbackProjection_targetRestrictionIso u p a X
  let eY := pullbackProjection_targetRestrictionIso u p a Y
  let sourceMap :=
    (pullbackProjection_targetFiberFunctor u p V).map
      (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        a.op.toLoc).toFunctor.map φ)
  let targetMap :=
    (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.map
      ((pullbackProjection_targetFiberFunctor u p U).map φ))
  have hconj : eX.inv ≫ sourceMap ≫ eY.hom = targetMap := by
    simpa [eX, eY, sourceMap, targetMap] using
      pullbackProjection_targetRestrictionIso_naturality_over_vertical u p a φ
  change sourceMap ≫ eY.hom = eX.hom ≫ targetMap
  have hpre := congrArg (fun k ↦ eX.hom ≫ k) hconj
  dsimp at hpre
  have hleft :
      (eX.hom ≫ eX.inv) ≫ sourceMap ≫ eY.hom = eX.hom ≫ targetMap := by
    simpa only [Category.assoc] using hpre
  have hid :
      (eX.hom ≫ eX.inv) ≫ sourceMap ≫ eY.hom = sourceMap ≫ eY.hom := by
    rw [eX.hom_inv_id]
    simp only [Category.id_comp]
    rfl
  exact hid.symm.trans hleft

end

end CategoryTheory
