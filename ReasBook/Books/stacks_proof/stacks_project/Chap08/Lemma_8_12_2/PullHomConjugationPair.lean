import StacksProject_2024.Chap08.Lemma_8_12_2.TargetRestrictionNaturality
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover
universe uC uD uS vC vD vS
namespace CategoryTheory
section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: strictifying target components conjugates source
`pullHom` between two possibly different cover legs to the corresponding target `pullHom`. -/
theorem pullbackProjection_targetRestrictionIso_pullHom_conjugation_pair
    (p : S ⥤ D) [p.IsFibered] {U₁ U₂ V W : C} (a₁ : V ⟶ U₁) (a₂ : V ⟶ U₂)
    (k : W ⟶ V) (b₁ : W ⟶ U₁) (b₂ : W ⟶ U₂)
    (hk₁ : k ≫ a₁ = b₁) (hk₂ : k ≫ a₂ = b₂)
    (hkTarget₁ : u.map k ≫ u.map a₁ = u.map b₁)
    (hkTarget₂ : u.map k ≫ u.map a₂ = u.map b₂)
    (X : (CategoricalPullback.π₁ u p).Fiber U₁)
    (Y : (CategoricalPullback.π₁ u p).Fiber U₂)
    (φ :
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a₁.op.toLoc).toFunctor.obj X ⟶
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a₂.op.toLoc).toFunctor.obj Y) :
    (pullbackProjection_targetRestrictionIso u p b₁ X).inv ≫
        (pullbackProjection_targetFiberFunctor u p W).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b₁ b₂ hk₁ hk₂) ≫
        (pullbackProjection_targetRestrictionIso u p b₂ Y).hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((pullbackProjection_targetRestrictionIso u p a₁ X).inv ≫ (pullbackProjection_targetFiberFunctor u p V).map φ ≫
          (pullbackProjection_targetRestrictionIso u p a₂ Y).hom)
        (u.map k) (u.map b₁) (u.map b₂) hkTarget₁ hkTarget₂ := by
  apply Functor.Fiber.hom_ext
  change ((pullbackProjection_targetRestrictionIso u p b₁ X).inv ≫
      (pullbackProjection_targetFiberFunctor u p W).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b₁ b₂ hk₁ hk₂) ≫
      (pullbackProjection_targetRestrictionIso u p b₂ Y).hom).1 =
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv ≫
        (pullbackProjection_targetFiberFunctor u p V).map φ ≫
        (pullbackProjection_targetRestrictionIso u p a₂ Y).hom)
      (u.map k) (u.map b₁) (u.map b₂) hkTarget₁ hkTarget₂).1
  let lhs := ((pullbackProjection_targetRestrictionIso u p b₁ X).inv ≫
      (pullbackProjection_targetFiberFunctor u p W).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b₁ b₂ hk₁ hk₂) ≫
      (pullbackProjection_targetRestrictionIso u p b₂ Y).hom).1
  let rhs := (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv ≫
        (pullbackProjection_targetFiberFunctor u p V).map φ ≫
        (pullbackProjection_targetRestrictionIso u p a₂ Y).hom)
      (u.map k) (u.map b₁) (u.map b₂) hkTarget₁ hkTarget₂).1
  change lhs = rhs
  let tailY := (canonicalPullbackChoice p).map (u.map b₂) (pullbackProjection_targetFiberObj u p Y)
  letI : p.IsStronglyCartesian (u.map b₂) tailY :=
    (canonicalPullbackChoice p).isStronglyCartesian (u.map b₂) (pullbackProjection_targetFiberObj u p Y)
  letI : p.IsCartesian (u.map b₂) tailY := inferInstance
  have htailY : p.IsCartesian (u.map b₂) tailY := by
    exact inferInstance
  have hlhs : p.IsHomLift (𝟙 (u.obj W)) lhs := by
    dsimp [lhs]
    simpa using ((pullbackProjection_targetRestrictionIso u p b₁ X).inv ≫
      (pullbackProjection_targetFiberFunctor u p W).map
        (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b₁ b₂ hk₁ hk₂) ≫
      (pullbackProjection_targetRestrictionIso u p b₂ Y).hom).2
  have hrhs : p.IsHomLift (𝟙 (u.obj W)) rhs := by
    dsimp [rhs]
    simpa using (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv ≫
        (pullbackProjection_targetFiberFunctor u p V).map φ ≫
        (pullbackProjection_targetRestrictionIso u p a₂ Y).hom)
      (u.map k) (u.map b₁) (u.map b₂) hkTarget₁ hkTarget₂).2
  apply @Functor.IsCartesian.ext D S _ _ p _ _ _ _
    (u.map b₂) tailY htailY _ lhs rhs hlhs hrhs
  let targetMapY := pullbackProjection_targetFiberMap u p Y
  letI : IsIso targetMapY := pullbackProjection_targetFiberMap_isIso u p Y
  apply (cancel_mono targetMapY).1
  change (lhs ≫ tailY) ≫ targetMapY = (rhs ≫ tailY) ≫ targetMapY
  let targetMapX := pullbackProjection_targetFiberMap u p X
  letI : IsIso targetMapX := pullbackProjection_targetFiberMap_isIso u p X
  let sourceXa := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a₁.op.toLoc).toFunctor.obj X)
  let sourceYa := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a₂.op.toLoc).toFunctor.obj Y)
  let sourceXb := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map b₁.op.toLoc).toFunctor.obj X)
  let sourceYb := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map b₂.op.toLoc).toFunctor.obj Y)
  let sourceTailXa := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a₁ X).snd
  let sourceTailYa := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a₂ Y).snd
  let sourceTailXb := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map b₁ X).snd
  let sourceTailYb := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map b₂ Y).snd
  let sourceTailKX := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map k sourceXa).snd
  let sourceTailKY := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map k sourceYa).snd
  let sourceTargetMapXa := pullbackProjection_targetFiberMap u p sourceXa
  let sourceTargetMapYa := pullbackProjection_targetFiberMap u p sourceYa
  let sourceTargetMapXb := pullbackProjection_targetFiberMap u p sourceXb
  let sourceTargetMapYb := pullbackProjection_targetFiberMap u p sourceYb
  letI : IsIso sourceTargetMapXa := pullbackProjection_targetFiberMap_isIso u p sourceXa
  letI : IsIso sourceTargetMapYa := pullbackProjection_targetFiberMap_isIso u p sourceYa
  letI : IsIso sourceTargetMapXb := pullbackProjection_targetFiberMap_isIso u p sourceXb
  letI : IsIso sourceTargetMapYb := pullbackProjection_targetFiberMap_isIso u p sourceYb
  let targetX := pullbackProjection_targetFiberObj u p X
  let targetTailA₁ := (canonicalPullbackChoice p).map (u.map a₁) targetX
  let targetTailB₁ := (canonicalPullbackChoice p).map (u.map b₁) targetX
  let targetTailKX := (canonicalPullbackChoice p).map (u.map k)
    (((canonicalFiberPseudofunctor p).map (u.map a₁).op.toLoc).toFunctor.obj targetX)
  let leftSource := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp' a₁.op.toLoc
    k.op.toLoc b₁.op.toLoc (FibredCategoryMor.comp_toLoc_eq a₁ k b₁ hk₁)).hom.toNatTrans.app X)
  let rightSource := (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp' a₂.op.toLoc
    k.op.toLoc b₂.op.toLoc (FibredCategoryMor.comp_toLoc_eq a₂ k b₂ hk₂)).inv.toNatTrans.app Y)
  let leftTarget := (((canonicalFiberPseudofunctor p).mapComp' (u.map a₁).op.toLoc (u.map k).op.toLoc
    (u.map b₁).op.toLoc (FibredCategoryMor.comp_toLoc_eq (u.map a₁) (u.map k) (u.map b₁) hkTarget₁)).hom.toNatTrans.app
      (pullbackProjection_targetFiberObj u p X))
  let rightTarget := (((canonicalFiberPseudofunctor p).mapComp' (u.map a₂).op.toLoc (u.map k).op.toLoc
    (u.map b₂).op.toLoc (FibredCategoryMor.comp_toLoc_eq (u.map a₂) (u.map k) (u.map b₂) hkTarget₂)).inv.toNatTrans.app
      (pullbackProjection_targetFiberObj u p Y))
  let sourcePull := Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b₁ b₂ hk₁ hk₂
  let targetφ :=
    (pullbackProjection_targetRestrictionIso u p a₁ X).inv ≫
      (pullbackProjection_targetFiberFunctor u p V).map φ ≫
      (pullbackProjection_targetRestrictionIso u p a₂ Y).hom
  have hhomB₂ :
      (pullbackProjection_targetRestrictionIso u p b₂ Y).hom.1 ≫ tailY ≫ targetMapY =
        sourceTargetMapYb ≫ sourceTailYb := by
    simpa [tailY, targetMapY, sourceTargetMapYb, sourceTailYb, sourceYb] using
      pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap u p b₂ Y
  have hhomA₂ :
      (pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 ≫
          (canonicalPullbackChoice p).map (u.map a₂)
            (pullbackProjection_targetFiberObj u p Y) ≫
          targetMapY =
        sourceTargetMapYa ≫ sourceTailYa := by
    simpa [targetMapY, sourceTargetMapYa, sourceTailYa, sourceYa] using
      pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap u p a₂ Y
  have hhomA₁ :
      (pullbackProjection_targetRestrictionIso u p a₁ X).hom.1 ≫ targetTailA₁ ≫
          targetMapX =
        sourceTargetMapXa ≫ sourceTailXa := by
    simpa [targetTailA₁, targetMapX, sourceTargetMapXa, sourceTailXa, sourceXa, targetX] using
      pullbackProjection_targetRestrictionIso_hom_comp_targetFiberMap u p a₁ X
  have hinvB₁ :
      (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
          sourceTailXb =
        targetTailB₁ ≫ pullbackProjection_targetFiberMap u p X := by
    simpa [targetTailB₁, sourceTargetMapXb, sourceTailXb, sourceXb] using
      pullbackProjection_targetRestrictionIso_inv_comp_targetFiberMap_comp_restriction_snd u p b₁ X
  have hinvA₁ :
      (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa ≫
          sourceTailXa =
        targetTailA₁ ≫ pullbackProjection_targetFiberMap u p X := by
    simpa [targetTailA₁, sourceTargetMapXa, sourceTailXa, sourceXa] using
      pullbackProjection_targetRestrictionIso_inv_comp_targetFiberMap_comp_restriction_snd u p a₁ X
  have hsourceMapK :
      ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        k.op.toLoc).toFunctor.map φ).1.snd) ≫ sourceTailKY =
        sourceTailKX ≫ φ.1.snd := by
    simpa [sourceTailKX, sourceTailKY, sourceXa, sourceYa] using
      congrArg CategoricalPullback.Hom.snd
        (FibredCategoryMor.canonical_pullbackFunctor_map_fac
          (p := CategoricalPullback.π₁ u p) (f := k) (φ := φ))
  have hrightSource :
      rightSource.1.snd ≫ sourceTailYb = sourceTailKY ≫ sourceTailYa := by
    simpa [rightSource, sourceTailYb, sourceTailKY, sourceTailYa, sourceYa, sourceYb] using
      congrArg CategoricalPullback.Hom.snd
        (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
          (p := CategoricalPullback.π₁ u p) (f := a₂) (g := k)
          (gf := b₂) (hgf := hk₂) Y)
  have hleftSource :
      leftSource.1.snd ≫ sourceTailKX ≫ sourceTailXa = sourceTailXb := by
    simpa [leftSource, sourceTailKX, sourceTailXa, sourceTailXb, sourceXa, sourceXb] using
      congrArg CategoricalPullback.Hom.snd
        (FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
          (p := CategoricalPullback.π₁ u p) (f := a₁) (g := k)
          (gf := b₁) (hgf := hk₁) X)
  have hleftTarget :
      leftTarget.1 ≫ targetTailKX ≫ targetTailA₁ = targetTailB₁ := by
    simpa [leftTarget, targetTailKX, targetTailA₁, targetTailB₁, targetX] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        (p := p) (f := u.map a₁) (g := u.map k)
        (gf := u.map b₁) (hgf := hkTarget₁) targetX
  have hrightTarget :
      rightTarget.1 ≫ tailY =
        (canonicalPullbackChoice p).map (u.map k)
            (((canonicalFiberPseudofunctor p).map
              (u.map a₂).op.toLoc).toFunctor.obj
                (pullbackProjection_targetFiberObj u p Y)) ≫
          (canonicalPullbackChoice p).map (u.map a₂)
            (pullbackProjection_targetFiberObj u p Y) := by
    simpa [rightTarget, tailY] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_inv_app_fac
        (p := p) (f := u.map a₂) (g := u.map k)
        (gf := u.map b₂) (hgf := hkTarget₂)
        (pullbackProjection_targetFiberObj u p Y)
  have hleftBoundary :
      (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
          leftSource.1.snd ≫ sourceTailKX =
        leftTarget.1 ≫ targetTailKX ≫
          (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa := by
    let eA := pullbackProjection_targetRestrictionIso u p a₁ X
    let α :=
      (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
        leftSource.1.snd ≫ sourceTailKX
    let β :=
      leftTarget.1 ≫ targetTailKX ≫
        (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa
    let α' := α ≫ inv sourceTargetMapXa ≫ eA.hom.1
    let β' := leftTarget.1 ≫ targetTailKX
    letI : p.IsHomLift (𝟙 (u.obj W)) leftTarget.1 := leftTarget.2
    letI : p.IsStronglyCartesian (u.map k) targetTailKX :=
      (canonicalPullbackChoice p).isStronglyCartesian (u.map k)
        (((canonicalFiberPseudofunctor p).map (u.map a₁).op.toLoc).toFunctor.obj targetX)
    letI : p.IsHomLift (u.map k) targetTailKX := inferInstance
    letI : p.IsStronglyCartesian (u.map a₁) targetTailA₁ :=
      (canonicalPullbackChoice p).isStronglyCartesian (u.map a₁) targetX
    have hαInst : p.IsHomLift (u.map k) α' := by
      let eB := pullbackProjection_targetRestrictionIso u p b₁ X
      let baseXa := pullbackProjection_targetBaseMap u p sourceXa
      let baseXb := pullbackProjection_targetBaseMap u p sourceXb
      letI : p.IsHomLift (𝟙 (u.obj W)) eB.inv.1 := eB.inv.2
      letI : p.IsCartesian baseXb sourceTargetMapXb := by
        dsimp [baseXb, sourceTargetMapXb]
        exact pullbackProjection_targetFiberMap_isCartesian u p sourceXb
      letI : p.IsHomLift baseXb sourceTargetMapXb := inferInstance
      letI : IsIso baseXb := by
        dsimp [baseXb]
        exact pullbackProjection_targetBaseMap_isIso u p sourceXb
      letI : IsIso baseXa := by
        dsimp [baseXa]
        exact pullbackProjection_targetBaseMap_isIso u p sourceXa
      letI : p.IsCartesian baseXa sourceTargetMapXa := by
        dsimp [baseXa, sourceTargetMapXa]
        exact pullbackProjection_targetFiberMap_isCartesian u p sourceXa
      letI : p.IsHomLift (inv baseXa) (inv sourceTargetMapXa) := inferInstance
      letI : p.IsHomLift (𝟙 (u.obj V)) eA.hom.1 := eA.hom.2
      have hleftBase :
          baseXb ≫ p.map leftSource.1.snd =
            pullbackProjection_targetBaseMap u p
              (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                k.op.toLoc).toFunctor.obj sourceXa) := by
        simpa [baseXb, sourceXa, sourceXb, leftSource] using
          pullbackProjection_targetBaseMap_comp_snd u p leftSource
      have htailBase :
          pullbackProjection_targetBaseMap u p
              (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                k.op.toLoc).toFunctor.obj sourceXa) ≫ p.map sourceTailKX =
            u.map k ≫ baseXa := by
        simpa [baseXa, sourceTailKX, sourceXa] using
          pullbackProjection_targetBaseMap_comp_restriction_snd u p k sourceXa
      have hαLift :
          p.IsHomLift
            (((((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
                p.map sourceTailKX) ≫ inv baseXa) ≫ 𝟙 (u.obj V))
            α' := by
        have h₀ : p.IsHomLift (𝟙 (u.obj W) ≫ baseXb)
            (eB.inv.1 ≫ sourceTargetMapXb) := by
          infer_instance
        letI : p.IsHomLift (𝟙 (u.obj W) ≫ baseXb)
            (eB.inv.1 ≫ sourceTargetMapXb) := h₀
        have h₁ : p.IsHomLift
            ((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd)
            ((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) := by
          infer_instance
        letI : p.IsHomLift
            ((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd)
            ((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) := h₁
        have h₂ : p.IsHomLift
            (((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
              p.map sourceTailKX)
            (((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) ≫
              sourceTailKX) := by
          infer_instance
        letI : p.IsHomLift
            (((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
              p.map sourceTailKX)
            (((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) ≫
              sourceTailKX) := h₂
        have h₃ : p.IsHomLift
            ((((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
              p.map sourceTailKX) ≫ inv baseXa)
            ((((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) ≫
              sourceTailKX) ≫ inv sourceTargetMapXa) := by
          infer_instance
        letI : p.IsHomLift
            ((((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
              p.map sourceTailKX) ≫ inv baseXa)
            ((((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) ≫
              sourceTailKX) ≫ inv sourceTargetMapXa) := h₃
        have h₄ : p.IsHomLift
            (((((𝟙 (u.obj W) ≫ baseXb) ≫ p.map leftSource.1.snd) ≫
              p.map sourceTailKX) ≫ inv baseXa) ≫ 𝟙 (u.obj V))
            (((((eB.inv.1 ≫ sourceTargetMapXb) ≫ leftSource.1.snd) ≫
              sourceTailKX) ≫ inv sourceTargetMapXa) ≫ eA.hom.1) := by
          infer_instance
        simpa [α', α, Category.assoc] using h₄
      have hbase :
          baseXb ≫ p.map leftSource.1.snd ≫ p.map sourceTailKX ≫ inv baseXa =
            u.map k := by
        calc
          baseXb ≫ p.map leftSource.1.snd ≫ p.map sourceTailKX ≫ inv baseXa =
              ((baseXb ≫ p.map leftSource.1.snd) ≫ p.map sourceTailKX) ≫
                inv baseXa := by
                simp only [Category.assoc]
          _ =
              (pullbackProjection_targetBaseMap u p
                  (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                    k.op.toLoc).toFunctor.obj sourceXa) ≫
                p.map sourceTailKX) ≫ inv baseXa := by
                exact congrArg (fun t ↦ (t ≫ p.map sourceTailKX) ≫ inv baseXa) hleftBase
          _ = (u.map k ≫ baseXa) ≫ inv baseXa := by
                rw [htailBase]
          _ = u.map k := by
                simp [Category.assoc]
      have hαLift' :
          p.IsHomLift
            (baseXb ≫ p.map leftSource.1.snd ≫ p.map sourceTailKX ≫ inv baseXa)
            α' := by
        simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hαLift
      exact hbase ▸ hαLift'
    letI : p.IsHomLift (u.map k) α' := hαInst
    have hβInst : p.IsHomLift (u.map k) β' := by
      have hTail : p.IsHomLift (u.map k) targetTailKX := by
        infer_instance
      have hβ :
          p.IsHomLift (u.map k) (leftTarget.1 ≫ targetTailKX) := by
        exact @IsHomLift.comp_lift_id_left' _ _ _ _ p _ _ _
          (u.obj W) leftTarget.1 leftTarget.property _ _ (u.map k) targetTailKX hTail
      simpa [β'] using hβ
    letI : p.IsHomLift (u.map k) β' := hβInst
    have hpre : α' = β' := by
      have hpost : α' ≫ targetTailA₁ = β' ≫ targetTailA₁ := by
        apply (cancel_mono targetMapX).1
        have hmid :
            (α' ≫ targetTailA₁) ≫ targetMapX =
              targetTailB₁ ≫ targetMapX := by
          calc
            (α' ≫ targetTailA₁) ≫ targetMapX =
                α ≫ inv sourceTargetMapXa ≫
                  ((pullbackProjection_targetRestrictionIso u p a₁ X).hom.1 ≫
                    targetTailA₁ ≫ targetMapX) := by
                  simp [α', eA, Category.assoc]
            _ = α ≫ inv sourceTargetMapXa ≫ (sourceTargetMapXa ≫ sourceTailXa) := by
                  rw [hhomA₁]
            _ = α ≫ sourceTailXa := by
                  simp
            _ = targetTailB₁ ≫ targetMapX := by
                  dsimp [α]
                  calc
                    ((pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                          sourceTargetMapXb ≫ leftSource.1.snd ≫ sourceTailKX) ≫
                        sourceTailXa =
                        (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                          sourceTargetMapXb ≫
                            (leftSource.1.snd ≫ sourceTailKX ≫ sourceTailXa) := by
                          simp only [Category.assoc]
                    _ =
                        (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                          sourceTargetMapXb ≫ sourceTailXb := by
                          rw [hleftSource]
                    _ = targetTailB₁ ≫ targetMapX := by
                          simpa [targetMapX, Category.assoc] using hinvB₁
        have htarget :
            targetTailB₁ ≫ targetMapX = (β' ≫ targetTailA₁) ≫ targetMapX := by
          have hleftTarget' : targetTailB₁ = β' ≫ targetTailA₁ := by
            dsimp [β']
            simpa only [Category.assoc] using hleftTarget.symm
          rw [hleftTarget']
          rfl
        exact hmid.trans htarget
      exact @Functor.IsStronglyCartesian.ext D S _ _ p _ _ _ _ (u.map a₁)
        targetTailA₁ inferInstance _ _ (u.map k) α' β' hαInst hβInst hpost
    calc
        α = α' ≫ (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫
              sourceTargetMapXa := by
            have heA : eA.hom.1 ≫ eA.inv.1 = 𝟙 _ := congrArg Subtype.val eA.hom_inv_id
            have hsource : inv sourceTargetMapXa ≫ sourceTargetMapXa = 𝟙 _ :=
              IsIso.inv_hom_id sourceTargetMapXa
            symm
            calc
              α' ≫ (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫
                  sourceTargetMapXa =
                α ≫ inv sourceTargetMapXa ≫ eA.hom.1 ≫ eA.inv.1 ≫
                  sourceTargetMapXa := by
                  simp [α', eA, Category.assoc]
              _ = α ≫ inv sourceTargetMapXa ≫ (eA.hom.1 ≫ eA.inv.1) ≫
                    sourceTargetMapXa := by
                  simp only [Category.assoc]
              _ = α := by
                  rw [heA]
                  calc
                    α ≫ inv sourceTargetMapXa ≫ 𝟙 _ ≫ sourceTargetMapXa =
                        α ≫ (inv sourceTargetMapXa ≫ sourceTargetMapXa) := by
                      simp
                    _ = α := by
                      rw [hsource]
                      simp
      _ = β' ≫ (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫
            sourceTargetMapXa := by
          rw [hpre]
      _ = β := by
          simp [β, β', Category.assoc]
  have hlhs_underlying :
      lhs =
        (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
          ((pullbackProjection_targetFiberFunctor u p W).map sourcePull).1 ≫
          (pullbackProjection_targetRestrictionIso u p b₂ Y).hom.1 := by
    rfl
  have hlhs_norm :
      (lhs ≫ tailY) ≫ targetMapY =
        (leftTarget.1 ≫ targetTailKX ≫
          (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa) ≫
          φ.1.snd ≫ sourceTailYa := by
    calc
      (lhs ≫ tailY) ≫ targetMapY =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
            ((pullbackProjection_targetFiberFunctor u p W).map sourcePull).1 ≫
            ((pullbackProjection_targetRestrictionIso u p b₂ Y).hom.1 ≫ tailY ≫
              targetMapY) := by
            rw [hlhs_underlying]
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
            ((pullbackProjection_targetFiberFunctor u p W).map sourcePull).1 ≫
            (sourceTargetMapYb ≫ sourceTailYb) := by
            exact
              congrArg
                (fun t ↦
                  (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                    ((pullbackProjection_targetFiberFunctor u p W).map sourcePull).1 ≫ t)
                hhomB₂
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
            ((((pullbackProjection_targetFiberFunctor u p W).map sourcePull).1 ≫
              sourceTargetMapYb) ≫ sourceTailYb) := by
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
            ((sourceTargetMapXb ≫ sourcePull.1.snd) ≫ sourceTailYb) := by
            exact
              congrArg
                (fun t ↦
                  (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ t ≫
                    sourceTailYb)
                (by
                  simpa [pullbackProjection_targetFiberFunctor, sourceTargetMapXb,
                    sourceTargetMapYb] using
                    pullbackProjection_targetFiberHom_fac u p sourcePull)
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
            (leftSource.1.snd ≫
              ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                k.op.toLoc).toFunctor.map φ).1.snd) ≫
            rightSource.1.snd) ≫ sourceTailYb := by
            have hsnd :
                sourcePull.1.snd =
                  leftSource.1.snd ≫
                    ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                      k.op.toLoc).toFunctor.map φ).1.snd) ≫
                    rightSource.1.snd := by
              dsimp [sourcePull, leftSource, rightSource,
                Pseudofunctor.LocallyDiscreteOpToCat.pullHom, Functor.Fiber.fiberCategory,
                CategoryStruct.comp]
              change
                (leftSource.1 ≫
                    ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                      k.op.toLoc).toFunctor.map φ).1) ≫ rightSource.1).snd =
                  leftSource.1.snd ≫
                    ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                      k.op.toLoc).toFunctor.map φ).1.snd) ≫ rightSource.1.snd
              rw [Limits.CategoricalPullback.comp_snd, Limits.CategoricalPullback.comp_snd]
            rw [hsnd]
            simp only [Category.assoc]
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
            leftSource.1.snd ≫
              ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                k.op.toLoc).toFunctor.map φ).1.snd) ≫
              (sourceTailKY ≫ sourceTailYa) := by
            simpa only [Category.assoc] using
              congrArg
                (fun t ↦
                  (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                    sourceTargetMapXb ≫ leftSource.1.snd ≫
                      ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                        k.op.toLoc).toFunctor.map φ).1.snd) ≫ t)
                hrightSource
      _ =
          (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫ sourceTargetMapXb ≫
            leftSource.1.snd ≫ sourceTailKX ≫ φ.1.snd ≫ sourceTailYa := by
            calc
              (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                  sourceTargetMapXb ≫ leftSource.1.snd ≫
                  ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                    k.op.toLoc).toFunctor.map φ).1.snd) ≫
                  (sourceTailKY ≫ sourceTailYa) =
                (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                  sourceTargetMapXb ≫ leftSource.1.snd ≫
                  ((((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
                    k.op.toLoc).toFunctor.map φ).1.snd ≫ sourceTailKY) ≫
                  sourceTailYa := by
                  simp only [Category.assoc]
              _ =
                (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                  sourceTargetMapXb ≫ leftSource.1.snd ≫
                  (sourceTailKX ≫ φ.1.snd) ≫ sourceTailYa := by
                  exact
                    congrArg
                      (fun t ↦
                        (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                          sourceTargetMapXb ≫ leftSource.1.snd ≫ t ≫ sourceTailYa)
                      hsourceMapK
              _ =
                (pullbackProjection_targetRestrictionIso u p b₁ X).inv.1 ≫
                  sourceTargetMapXb ≫ leftSource.1.snd ≫ sourceTailKX ≫
                  φ.1.snd ≫ sourceTailYa := by
                  simp only [Category.assoc]
      _ =
          (leftTarget.1 ≫ targetTailKX ≫
            (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa) ≫
            φ.1.snd ≫ sourceTailYa := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ t ≫ φ.1.snd ≫ sourceTailYa) hleftBoundary
  have hrhs_underlying :
      rhs =
        leftTarget.1 ≫
          (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
            targetφ).1 ≫ rightTarget.1 := by
    dsimp [rhs, targetφ, Pseudofunctor.LocallyDiscreteOpToCat.pullHom, leftTarget,
      rightTarget]
    rfl
  have hrhs_norm :
      (rhs ≫ tailY) ≫ targetMapY =
        (leftTarget.1 ≫ targetTailKX ≫
          (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa) ≫
          φ.1.snd ≫ sourceTailYa := by
    calc
      (rhs ≫ tailY) ≫ targetMapY =
          (leftTarget.1 ≫
              (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                targetφ).1 ≫
              rightTarget.1) ≫ tailY ≫ targetMapY := by
            rw [hrhs_underlying]
            simp only [Category.assoc]
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              targetφ).1 ≫
            ((canonicalPullbackChoice p).map (u.map k)
                (((canonicalFiberPseudofunctor p).map
                  (u.map a₂).op.toLoc).toFunctor.obj
                    (pullbackProjection_targetFiberObj u p Y)) ≫
              (canonicalPullbackChoice p).map (u.map a₂)
                (pullbackProjection_targetFiberObj u p Y)) ≫
            targetMapY := by
            calc
              (leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    targetφ).1 ≫ rightTarget.1) ≫ tailY ≫ targetMapY =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      targetφ).1 ≫ (rightTarget.1 ≫ tailY) ≫ targetMapY := by
                    simp only [Category.assoc]
              _ =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      targetφ).1 ≫
                    ((canonicalPullbackChoice p).map (u.map k)
                        (((canonicalFiberPseudofunctor p).map
                          (u.map a₂).op.toLoc).toFunctor.obj
                          (pullbackProjection_targetFiberObj u p Y)) ≫
                      (canonicalPullbackChoice p).map (u.map a₂)
                        (pullbackProjection_targetFiberObj u p Y)) ≫
                      targetMapY := by
                      exact
                        congrArg
                          (fun t ↦
                            leftTarget.1 ≫
                              (((canonicalFiberPseudofunctor p).map
                                (u.map k).op.toLoc).toFunctor.map targetφ).1 ≫
                              t ≫ targetMapY)
                          hrightTarget
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
            (canonicalPullbackChoice p).map (u.map k)
                (((canonicalFiberPseudofunctor p).map
                  (u.map a₂).op.toLoc).toFunctor.obj
                    (pullbackProjection_targetFiberObj u p Y)) ≫
            (canonicalPullbackChoice p).map (u.map a₂)
                (pullbackProjection_targetFiberObj u p Y) ≫
            targetMapY := by
            have hmap :
                (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    targetφ).1 =
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 := by
              dsimp [targetφ]
              exact congrArg (fun t ↦ Functor.Fiber.fiberInclusion.map t)
                (functor_map_threefold_comp
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor)
                  (pullbackProjection_targetRestrictionIso u p a₁ X).inv
                  ((pullbackProjection_targetFiberFunctor u p V).map φ)
                  (pullbackProjection_targetRestrictionIso u p a₂ Y).hom)
            calc
              leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    targetφ).1 ≫
                  ((canonicalPullbackChoice p).map (u.map k)
                      (((canonicalFiberPseudofunctor p).map
                        (u.map a₂).op.toLoc).toFunctor.obj
                          (pullbackProjection_targetFiberObj u p Y)) ≫
                    (canonicalPullbackChoice p).map (u.map a₂)
                      (pullbackProjection_targetFiberObj u p Y)) ≫ targetMapY =
                  leftTarget.1 ≫
                  ((((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1) ≫
                  ((canonicalPullbackChoice p).map (u.map k)
                      (((canonicalFiberPseudofunctor p).map
                      (u.map a₂).op.toLoc).toFunctor.obj
                          (pullbackProjection_targetFiberObj u p Y)) ≫
                    (canonicalPullbackChoice p).map (u.map a₂)
                      (pullbackProjection_targetFiberObj u p Y)) ≫ targetMapY := by
                    exact
                      congrArg
                        (fun t ↦
                          leftTarget.1 ≫ t ≫
                            ((canonicalPullbackChoice p).map (u.map k)
                                (((canonicalFiberPseudofunctor p).map
                                  (u.map a₂).op.toLoc).toFunctor.obj
                                    (pullbackProjection_targetFiberObj u p Y)) ≫
                              (canonicalPullbackChoice p).map (u.map a₂)
                                (pullbackProjection_targetFiberObj u p Y)) ≫ targetMapY)
                        hmap
              _ =
                leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (((canonicalFiberPseudofunctor p).map
                      (u.map a₂).op.toLoc).toFunctor.obj
                        (pullbackProjection_targetFiberObj u p Y)) ≫
                  (canonicalPullbackChoice p).map (u.map a₂)
                    (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY := by
                  simp only [Category.assoc]
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
            (canonicalPullbackChoice p).map (u.map k)
              (pullbackProjection_targetFiberObj u p sourceYa) ≫
            ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 ≫
              (canonicalPullbackChoice p).map (u.map a₂)
                (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY) := by
            have hmapA₂ :
                (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (((canonicalFiberPseudofunctor p).map
                      (u.map a₂).op.toLoc).toFunctor.obj
                        (pullbackProjection_targetFiberObj u p Y)) =
                (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceYa) ≫
                  (pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 := by
              simpa [sourceTargetMapYa, sourceYa] using
                (FibredCategoryMor.canonical_pullbackFunctor_map_fac
                  (p := p) (f := u.map k)
                  (φ := (pullbackProjection_targetRestrictionIso u p a₂ Y).hom))
            calc
              leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (((canonicalFiberPseudofunctor p).map
                      (u.map a₂).op.toLoc).toFunctor.obj
                        (pullbackProjection_targetFiberObj u p Y)) ≫
                  (canonicalPullbackChoice p).map (u.map a₂)
                    (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                    (canonicalPullbackChoice p).map (u.map k)
                      (pullbackProjection_targetFiberObj u p sourceYa) ≫
                    (pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 ≫
                  (canonicalPullbackChoice p).map (u.map a₂)
                    (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY := by
                      calc
                        leftTarget.1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
                            (canonicalPullbackChoice p).map (u.map k)
                              (((canonicalFiberPseudofunctor p).map
                                (u.map a₂).op.toLoc).toFunctor.obj
                                  (pullbackProjection_targetFiberObj u p Y)) ≫
                            (canonicalPullbackChoice p).map (u.map a₂)
                              (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY =
                          leftTarget.1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                            ((((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom)).1 ≫
                              (canonicalPullbackChoice p).map (u.map k)
                                (((canonicalFiberPseudofunctor p).map
                                  (u.map a₂).op.toLoc).toFunctor.obj
                                    (pullbackProjection_targetFiberObj u p Y))) ≫
                            (canonicalPullbackChoice p).map (u.map a₂)
                              (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY := by
                              simp only [Category.assoc]
                        _ =
                          leftTarget.1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                            ((canonicalPullbackChoice p).map (u.map k)
                                (pullbackProjection_targetFiberObj u p sourceYa) ≫
                              (pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1) ≫
                            (canonicalPullbackChoice p).map (u.map a₂)
                              (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY := by
                              exact
                                congrArg
                                  (fun t ↦
                                    leftTarget.1 ≫
                                      (((canonicalFiberPseudofunctor p).map
                                        (u.map k).op.toLoc).toFunctor.map
                                        ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                                      (((canonicalFiberPseudofunctor p).map
                                        (u.map k).op.toLoc).toFunctor.map
                                        ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                                      t ≫
                                      (canonicalPullbackChoice p).map (u.map a₂)
                                        (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY)
                                  hmapA₂
                        _ =
                          leftTarget.1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                            (((canonicalFiberPseudofunctor p).map
                              (u.map k).op.toLoc).toFunctor.map
                              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                            (canonicalPullbackChoice p).map (u.map k)
                              (pullbackProjection_targetFiberObj u p sourceYa) ≫
                            (pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 ≫
                            (canonicalPullbackChoice p).map (u.map a₂)
                              (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY := by
                              simp only [Category.assoc]
              _ =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                    (canonicalPullbackChoice p).map (u.map k)
                      (pullbackProjection_targetFiberObj u p sourceYa) ≫
                    ((pullbackProjection_targetRestrictionIso u p a₂ Y).hom.1 ≫
                      (canonicalPullbackChoice p).map (u.map a₂)
                        (pullbackProjection_targetFiberObj u p Y) ≫ targetMapY) := by
                    rfl
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
            (canonicalPullbackChoice p).map (u.map k)
              (pullbackProjection_targetFiberObj u p sourceYa) ≫
            (sourceTargetMapYa ≫ sourceTailYa) := by
            rw [hhomA₂]
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
            (canonicalPullbackChoice p).map (u.map k)
              (pullbackProjection_targetFiberObj u p sourceXa) ≫
            (((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
              sourceTargetMapYa) ≫ sourceTailYa := by
            have hmapφ :
                (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceYa) =
                (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceXa) ≫
                  ((pullbackProjection_targetFiberFunctor u p V).map φ).1 := by
              simpa [sourceTargetMapXa, sourceTargetMapYa, sourceXa, sourceYa] using
                (FibredCategoryMor.canonical_pullbackFunctor_map_fac
                  (p := p) (f := u.map k)
                  (φ := ((pullbackProjection_targetFiberFunctor u p V).map φ)))
            calc
              leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceYa) ≫
                  sourceTargetMapYa ≫ sourceTailYa =
                    leftTarget.1 ≫
                      (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                        ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                        (canonicalPullbackChoice p).map (u.map k)
                          (pullbackProjection_targetFiberObj u p sourceXa) ≫
                        ((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
                        sourceTargetMapYa ≫ sourceTailYa := by
                        calc
                          leftTarget.1 ≫
                              (((canonicalFiberPseudofunctor p).map
                                (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                              (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                              (canonicalPullbackChoice p).map (u.map k)
                                (pullbackProjection_targetFiberObj u p sourceYa) ≫
                              sourceTargetMapYa ≫ sourceTailYa =
                            leftTarget.1 ≫
                              (((canonicalFiberPseudofunctor p).map
                                (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                              ((((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetFiberFunctor u p V).map φ)).1 ≫
                                (canonicalPullbackChoice p).map (u.map k)
                                  (pullbackProjection_targetFiberObj u p sourceYa)) ≫
                              sourceTargetMapYa ≫ sourceTailYa := by
                              simp only [Category.assoc]
                          _ =
                            leftTarget.1 ≫
                              (((canonicalFiberPseudofunctor p).map
                                (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                              ((canonicalPullbackChoice p).map (u.map k)
                                  (pullbackProjection_targetFiberObj u p sourceXa) ≫
                                ((pullbackProjection_targetFiberFunctor u p V).map φ).1) ≫
                              sourceTargetMapYa ≫ sourceTailYa := by
                              exact
                                congrArg
                                  (fun t ↦
                                    leftTarget.1 ≫
                                      (((canonicalFiberPseudofunctor p).map
                                        (u.map k).op.toLoc).toFunctor.map
                                        ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                                      t ≫ sourceTargetMapYa ≫ sourceTailYa)
                                  hmapφ
                          _ =
                            leftTarget.1 ≫
                              (((canonicalFiberPseudofunctor p).map
                                (u.map k).op.toLoc).toFunctor.map
                                ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                              (canonicalPullbackChoice p).map (u.map k)
                                (pullbackProjection_targetFiberObj u p sourceXa) ≫
                              ((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
                              sourceTargetMapYa ≫ sourceTailYa := by
                              simp only [Category.assoc]
              _ =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                    (canonicalPullbackChoice p).map (u.map k)
                      (pullbackProjection_targetFiberObj u p sourceXa) ≫
                    (((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
                      sourceTargetMapYa) ≫ sourceTailYa := by
                    simp only [Category.assoc]
      _ =
          leftTarget.1 ≫
            (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
              ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
            (canonicalPullbackChoice p).map (u.map k)
              (pullbackProjection_targetFiberObj u p sourceXa) ≫
            (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa := by
            have hφ :
                ((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
                    sourceTargetMapYa =
                  sourceTargetMapXa ≫ φ.1.snd := by
              simpa [sourceTargetMapXa, sourceTargetMapYa] using
                pullbackProjection_targetFiberHom_fac u p φ
            calc
              leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceXa) ≫
                    (((pullbackProjection_targetFiberFunctor u p V).map φ).1 ≫
                      sourceTargetMapYa) ≫ sourceTailYa =
                      leftTarget.1 ≫
                        (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                          ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                        (canonicalPullbackChoice p).map (u.map k)
                          (pullbackProjection_targetFiberObj u p sourceXa) ≫
                          (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa := by
                          exact
                            congrArg
                              (fun t ↦
                                leftTarget.1 ≫
                                  (((canonicalFiberPseudofunctor p).map
                                    (u.map k).op.toLoc).toFunctor.map
                                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                                  (canonicalPullbackChoice p).map (u.map k)
                                    (pullbackProjection_targetFiberObj u p sourceXa) ≫
                                  t ≫ sourceTailYa)
                              hφ
              _ =
                  leftTarget.1 ≫
                    (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                      ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                    (canonicalPullbackChoice p).map (u.map k)
                      (pullbackProjection_targetFiberObj u p sourceXa) ≫
                    (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa := by
                    simp only [Category.assoc]
      _ =
          leftTarget.1 ≫ targetTailKX ≫
            ((pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa) ≫
            φ.1.snd ≫ sourceTailYa := by
            have hmapInv :
                (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceXa) =
                targetTailKX ≫
                  (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 := by
              simpa [targetTailKX, sourceTargetMapXa, sourceXa, targetX] using
                (FibredCategoryMor.canonical_pullbackFunctor_map_fac
                  (p := p) (f := u.map k)
                  (φ := (pullbackProjection_targetRestrictionIso u p a₁ X).inv))
            calc
              leftTarget.1 ≫
                  (((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                  (canonicalPullbackChoice p).map (u.map k)
                    (pullbackProjection_targetFiberObj u p sourceXa) ≫
                    (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa =
                      leftTarget.1 ≫
                        ((((canonicalFiberPseudofunctor p).map (u.map k).op.toLoc).toFunctor.map
                          ((pullbackProjection_targetRestrictionIso u p a₁ X).inv)).1 ≫
                          (canonicalPullbackChoice p).map (u.map k)
                            (pullbackProjection_targetFiberObj u p sourceXa)) ≫
                        (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa := by
                        simp only [Category.assoc]
              _ =
                    leftTarget.1 ≫
                      (targetTailKX ≫
                        (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1) ≫
                    (sourceTargetMapXa ≫ φ.1.snd) ≫ sourceTailYa := by
                      dsimp [targetTailKX]
                      dsimp [targetTailKX] at hmapInv
                      exact
                        congrArg
                          (fun t ↦
                            leftTarget.1 ≫ t ≫ (sourceTargetMapXa ≫ φ.1.snd) ≫
                              sourceTailYa)
                          hmapInv
              _ =
                  leftTarget.1 ≫ targetTailKX ≫
                    ((pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫
                      sourceTargetMapXa) ≫
                    φ.1.snd ≫ sourceTailYa := by
                    simp only [Category.assoc]
      _ =
          (leftTarget.1 ≫ targetTailKX ≫
            (pullbackProjection_targetRestrictionIso u p a₁ X).inv.1 ≫ sourceTargetMapXa) ≫
            φ.1.snd ≫ sourceTailYa := by
            simp only [Category.assoc]
  exact hlhs_norm.trans hrhs_norm.symm
end

end CategoryTheory
