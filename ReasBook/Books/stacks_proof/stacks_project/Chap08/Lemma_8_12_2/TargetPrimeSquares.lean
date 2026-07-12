import StacksProject_2024.Chap08.Lemma_8_12_2.PrimeStrictification

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

/-- Helper for Chap08 Lemma 8 12 2: paste two adjacent commutative squares. -/
theorem compCompCompEqOfPaste {E : Type*} [Category E]
    {A B C₀ D₀ E₀ F : E}
    {a : A ⟶ B} {b : B ⟶ C₀} {c : C₀ ⟶ F}
    {d : A ⟶ D₀} {e : D₀ ⟶ E₀} {f : E₀ ⟶ F}
    {m : B ⟶ E₀} (hleft : a ≫ m = d ≫ e) (hright : b ≫ c = m ≫ f) :
    (a ≫ b) ≫ c = d ≫ (e ≫ f) := by
  -- Reassociate the outside rectangle and replace the two internal square boundaries.
  calc
    (a ≫ b) ≫ c = a ≫ (b ≫ c) := by
      simp only [Category.assoc]
    _ = a ≫ (m ≫ f) := by
      rw [hright]
    _ = (a ≫ m) ≫ f := by
      simp only [Category.assoc]
    _ = (d ≫ e) ≫ f := by
      rw [hleft]
    _ = d ≫ (e ≫ f) := by
      simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 12 2: split a functorial image of a composite inside
endpoint whiskers. -/
theorem mapCompWhisker {E₁ E₂ : Type*} [Category E₁] [Category E₂]
    (G : E₁ ⥤ E₂) {A B C : E₁} {X Y : E₂}
    (l : X ⟶ G.obj A) (f : A ⟶ B) (g : B ⟶ C) (r : G.obj C ⟶ Y) :
    l ≫ (G.map (f ≫ g) ≫ r) = l ≫ G.map f ≫ G.map g ≫ r := by
  -- Expose the two mapped factors before reassociating the endpoint whiskers.
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- Helper for Chap08 Lemma 8 12 2: insert an isomorphism followed by its inverse in a
whiskered composite. -/
theorem compIsoHomInvWhisker {E : Type*} [Category E]
    {A B C D F : E} (f : A ⟶ B) (i : B ≅ C) (g : B ⟶ D) (h : D ⟶ F) :
    f ≫ g ≫ h = f ≫ i.hom ≫ i.inv ≫ g ≫ h := by
  -- Replace the identity at the middle object by the visible iso-cancellation pair.
  calc
    f ≫ g ≫ h = f ≫ 𝟙 B ≫ g ≫ h := by
      simp only [Category.id_comp]
    _ = f ≫ (i.hom ≫ i.inv) ≫ g ≫ h := by
      rw [i.hom_inv_id]
    _ = f ≫ i.hom ≫ i.inv ≫ g ≫ h := by
      simp only [Category.assoc]

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: at the identity restriction, strictification followed by
the source `mapId.hom` component is the explicit target cartesian identity map. -/
private theorem pullbackProjection_targetRestrictionIso_id_inv_mapId_hom_explicit
    (p : S ⥤ D) [p.IsFibered] {U : C}
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    (pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv ≫
      (pullbackProjection_targetFiberFunctor u p U).map
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapId
          (.mk (Opposite.op U))).hom.toNatTrans.app X) =
      (⟨(canonicalPullbackChoice p).map (u.map (𝟙 U))
          (pullbackProjection_targetFiberObj u p X), by
        rw [← Functor.map_id u U]
        exact ((canonicalPullbackChoice p).isStronglyCartesian (u.map (𝟙 U))
            (pullbackProjection_targetFiberObj u p X)).toIsHomLift
       ⟩ :
        ((canonicalFiberPseudofunctor p).map (u.map (𝟙 U)).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X) ⟶
        pullbackProjection_targetFiberObj u p X) := by
  -- Compare after the target strictification map; the two sides are then the same cartesian
  -- arrow over `u.map (𝟙 U)`, with the source identity removed by the owner `mapId` formula.
  apply Functor.Fiber.hom_ext
  let targetMap := pullbackProjection_targetFiberMap u p X
  let sourceMapId :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapId
      (.mk (Opposite.op U))).hom.toNatTrans.app X)
  let sourceTargetMap :=
    pullbackProjection_targetFiberMap u p
      (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        (𝟙 U).op.toLoc).toFunctor.obj X)
  let sourceTail :=
    ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map (𝟙 U) X).snd
  let targetId :
      ((canonicalFiberPseudofunctor p).map (u.map (𝟙 U)).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X) ⟶
        pullbackProjection_targetFiberObj u p X :=
    (⟨(canonicalPullbackChoice p).map (u.map (𝟙 U))
        (pullbackProjection_targetFiberObj u p X), by
      rw [← Functor.map_id u U]
      exact ((canonicalPullbackChoice p).isStronglyCartesian (u.map (𝟙 U))
          (pullbackProjection_targetFiberObj u p X)).toIsHomLift
     ⟩)
  change ((pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv ≫
      (pullbackProjection_targetFiberFunctor u p U).map sourceMapId).1 = targetId.1
  letI : IsIso targetMap := pullbackProjection_targetFiberMap_isIso u p X
  apply (cancel_mono targetMap).1
  change (((pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv.1 ≫
      ((pullbackProjection_targetFiberFunctor u p U).map sourceMapId).1) ≫ targetMap =
    targetId.1 ≫ targetMap)
  have hsourceMap :
      ((pullbackProjection_targetFiberFunctor u p U).map sourceMapId).1 ≫ targetMap =
        sourceTargetMap ≫ sourceMapId.1.snd := by
    simpa [pullbackProjection_targetFiberFunctor, sourceMapId, targetMap, sourceTargetMap] using
      pullbackProjection_targetFiberHom_fac u p sourceMapId
  have hsourceId : sourceMapId.1.snd = sourceTail := by
    have h :=
      (canonicalPullbackChoice
        (CategoricalPullback.π₁ u p)).pullbackIdComponentIso_inv_eq U X
    simpa [sourceMapId, sourceTail, canonicalFiberPseudofunctor,
      PullbackChoice.fiberPseudofunctor, PullbackChoice.pullbackIdIso,
      Pseudofunctor.mapId'] using congrArg CategoricalPullback.Hom.snd h
  have hinv :
      (pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv.1 ≫
          sourceTargetMap ≫ sourceTail =
        (canonicalPullbackChoice p).map (u.map (𝟙 U))
          (pullbackProjection_targetFiberObj u p X) ≫ targetMap := by
    simpa [targetMap, sourceTargetMap, sourceTail] using
      pullbackProjection_targetRestrictionIso_inv_comp_targetFiberMap_comp_restriction_snd
        u p (𝟙 U) X
  have hpre :
      ((pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv.1 ≫
          ((pullbackProjection_targetFiberFunctor u p U).map sourceMapId).1) ≫ targetMap =
        (pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv.1 ≫
          sourceTargetMap ≫ sourceMapId.1.snd := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ (pullbackProjection_targetRestrictionIso u p (𝟙 U) X).inv.1 ≫ k)
        hsourceMap
  rw [hpre, hsourceId]
  simpa [targetId, Category.assoc] using hinv

/-- Helper for Chap08 Lemma 8 12 2: pulling a morphism preceded by the pseudofunctorial
identity comparison removes the left identity shell. -/
private theorem canonicalFiberPseudofunctor_pullHom_mapId_hom
    (p : S ⥤ D) [p.IsFibered] {U V W : D} {M : p.Fiber V}
    (a : V ⟶ U) (g : W ⟶ V) (b : W ⟶ U)
    (hid : g ≫ 𝟙 V = g) (h : g ≫ a = b) (N : p.Fiber U)
    (φ : M ⟶ ((canonicalFiberPseudofunctor p).map a.op.toLoc).toFunctor.obj N) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((((canonicalFiberPseudofunctor p).mapId (.mk (Opposite.op V))).hom.toNatTrans.app M) ≫
          φ)
        g g b hid h =
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ) ≫
        (((canonicalFiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc b.op.toLoc
          (FibredCategoryMor.comp_toLoc_eq a g b h)).inv.toNatTrans.app N) := by
  -- Reduce the left unit shell to the inverse-hom pair of the pseudofunctor unit isomorphism.
  subst h
  let t := ((canonicalFiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc
    (a.op.toLoc ≫ g.op.toLoc) (FibredCategoryMor.comp_toLoc_eq a g (g ≫ a) rfl)).inv.toNatTrans.app N
  let e := (canonicalFiberPseudofunctor p).mapId (.mk (Opposite.op V))
  suffices hsimp :
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.inv.toNatTrans.app M) ≫
          ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.hom.toNatTrans.app M) ≫
          ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ t =
        ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ t by
    simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      Pseudofunctor.mapComp'_id_comp_hom_app, t, e, Functor.map_comp, Category.assoc]
      using hsimp
  have hmap := (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map_comp
    (e.inv.toNatTrans.app M) (e.hom.toNatTrans.app M))
  rw [← Category.assoc]
  change (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
      (e.inv.toNatTrans.app M) ≫
    ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
      (e.hom.toNatTrans.app M)) ≫
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ t =
    ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ t
  rw [← hmap]
  have heq : e.inv.toNatTrans.app M ≫ e.hom.toNatTrans.app M = 𝟙 M := by
    change (fun k ↦ k.toNatTrans.app M) (e.inv ≫ e.hom) =
      (fun k ↦ k.toNatTrans.app M) (𝟙 (𝟙 ((canonicalFiberPseudofunctor p).obj
        (.mk (Opposite.op V)))))
    exact congrArg (fun k ↦ k.toNatTrans.app M) e.inv_hom_id
  have hmapId := congrArg (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map) heq
  rw [hmapId]
  exact
    (congrArg (fun k ↦
      k ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ t)
      (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map_id M)).trans
      (by simp)

/-- Helper for Chap08 Lemma 8 12 2: pulling a morphism followed by the pseudofunctorial
identity comparison removes the right identity shell. -/
private theorem canonicalFiberPseudofunctor_pullHom_mapId_inv
    (p : S ⥤ D) [p.IsFibered] {U V W : D} {M : p.Fiber V}
    (a : V ⟶ U) (g : W ⟶ V) (b : W ⟶ U)
    (h : g ≫ a = b) (hid : g ≫ 𝟙 V = g) (N : p.Fiber U)
    (φ : ((canonicalFiberPseudofunctor p).map a.op.toLoc).toFunctor.obj N ⟶ M) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (φ ≫ (((canonicalFiberPseudofunctor p).mapId (.mk (Opposite.op V))).inv.toNatTrans.app M))
        g b g h hid =
      (((canonicalFiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc b.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq a g b h)).hom.toNatTrans.app N) ≫
        ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := by
  -- Reduce the right unit shell to the same inverse-hom pair, now after the pulled morphism.
  subst h
  let t := ((canonicalFiberPseudofunctor p).mapComp' a.op.toLoc g.op.toLoc
    (a.op.toLoc ≫ g.op.toLoc) (FibredCategoryMor.comp_toLoc_eq a g (g ≫ a) rfl)).hom.toNatTrans.app N
  let e := (canonicalFiberPseudofunctor p).mapId (.mk (Opposite.op V))
  suffices hsimp :
      t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫
          ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.inv.toNatTrans.app M) ≫
          ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.hom.toNatTrans.app M) =
        t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ by
    simpa [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
      Pseudofunctor.mapComp'_id_comp_inv_app, t, e, Functor.map_comp, Category.assoc]
      using hsimp
  have hmap := (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map_comp
    (e.inv.toNatTrans.app M) (e.hom.toNatTrans.app M))
  have hpair :
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.inv.toNatTrans.app M) ≫
          ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map (e.hom.toNatTrans.app M) =
        ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
          (e.inv.toNatTrans.app M ≫ e.hom.toNatTrans.app M) := hmap.symm
  have heq : e.inv.toNatTrans.app M ≫ e.hom.toNatTrans.app M = 𝟙 M := by
    change (fun k ↦ k.toNatTrans.app M) (e.inv ≫ e.hom) =
      (fun k ↦ k.toNatTrans.app M) (𝟙 (𝟙 ((canonicalFiberPseudofunctor p).obj
        (.mk (Opposite.op V)))))
    exact congrArg (fun k ↦ k.toNatTrans.app M) e.inv_hom_id
  have hcollapse :
      t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫
        ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map
          (e.inv.toNatTrans.app M ≫ e.hom.toNatTrans.app M) =
      t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ := by
    have hmapId := congrArg (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map) heq
    exact (congrArg (fun k ↦
      t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ k) hmapId).trans
        ((congrArg (fun k ↦
          t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ k)
          (((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map_id M)).trans
          (by simp))
  simpa only [Category.assoc] using
    (congrArg (fun k ↦
      t ≫ ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ ≫ k) hpair).trans
      hcollapse

/-- Helper for Chap08 Lemma 8 12 2: a composite comparison whose first leg is represented by
the chosen identity pullback collapses after pulling that identity restriction along the second
leg. -/
private theorem canonicalFiberPseudofunctor_mapComp_hom_map_identityRestriction
    (p : S ⥤ D) [p.IsFibered] {V W : D} (e : V ⟶ V) (g : W ⟶ V)
    (hid : g ≫ e = g) (M : p.Fiber V)
    (φ : ((canonicalFiberPseudofunctor p).map e.op.toLoc).toFunctor.obj M ⟶ M)
    (hφ : φ.1 = (canonicalPullbackChoice p).map e M) :
    (((canonicalFiberPseudofunctor p).mapComp' e.op.toLoc g.op.toLoc g.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq e g g hid)).hom.toNatTrans.app M) ≫
      ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ =
    𝟙 _ := by
  -- Compare the two endomorphisms after the cartesian arrow over `g`; both become the chosen
  -- pullback arrow for `g`.
  apply Functor.Fiber.hom_ext
  let compHom :=
    (((canonicalFiberPseudofunctor p).mapComp' e.op.toLoc g.op.toLoc g.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq e g g hid)).hom.toNatTrans.app M)
  let mapφ := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.map φ
  let Mg := ((canonicalFiberPseudofunctor p).map g.op.toLoc).toFunctor.obj M
  let tailG := (canonicalPullbackChoice p).map g M
  let tailGE := (canonicalPullbackChoice p).map g
    (((canonicalFiberPseudofunctor p).map e.op.toLoc).toFunctor.obj M)
  let tailE := (canonicalPullbackChoice p).map e M
  change (compHom ≫ mapφ).1 = (𝟙 Mg : Mg ⟶ Mg).1
  letI : p.IsStronglyCartesian g tailG :=
    (canonicalPullbackChoice p).isStronglyCartesian g M
  have htailG : p.IsCartesian g tailG := by infer_instance
  have hlhsLift : p.IsHomLift (𝟙 W) (compHom ≫ mapφ).1 := by
    exact (compHom ≫ mapφ).2
  have hrhsLift : p.IsHomLift (𝟙 W) (𝟙 Mg : Mg ⟶ Mg).1 := by
    exact (𝟙 Mg : Mg ⟶ Mg).2
  apply @Functor.IsCartesian.ext D S _ _ p _ _ _ _ g tailG htailG _
    (compHom ≫ mapφ).1 (𝟙 Mg : Mg ⟶ Mg).1 hlhsLift hrhsLift
  have hmap :
      mapφ.1 ≫ tailG = tailGE ≫ φ.1 := by
    simpa [mapφ, tailG, tailGE] using
      FibredCategoryMor.canonical_pullbackFunctor_map_fac (p := p) (f := g) (φ := φ)
  have hcomp :
      compHom.1 ≫ tailGE ≫ tailE = tailG := by
    simpa [compHom, tailG, tailGE, tailE] using
      FibredCategoryMor.canonicalFiberPseudofunctor_mapComp'_hom_app_fac
        p e g g hid M
  have hleft : (compHom ≫ mapφ).1 ≫ tailG = tailG := by
    calc
      (compHom ≫ mapφ).1 ≫ tailG =
          (compHom.1 ≫ mapφ.1) ≫ tailG := by
          change (compHom.1 ≫ mapφ.1) ≫ tailG = (compHom.1 ≫ mapφ.1) ≫ tailG
          rfl
      _ = compHom.1 ≫ (mapφ.1 ≫ tailG) := by
          exact Category.assoc compHom.1 mapφ.1 tailG
      _ = compHom.1 ≫ (tailGE ≫ φ.1) := by
          exact congrArg (fun k ↦ compHom.1 ≫ k) hmap
      _ = compHom.1 ≫ (tailGE ≫ tailE) := by
          rw [hφ]
      _ = tailG := by
          simpa [Category.assoc] using hcomp
  change (compHom ≫ mapφ).1 ≫ tailG = 𝟙 Mg.1 ≫ tailG
  simpa only [Category.id_comp] using hleft

/-- Helper for Chap08 Lemma 8 12 2: the target-restriction comparison for a composite restriction
agrees with first comparing along the upper leg and then along the lower leg, in the inverse
`mapComp'` orientation. -/
private theorem pullbackProjection_targetRestrictionIso_comp_inv_boundary
    (p : S ⥤ D) [p.IsFibered] {U V W : C} (a : V ⟶ U) (g : W ⟶ V)
    (b : W ⟶ U) (h : g ≫ a = b)
    (htarget : u.map g ≫ u.map a = u.map b)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    let Xa :=
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        a.op.toLoc).toFunctor.obj X
    let sourceLeft :=
      (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
        a.op.toLoc g.op.toLoc b.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq a g b h)).inv.toNatTrans.app X)
    let targetLeft :=
      (((canonicalFiberPseudofunctor p).mapComp'
        (u.map a).op.toLoc (u.map g).op.toLoc (u.map b).op.toLoc
        (FibredCategoryMor.comp_toLoc_eq (u.map a) (u.map g) (u.map b) htarget)).inv.toNatTrans.app
        (pullbackProjection_targetFiberObj u p X))
    (pullbackProjection_targetRestrictionIso u p g Xa).hom ≫
        ((canonicalFiberPseudofunctor p).map (u.map g).op.toLoc).toFunctor.map
          (pullbackProjection_targetRestrictionIso u p a X).hom ≫
        targetLeft =
      (pullbackProjection_targetFiberFunctor u p W).map sourceLeft ≫
        (pullbackProjection_targetRestrictionIso u p b X).hom := by
  -- The two displayed morphisms are the same comparison with the composite cartesian pullback.
  let Xa :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
      a.op.toLoc).toFunctor.obj X
  let sourceLeft :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
      a.op.toLoc g.op.toLoc b.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq a g b h)).inv.toNatTrans.app X)
  let targetLeft :=
    (((canonicalFiberPseudofunctor p).mapComp'
      (u.map a).op.toLoc (u.map g).op.toLoc (u.map b).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq (u.map a) (u.map g) (u.map b) htarget)).inv.toNatTrans.app
      (pullbackProjection_targetFiberObj u p X))
  let sourceUnit :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapId
      (.mk (Opposite.op V))).hom.toNatTrans.app Xa)
  let eg := pullbackProjection_targetRestrictionIso u p g Xa
  let ea := pullbackProjection_targetRestrictionIso u p a X
  let eb := pullbackProjection_targetRestrictionIso u p b X
  let Fover := pullbackProjection_targetFiberFunctor u p W
  let Fg := ((canonicalFiberPseudofunctor p).map (u.map g).op.toLoc).toFunctor
  have hid : g ≫ 𝟙 V = g := by simp
  have hidTarget : u.map g ≫ u.map (𝟙 V) = u.map g := by
    rw [Functor.map_id]
    simp
  have htargetUnitRaw :=
    pullbackProjection_targetRestrictionIso_id_inv_mapId_hom_explicit u p Xa
  have hsourcePull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom sourceUnit g g b hid h =
        sourceLeft := by
    have hpull :=
      canonicalFiberPseudofunctor_pullHom_mapId_hom
        (CategoricalPullback.π₁ u p) a g b hid h X (𝟙 Xa)
    simpa [sourceUnit, sourceLeft] using hpull
  have htargetPull :
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
          ((pullbackProjection_targetRestrictionIso u p (𝟙 V) Xa).inv ≫
            (pullbackProjection_targetFiberFunctor u p V).map sourceUnit ≫ ea.hom)
          (u.map g) (u.map g) (u.map b) hidTarget htarget =
        Fg.map ea.hom ≫ targetLeft := by
    let targetUnit :=
      (pullbackProjection_targetRestrictionIso u p (𝟙 V) Xa).inv ≫
        (pullbackProjection_targetFiberFunctor u p V).map sourceUnit
    let targetCompHom :=
      (((canonicalFiberPseudofunctor p).mapComp'
        (u.map (𝟙 V)).op.toLoc (u.map g).op.toLoc (u.map g).op.toLoc
        (FibredCategoryMor.comp_toLoc_eq (u.map (𝟙 V)) (u.map g) (u.map g)
          hidTarget)).hom.toNatTrans.app
        (pullbackProjection_targetFiberObj u p Xa))
    have hunit :
        targetUnit =
          (⟨(canonicalPullbackChoice p).map (u.map (𝟙 V))
              (pullbackProjection_targetFiberObj u p Xa), by
            rw [← Functor.map_id u V]
            exact ((canonicalPullbackChoice p).isStronglyCartesian (u.map (𝟙 V))
                (pullbackProjection_targetFiberObj u p Xa)).toIsHomLift
           ⟩ :
            ((canonicalFiberPseudofunctor p).map (u.map (𝟙 V)).op.toLoc).toFunctor.obj
              (pullbackProjection_targetFiberObj u p Xa) ⟶
            pullbackProjection_targetFiberObj u p Xa) := by
      simpa [targetUnit, sourceUnit] using htargetUnitRaw
    have hunitUnderlying :
        targetUnit.1 =
          (canonicalPullbackChoice p).map (u.map (𝟙 V))
            (pullbackProjection_targetFiberObj u p Xa) := by
      exact congrArg Subtype.val hunit
    have hcollapse :
        targetCompHom ≫ Fg.map targetUnit = 𝟙 _ := by
      simpa [targetCompHom, targetUnit, Fg] using
        canonicalFiberPseudofunctor_mapComp_hom_map_identityRestriction
          p (u.map (𝟙 V)) (u.map g) hidTarget
          (pullbackProjection_targetFiberObj u p Xa) targetUnit hunitUnderlying
    have hmap :
        Fg.map (targetUnit ≫ ea.hom) = Fg.map targetUnit ≫ Fg.map ea.hom := by
      exact Fg.map_comp targetUnit ea.hom
    let targetUnitLeft := (pullbackProjection_targetRestrictionIso u p (𝟙 V) Xa).inv
    let targetUnitRight := (pullbackProjection_targetFiberFunctor u p V).map sourceUnit
    have hunitMap :
        Fg.map targetUnit = Fg.map targetUnitLeft ≫ Fg.map targetUnitRight := by
      dsimp [targetUnit, targetUnitLeft, targetUnitRight]
      exact Fg.map_comp _ _
    have hcollapseExpanded :
        targetCompHom ≫ Fg.map targetUnitLeft ≫ Fg.map targetUnitRight = 𝟙 _ := by
      calc
        targetCompHom ≫ Fg.map targetUnitLeft ≫ Fg.map targetUnitRight =
            targetCompHom ≫ (Fg.map targetUnitLeft ≫ Fg.map targetUnitRight) := by
            rfl
        _ = targetCompHom ≫ Fg.map targetUnit := by
            exact congrArg (fun k ↦ targetCompHom ≫ k) hunitMap.symm
        _ = 𝟙 _ := hcollapse
    dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    simp only [Functor.map_comp, Category.assoc]
    have hcollapseExpandedRight :
        (targetCompHom ≫ Fg.map targetUnitLeft ≫ Fg.map targetUnitRight) ≫
            Fg.map ea.hom =
          𝟙 (Fg.obj (pullbackProjection_targetFiberObj u p Xa)) ≫ Fg.map ea.hom := by
      exact congrArg (fun k ↦ k ≫ Fg.map ea.hom) hcollapseExpanded
    calc
      targetCompHom ≫ Fg.map targetUnitLeft ≫ Fg.map targetUnitRight ≫
          Fg.map ea.hom ≫ targetLeft =
          ((targetCompHom ≫ Fg.map targetUnitLeft ≫ Fg.map targetUnitRight) ≫
              Fg.map ea.hom) ≫ targetLeft := by
          simp only [Category.assoc]
      _ = (𝟙 (Fg.obj (pullbackProjection_targetFiberObj u p Xa)) ≫
            Fg.map ea.hom) ≫ targetLeft := by
          rw [hcollapseExpandedRight]
      _ = Fg.map ea.hom ≫ targetLeft := by
          simp [Fg, Xa]
  have hconj :=
    pullbackProjection_targetRestrictionIso_pullHom_conjugation_pair u p
      (𝟙 V) a g g b hid h hidTarget htarget Xa X sourceUnit
  have hnormalized :
      eg.inv ≫ Fover.map sourceLeft ≫ eb.hom =
        Fg.map ea.hom ≫ targetLeft := by
    have htargetPull' := by
      simpa [ea] using htargetPull
    rw [hsourcePull] at hconj
    have hconj' := hconj.trans htargetPull'
    simpa [eg, eb, Fover, sourceLeft, ea, Fg, targetLeft] using hconj'
  calc
    eg.hom ≫ Fg.map ea.hom ≫ targetLeft =
        eg.hom ≫ (eg.inv ≫ Fover.map sourceLeft ≫ eb.hom) := by
        rw [hnormalized]
        rfl
    _ = (eg.hom ≫ eg.inv) ≫ Fover.map sourceLeft ≫ eb.hom := by
        simp only [Category.assoc]
    _ = Fover.map sourceLeft ≫ eb.hom := by
        rw [eg.hom_inv_id]
        simp only [Category.id_comp]
        rfl

/-- Helper for Chap08 Lemma 8 12 2: the target-restriction comparison for a composite restriction
agrees with first comparing along the upper leg and then along the lower leg, in the hom
`mapComp'` orientation. -/
private theorem pullbackProjection_targetRestrictionIso_comp_hom_boundary
    (p : S ⥤ D) [p.IsFibered] {U V W : C} (a : V ⟶ U) (g : W ⟶ V)
    (b : W ⟶ U) (h : g ≫ a = b)
    (htarget : u.map g ≫ u.map a = u.map b)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    let Xa :=
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        a.op.toLoc).toFunctor.obj X
    let sourceRight :=
      (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
        a.op.toLoc g.op.toLoc b.op.toLoc
        (FibredCategoryMor.comp_toLoc_eq a g b h)).hom.toNatTrans.app X)
    let targetRight :=
      (((canonicalFiberPseudofunctor p).mapComp'
        (u.map a).op.toLoc (u.map g).op.toLoc (u.map b).op.toLoc
        (FibredCategoryMor.comp_toLoc_eq (u.map a) (u.map g) (u.map b) htarget)).hom.toNatTrans.app
        (pullbackProjection_targetFiberObj u p X))
    (pullbackProjection_targetFiberFunctor u p W).map sourceRight ≫
        (pullbackProjection_targetRestrictionIso u p g Xa).hom ≫
        ((canonicalFiberPseudofunctor p).map (u.map g).op.toLoc).toFunctor.map
          (pullbackProjection_targetRestrictionIso u p a X).hom =
      (pullbackProjection_targetRestrictionIso u p b X).hom ≫ targetRight := by
  -- The two displayed morphisms are the same comparison with the composite cartesian pullback.
  -- Instead of repeating the transport calculation, invert the preceding `inv`-oriented
  -- boundary and cancel the two `mapComp'` isomorphism pairs explicitly.
  let Xa :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
      a.op.toLoc).toFunctor.obj X
  let sourceIso :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
      a.op.toLoc g.op.toLoc b.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq a g b h))
  let sourceLeft := sourceIso.inv.toNatTrans.app X
  let sourceRight := sourceIso.hom.toNatTrans.app X
  let targetIso :=
    ((canonicalFiberPseudofunctor p).mapComp'
      (u.map a).op.toLoc (u.map g).op.toLoc (u.map b).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq (u.map a) (u.map g) (u.map b) htarget))
  let targetLeft := targetIso.inv.toNatTrans.app (pullbackProjection_targetFiberObj u p X)
  let targetRight := targetIso.hom.toNatTrans.app (pullbackProjection_targetFiberObj u p X)
  let eg := pullbackProjection_targetRestrictionIso u p g Xa
  let ea := pullbackProjection_targetRestrictionIso u p a X
  let eb := pullbackProjection_targetRestrictionIso u p b X
  let Fover := pullbackProjection_targetFiberFunctor u p W
  let Fg := ((canonicalFiberPseudofunctor p).map (u.map g).op.toLoc).toFunctor
  have hInv :
      eg.hom ≫ Fg.map ea.hom ≫ targetLeft = Fover.map sourceLeft ≫ eb.hom := by
    simpa [Xa, sourceIso, sourceLeft, targetIso, targetLeft, eg, ea, eb, Fover, Fg] using
      pullbackProjection_targetRestrictionIso_comp_inv_boundary u p a g b h htarget X
  have hSourceComp : sourceRight ≫ sourceLeft = 𝟙 _ := by
    simpa [sourceLeft, sourceRight] using Cat.Hom.hom_inv_id_toNatTrans_app sourceIso X
  have hSourceMap : Fover.map sourceRight ≫ Fover.map sourceLeft = 𝟙 _ := by
    calc
      Fover.map sourceRight ≫ Fover.map sourceLeft = Fover.map (sourceRight ≫ sourceLeft) := by
        exact (Fover.map_comp sourceRight sourceLeft).symm
      _ = Fover.map (𝟙 _) := by
        exact congrArg Fover.map hSourceComp
      _ = 𝟙 _ := by
        simp only [Functor.map_id]
  have hSourceCollapsed :
      (Fover.map sourceRight ≫ Fover.map sourceLeft) ≫ eb.hom ≫ targetRight =
        eb.hom ≫ targetRight := by
    have h :=
      congrArg (fun k ↦ k ≫ eb.hom ≫ targetRight) hSourceMap
    calc
      (Fover.map sourceRight ≫ Fover.map sourceLeft) ≫ eb.hom ≫ targetRight =
          𝟙 _ ≫ eb.hom ≫ targetRight := by
          simpa [Fover, pullbackProjection_targetFiberFunctor] using h
      _ = eb.hom ≫ targetRight := by
          simp only [Category.id_comp]
  have hTargetComp : targetLeft ≫ targetRight = 𝟙 _ := by
    simpa [targetLeft, targetRight] using
      Cat.Hom.inv_hom_id_toNatTrans_app targetIso (pullbackProjection_targetFiberObj u p X)
  have hTargetComp' :
      targetLeft ≫ targetRight =
        𝟙 (Fg.obj (((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
          (pullbackProjection_targetFiberObj u p X))) := by
    simpa [targetIso, Fg] using hTargetComp
  have hTargetInsert :
      eg.hom ≫ Fg.map ea.hom =
        (eg.hom ≫ Fg.map ea.hom) ≫ (targetLeft ≫ targetRight) := by
    calc
      eg.hom ≫ Fg.map ea.hom =
          (eg.hom ≫ Fg.map ea.hom) ≫
              𝟙 (Fg.obj (((canonicalFiberPseudofunctor p).map
                (u.map a).op.toLoc).toFunctor.obj
                (pullbackProjection_targetFiberObj u p X))) := by
          exact (Category.comp_id (eg.hom ≫ Fg.map ea.hom)).symm
      _ = (eg.hom ≫ Fg.map ea.hom) ≫ (targetLeft ≫ targetRight) := by
          exact congrArg (fun k ↦ (eg.hom ≫ Fg.map ea.hom) ≫ k) hTargetComp'.symm
  have hTargetCollapsed :
      eg.hom ≫ Fg.map ea.hom = Fover.map sourceLeft ≫ eb.hom ≫ targetRight := by
    have htargetWhisker :
        (eg.hom ≫ Fg.map ea.hom ≫ targetLeft) ≫ targetRight =
          (Fover.map sourceLeft ≫ eb.hom) ≫ targetRight := by
      exact congrArg (fun k ↦ k ≫ targetRight) hInv
    have htargetAssoc :
        (eg.hom ≫ Fg.map ea.hom) ≫ (targetLeft ≫ targetRight) =
          (eg.hom ≫ Fg.map ea.hom ≫ targetLeft) ≫ targetRight := by
      simp only [Category.assoc]
    have htargetWhisker' :
        (Fover.map sourceLeft ≫ eb.hom) ≫ targetRight =
          Fover.map sourceLeft ≫ eb.hom ≫ targetRight := by
      simp only [Category.assoc]
    exact hTargetInsert.trans (htargetAssoc.trans (htargetWhisker.trans htargetWhisker'))
  have hpre :
      Fover.map sourceRight ≫ eg.hom ≫ Fg.map ea.hom =
        Fover.map sourceRight ≫ (Fover.map sourceLeft ≫ eb.hom ≫ targetRight) := by
    have hpreAssoc :
        Fover.map sourceRight ≫ eg.hom ≫ Fg.map ea.hom =
          Fover.map sourceRight ≫ (eg.hom ≫ Fg.map ea.hom) := by
      rfl
    have hpreRewrite :
        Fover.map sourceRight ≫ (eg.hom ≫ Fg.map ea.hom) =
          Fover.map sourceRight ≫ (Fover.map sourceLeft ≫ eb.hom ≫ targetRight) := by
      exact congrArg (fun k ↦ Fover.map sourceRight ≫ k) hTargetCollapsed
    exact hpreAssoc.trans hpreRewrite
  have hassoc :
      Fover.map sourceRight ≫ (Fover.map sourceLeft ≫ eb.hom ≫ targetRight) =
        (Fover.map sourceRight ≫ Fover.map sourceLeft) ≫ eb.hom ≫ targetRight := by
    simp only [Category.assoc]
  exact hpre.trans (hassoc.trans hSourceCollapsed)

/-- Helper for Chap08 Lemma 8 12 2: target-restriction components identify the strictification
of the source prime object with the target prime object of the strictified target fiber object. -/
theorem pullbackProjection_targetRestriction_primeFunctor_hom
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (A : p.Fiber (u.obj U)) (I J₁ : T.Arrow) :
    let X := pullbackProjection_ofTargetFiberObj u p A
    let B := pullbackProjection_targetFiberObj u p X
    let D₀ := (pullbackProjection_sourcePrimeDescentFunctor u p T).obj X
    let gammaI := pullbackProjection_targetRestrictionIso u p I.f X
    let gammaJ := pullbackProjection_targetRestrictionIso u p J₁.f X
    ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor.map gammaI.hom ≫
      ((pullbackProjection_targetPrimeDescentFunctor u p T).obj B).hom I J₁ =
    (pullbackProjection_targetDescentDataPrime u p T D₀).hom I J₁ ≫
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor.map gammaJ.hom := by
  -- Expand the two prime descent morphisms, then paste the two composite-restriction comparison
  -- boundaries around the common restriction along the chosen source overlap.
  intro X B D₀ gammaI gammaJ
  let sq := coverSourceChosenPullback T I J₁
  let Fover := pullbackProjection_targetFiberFunctor u p sq.pullback
  let F₁ :=
    ((canonicalFiberPseudofunctor p).map
      (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor
  let F₂ :=
    ((canonicalFiberPseudofunctor p).map
      (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor
  let e₁ := pullbackProjection_targetRestrictionIso u p sq.p₁ (D₀.obj I)
  let e₂ := pullbackProjection_targetRestrictionIso u p sq.p₂ (D₀.obj J₁)
  let e := pullbackProjection_targetRestrictionIso u p sq.p X
  let sourceLeft :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
      I.f.op.toLoc sq.p₁.op.toLoc sq.p.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq I.f sq.p₁ sq.p sq.hp₁)).inv.toNatTrans.app X)
  let sourceRight :=
    (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).mapComp'
      J₁.f.op.toLoc sq.p₂.op.toLoc sq.p.op.toLoc
      (FibredCategoryMor.comp_toLoc_eq J₁.f sq.p₂ sq.p sq.hp₂)).hom.toNatTrans.app X)
  let targetLeft :=
    (((canonicalFiberPseudofunctor p).mapComp'
      (u.map I.f).op.toLoc (u.map sq.p₁).op.toLoc (u.map sq.p).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq (u.map I.f) (u.map sq.p₁) (u.map sq.p)
        (by rw [← u.map_comp, sq.hp₁]))).inv.toNatTrans.app B)
  let targetRight :=
    (((canonicalFiberPseudofunctor p).mapComp'
      (u.map J₁.f).op.toLoc (u.map sq.p₂).op.toLoc (u.map sq.p).op.toLoc
      (FibredCategoryMor.comp_toLoc_eq (u.map J₁.f) (u.map sq.p₂) (u.map sq.p)
        (by rw [← u.map_comp, sq.hp₂]))).hom.toNatTrans.app B)
  have hD₀ : D₀.hom I J₁ = sourceLeft ≫ sourceRight := by
    simp [D₀, sq, sourceLeft, sourceRight, pullbackProjection_sourcePrimeDescentFunctor]
  have hleft :
      e₁.hom ≫ F₁.map gammaI.hom ≫ targetLeft =
        Fover.map sourceLeft ≫ e.hom := by
    simpa [e₁, e, F₁, Fover, gammaI, B, sq, sourceLeft, targetLeft,
      coverImageChosenPullback, imageChosenPullback] using
      pullbackProjection_targetRestrictionIso_comp_inv_boundary u p I.f sq.p₁ sq.p
        sq.hp₁ (by rw [← u.map_comp, sq.hp₁]) X
  have hright :
      Fover.map sourceRight ≫ e₂.hom ≫ F₂.map gammaJ.hom =
        e.hom ≫ targetRight := by
    simpa [e₂, e, F₂, Fover, gammaJ, B, sq, sourceRight, targetRight,
      coverImageChosenPullback, imageChosenPullback] using
      pullbackProjection_targetRestrictionIso_comp_hom_boundary u p J₁.f sq.p₂ sq.p
        sq.hp₂ (by rw [← u.map_comp, sq.hp₂]) X
  simp only [pullbackProjection_targetPrimeDescentFunctor, Functor.comp_obj,
    Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData'.fromDescentDataFunctor_obj,
    Pseudofunctor.DescentData'.ofDescentData_obj, Pseudofunctor.DescentData.ofObj_obj,
    Pseudofunctor.DescentData'.ofDescentData_hom, Pseudofunctor.DescentData.ofObj_hom,
    Cat.Hom.comp_toFunctor, pullbackProjection_targetDescentDataPrime,
    pullbackProjection_targetDescentDataPrimeHom, Category.assoc]
  change F₁.map gammaI.hom ≫ targetLeft ≫ targetRight =
    e₁.inv ≫ Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫ F₂.map gammaJ.hom
  refine (cancel_epi e₁.hom).1 ?_
  have hstepLeft :
      e₁.hom ≫ (F₁.map gammaI.hom ≫ targetLeft ≫ targetRight) =
        Fover.map sourceLeft ≫ e.hom ≫ targetRight := by
    calc
      e₁.hom ≫ (F₁.map gammaI.hom ≫ targetLeft ≫ targetRight)
          = (e₁.hom ≫ F₁.map gammaI.hom ≫ targetLeft) ≫ targetRight := by
            simp only [Category.assoc]
      _ = (Fover.map sourceLeft ≫ e.hom) ≫ targetRight := by
            exact congrArg (fun k ↦ k ≫ targetRight) hleft
      _ = Fover.map sourceLeft ≫ e.hom ≫ targetRight := by
            simp only [Category.assoc]
  have hstepRight :
      Fover.map sourceLeft ≫ e.hom ≫ targetRight =
        Fover.map sourceLeft ≫ Fover.map sourceRight ≫ e₂.hom ≫ F₂.map gammaJ.hom := by
    simpa only [Category.assoc] using
      congrArg (fun k ↦ Fover.map sourceLeft ≫ k) hright.symm
  have hstepMap :
      Fover.map sourceLeft ≫ Fover.map sourceRight ≫ e₂.hom ≫ F₂.map gammaJ.hom =
        Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫ F₂.map gammaJ.hom := by
    have hmap : Fover.map sourceLeft ≫ Fover.map sourceRight =
        Fover.map (D₀.hom I J₁) := by
      rw [← Fover.map_comp]
      exact congrArg Fover.map hD₀.symm
    calc
      Fover.map sourceLeft ≫ Fover.map sourceRight ≫ e₂.hom ≫ F₂.map gammaJ.hom =
          (Fover.map sourceLeft ≫ Fover.map sourceRight) ≫ e₂.hom ≫
            F₂.map gammaJ.hom := by
            simp only [Category.assoc]
      _ = Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫ F₂.map gammaJ.hom := by
            rw [hmap]
            rfl
  have hstepCancel :
      Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫ F₂.map gammaJ.hom =
        e₁.hom ≫ (e₁.inv ≫ Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫
          F₂.map gammaJ.hom) := by
    calc
      Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫ F₂.map gammaJ.hom =
          (e₁.hom ≫ e₁.inv) ≫ Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫
            F₂.map gammaJ.hom := by
            rw [e₁.hom_inv_id]
            simp only [Category.id_comp]
            rfl
      _ = e₁.hom ≫ (e₁.inv ≫ Fover.map (D₀.hom I J₁) ≫ e₂.hom ≫
            F₂.map gammaJ.hom) := by
            simp only [Category.assoc]
  exact hstepLeft.trans (hstepRight.trans (hstepMap.trans hstepCancel))

/-- Helper for Chap08 Lemma 8 12 2: the target-fiber counit components commute with the target
prime descent morphisms. -/
theorem pullbackProjection_targetFiberCounit_primeFunctor_hom
    [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan u]
    (p : S ⥤ D) [p.IsFibered] {U : C} (T : J.Cover U)
    (A : p.Fiber (u.obj U)) (I J₁ : T.Arrow) :
    let X := pullbackProjection_ofTargetFiberObj u p A
    let B := pullbackProjection_targetFiberObj u p X
    ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₁.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor p).map (u.map I.f).op.toLoc).toFunctor.map
          (pullbackProjection_targetFiberCounitIso u p A).hom) ≫
      ((pullbackProjection_targetPrimeDescentFunctor u p T).obj A).hom I J₁ =
    ((pullbackProjection_targetPrimeDescentFunctor u p T).obj B).hom I J₁ ≫
      ((canonicalFiberPseudofunctor p).map
        (coverImageChosenPullback u T I J₁).p₂.op.toLoc).toFunctor.map
        (((canonicalFiberPseudofunctor p).map (u.map J₁.f).op.toLoc).toFunctor.map
          (pullbackProjection_targetFiberCounitIso u p A).hom) := by
  -- This is the component square of the target prime descent functor applied to the counit
  -- morphism from the strictified target object back to `A`.
  intro X B
  simpa [B, pullbackProjection_targetPrimeDescentFunctor] using
    ((pullbackProjection_targetPrimeDescentFunctor u p T).map
      (pullbackProjection_targetFiberCounitIso u p A).hom).comm I J₁

end

end CategoryTheory
