import stacks_proof.stacks_project.Chap08.Lemma_8_12_2.TargetFiberEquivalence

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Lemma 8.12.2: the target-base map of the pullback restriction composes with the
second component of the canonical pullback restriction to the target-base map of the original
object pulled back along `u.map a`. -/
theorem pullbackProjection_targetBaseMap_comp_restriction_snd
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    pullbackProjection_targetBaseMap u p
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≫
      p.map ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd =
        u.map a ≫ pullbackProjection_targetBaseMap u p X := by
  -- Rewrite the pseudofunctorial restriction as the chosen pullback object, where its chosen
  -- map has an explicit first component over `a`.
  change pullbackProjection_targetBaseMap u p
      (a ^*[canonicalPullbackChoice (CategoricalPullback.π₁ u p)] X) ≫
    p.map ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd =
      u.map a ≫ pullbackProjection_targetBaseMap u p X
  have hfst : ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).fst =
      eqToHom ((a ^*[canonicalPullbackChoice (CategoricalPullback.π₁ u p)] X).2) ≫
        a ≫ eqToHom X.2.symm := by
    -- The chosen pullback restriction lies over `a`, so its first component is the transported
    -- representative of `a` between the selected fiber representatives.
    letI : (CategoricalPullback.π₁ u p).IsHomLift a
        ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X) :=
      (canonicalPullbackChoice (CategoricalPullback.π₁ u p)).isStronglyCartesian a X |>.toIsHomLift
    simpa using
      (IsHomLift.fac' (CategoricalPullback.π₁ u p) a
        ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X))
  have hw := ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).w
  calc
    pullbackProjection_targetBaseMap u p
        (a ^*[canonicalPullbackChoice (CategoricalPullback.π₁ u p)] X) ≫
        p.map ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).snd
        =
          eqToHom (congrArg u.obj
              ((a ^*[canonicalPullbackChoice (CategoricalPullback.π₁ u p)] X).2)).symm ≫
            (u.map ((canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X).fst ≫
              X.1.iso.hom) := by
          -- The categorical-pullback square changes the second-component composite into the
          -- image of the first component followed by the structural isomorphism of `X`.
          simpa [pullbackProjection_targetBaseMap, Category.assoc] using
            congrArg
              (fun k ↦
                eqToHom (congrArg u.obj
                  ((a ^*[canonicalPullbackChoice (CategoricalPullback.π₁ u p)] X).2)).symm ≫ k)
              hw.symm
    _ = u.map a ≫ pullbackProjection_targetBaseMap u p X := by
          -- Substituting the first-component lift equation cancels the two transport isomorphisms.
          rw [hfst]
          simp [pullbackProjection_targetBaseMap, Category.assoc, eqToHom_map]

/-- Helper for Lemma 8.12.2: the strict pullback object associated to a target-fiber restriction
satisfies the categorical-pullback square. -/
theorem pullbackProjection_ofTargetRestrictionAmbientHom_w
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : p.Fiber (u.obj U)) :
    u.map a ≫ (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom =
      (pullbackProjection_ofTargetFiberObj u p
          (u.map a ^*[canonicalPullbackChoice p] X)).1.iso.hom ≫
        p.map ((canonicalPullbackChoice p).map (u.map a) X) := by
  -- The chosen target pullback map lies over `u.map a`; rewriting its lift equation gives exactly
  -- the square needed for the categorical-pullback morphism.
  let m := (canonicalPullbackChoice p).map (u.map a) X
  letI : p.IsStronglyCartesian (u.map a) m :=
    (canonicalPullbackChoice p).isStronglyCartesian (u.map a) X
  letI : p.IsHomLift (u.map a) m := inferInstance
  have hm := IsHomLift.fac' p (u.map a) m
  dsimp [pullbackProjection_ofTargetFiberObj]
  rw [hm]
  simp

/-- Helper for Lemma 8.12.2: the ambient pullback morphism induced by restricting a strict target
object along `u.map a`. -/
noncomputable def pullbackProjection_ofTargetRestrictionAmbientHom
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : p.Fiber (u.obj U)) :
    (pullbackProjection_ofTargetFiberObj u p
        (u.map a ^*[canonicalPullbackChoice p] X)).1 ⟶
      (pullbackProjection_ofTargetFiberObj u p X).1 :=
  { fst := a
    snd := (canonicalPullbackChoice p).map (u.map a) X
    w := pullbackProjection_ofTargetRestrictionAmbientHom_w u p a X }

/-- Helper for Lemma 8.12.2: the strict target-restriction morphism lies over the base arrow
`a` in the categorical pullback. -/
theorem pullbackProjection_ofTargetRestrictionAmbientHom_isHomLift
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : p.Fiber (u.obj U)) :
    (CategoricalPullback.π₁ u p).IsHomLift a
      (pullbackProjection_ofTargetRestrictionAmbientHom u p a X) := by
  -- Its first component is `a`, so the hom-lift condition for the first projection is immediate
  -- after unfolding the strict source and target fibers.
  exact
    IsHomLift.of_fac' (CategoricalPullback.π₁ u p) a
      (pullbackProjection_ofTargetRestrictionAmbientHom u p a X)
      (pullbackProjection_ofTargetFiberObj u p
        (u.map a ^*[canonicalPullbackChoice p] X)).2
      (pullbackProjection_ofTargetFiberObj u p X).2 (by
        dsimp [pullbackProjection_ofTargetRestrictionAmbientHom,
          pullbackProjection_ofTargetFiberObj]
        simp)

/-- Helper for Lemma 8.12.2: the strict target-restriction morphism is cartesian for the pullback
projection. -/
theorem pullbackProjection_ofTargetRestrictionAmbientHom_isCartesian
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : p.Fiber (u.obj U)) :
    (CategoricalPullback.π₁ u p).IsCartesian a
      (pullbackProjection_ofTargetRestrictionAmbientHom u p a X) := by
  -- A morphism into the strict target restriction is reconstructed from its second component by
  -- the strongly cartesian universal property of the chosen target pullback map.
  let φ := pullbackProjection_ofTargetRestrictionAmbientHom u p a X
  let m := (canonicalPullbackChoice p).map (u.map a) X
  letI : p.IsStronglyCartesian (u.map a) m :=
    (canonicalPullbackChoice p).isStronglyCartesian (u.map a) X
  letI : (CategoricalPullback.π₁ u p).IsHomLift a φ :=
    pullbackProjection_ofTargetRestrictionAmbientHom_isHomLift u p a X
  refine { universal_property := ?_ }
  intro z θ hθ
  letI : (CategoricalPullback.π₁ u p).IsHomLift a θ := hθ
  let hdom := IsHomLift.domain_eq (CategoricalPullback.π₁ u p) a θ
  have hθfst : θ.fst = eqToHom hdom ≫ a := by
    simpa [pullbackProjection_ofTargetFiberObj] using
      IsHomLift.fac' (CategoricalPullback.π₁ u p) a θ
  let gD : p.obj z.snd ⟶ u.obj V := z.iso.inv ≫ u.map (eqToHom hdom)
  have hθsnd : p.IsHomLift (gD ≫ u.map a) θ.snd := by
    apply IsHomLift.of_fac' p (gD ≫ u.map a) θ.snd rfl X.2
    have hw := θ.w
    calc
      p.map θ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map θ.snd) := by
        simp
      _ =
          z.iso.inv ≫
            (u.map θ.fst ≫ (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom) := by
          rw [← hw]
      _ =
          z.iso.inv ≫
            (u.map (eqToHom hdom ≫ a) ≫
              (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom) := by
          rw [hθfst]
          rfl
      _ =
          z.iso.inv ≫
            ((u.map (eqToHom hdom) ≫ u.map a) ≫
              (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom) := by
          exact
            congrArg
              (fun k ↦ z.iso.inv ≫
                (k ≫ (pullbackProjection_ofTargetFiberObj u p X).1.iso.hom))
              (u.map_comp (eqToHom hdom) a)
      _ = eqToHom rfl ≫ (gD ≫ u.map a) ≫ eqToHom X.2.symm := by
          dsimp [gD, pullbackProjection_ofTargetFiberObj]
          simp [Category.assoc, eqToHom_map]
  have hExists :=
    @Functor.IsStronglyCartesian.universal_property _ _ _ _ p _ _ _ _ (u.map a) m
      inferInstance _ _ gD (gD ≫ u.map a) rfl θ.snd hθsnd
  obtain ⟨χsnd, hχsnd, hχuniq⟩ := hExists
  let sourcePB :=
    pullbackProjection_ofTargetFiberObj u p (u.map a ^*[canonicalPullbackChoice p] X)
  let χ : z ⟶ sourcePB.1 :=
    { fst := eqToHom hdom
      snd := χsnd
      w := by
        letI : p.IsHomLift gD χsnd := hχsnd.1
        have hχfac := IsHomLift.fac' p gD χsnd
        dsimp [sourcePB, pullbackProjection_ofTargetFiberObj]
        rw [hχfac]
        dsimp [gD]
        simp [Category.assoc, eqToHom_map] }
  have hχlift : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 V) χ := by
    apply IsHomLift.of_fac' (CategoricalPullback.π₁ u p) (𝟙 V) χ hdom sourcePB.2
    dsimp [χ, sourcePB, pullbackProjection_ofTargetFiberObj]
    simp
  refine ⟨χ, ⟨hχlift, ?_⟩, ?_⟩
  · apply CategoricalPullback.hom_ext
    · dsimp [χ, φ, pullbackProjection_ofTargetRestrictionAmbientHom]
      rw [hθfst]
      rfl
    · dsimp [χ, φ, pullbackProjection_ofTargetRestrictionAmbientHom]
      exact hχsnd.2
  · intro τ hτ
    letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 V) τ := hτ.1
    have hτfst : τ.fst = eqToHom hdom := by
      simpa [sourcePB, pullbackProjection_ofTargetFiberObj] using
        IsHomLift.fac' (CategoricalPullback.π₁ u p) (𝟙 V) τ
    have hτsndLift : p.IsHomLift gD τ.snd := by
      apply IsHomLift.of_fac' p gD τ.snd rfl
        (u.map a ^*[canonicalPullbackChoice p] X).2
      have hw := τ.w
      calc
        p.map τ.snd = z.iso.inv ≫ (z.iso.hom ≫ p.map τ.snd) := by
          simp
        _ = z.iso.inv ≫ (u.map τ.fst ≫ sourcePB.1.iso.hom) := by
          rw [← hw]
        _ = z.iso.inv ≫ (u.map (eqToHom hdom) ≫ sourcePB.1.iso.hom) := by
          rw [hτfst]
          rfl
        _ = eqToHom rfl ≫ gD ≫
            eqToHom (u.map a ^*[canonicalPullbackChoice p] X).2.symm := by
          dsimp [gD, sourcePB, pullbackProjection_ofTargetFiberObj]
          simp [Category.assoc, eqToHom_map]
    have hτcomp_snd : τ.snd ≫ m = θ.snd := by
      simpa [φ, pullbackProjection_ofTargetRestrictionAmbientHom] using
        congrArg CategoricalPullback.Hom.snd hτ.2
    have hτsnd : τ.snd = χsnd := hχuniq τ.snd ⟨hτsndLift, hτcomp_snd⟩
    apply CategoricalPullback.hom_ext
    · simpa [χ] using hτfst
    · simpa [χ] using hτsnd

/-- Helper for Lemma 8.12.2: restricting a pullback-fiber object and then strictifying its target
component agrees, up to the canonical cartesian-domain isomorphism, with first strictifying the
target component and then restricting it in the target fiber. -/
noncomputable def pullbackProjection_targetRestrictionIso
    (p : S ⥤ D) [p.IsFibered] {U V : C} (a : V ⟶ U)
    (X : (CategoricalPullback.π₁ u p).Fiber U) :
    pullbackProjection_targetFiberObj u p
        (((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X) ≅
      ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
        (pullbackProjection_targetFiberObj u p X) :=
  -- Compare the two pullback restrictions as cartesian arrows with the same codomain in the
  -- categorical pullback, then strictify the resulting vertical isomorphism on second components.
  let A : (CategoricalPullback.π₁ u p).Fiber V :=
    ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map a.op.toLoc).toFunctor.obj X
  let R : p.Fiber (u.obj V) :=
    ((canonicalFiberPseudofunctor p).map (u.map a).op.toLoc).toFunctor.obj
      (pullbackProjection_targetFiberObj u p X)
  let B : (CategoricalPullback.π₁ u p).Fiber V :=
    pullbackProjection_ofTargetFiberObj u p R
  let φB₀ : B.1 ⟶ (pullbackProjection_ofTargetFiberObj u p
      (pullbackProjection_targetFiberObj u p X)).1 :=
    pullbackProjection_ofTargetRestrictionAmbientHom u p a
      (pullbackProjection_targetFiberObj u p X)
  let γ : pullbackProjection_ofTargetFiberObj u p
      (pullbackProjection_targetFiberObj u p X) ⟶ X :=
    pullbackProjection_targetFiberComparisonHom u p X
  letI : IsIso γ := pullbackProjection_targetFiberComparisonHom_isIso u p X
  letI : IsIso γ.1 := by
    change IsIso ((Functor.Fiber.fiberInclusion :
      (CategoricalPullback.π₁ u p).Fiber U ⥤ CategoricalPullback u p).map γ)
    infer_instance
  let γIso :
      (pullbackProjection_ofTargetFiberObj u p
        (pullbackProjection_targetFiberObj u p X)).1 ≅ X.1 :=
    asIso γ.1
  letI : (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) γIso.hom := by
    change (CategoricalPullback.π₁ u p).IsHomLift (𝟙 U) γ.1
    exact γ.2
  let φB : B.1 ⟶ X.1 := φB₀ ≫ γIso.hom
  letI : (CategoricalPullback.π₁ u p).IsCartesian a φB₀ :=
    pullbackProjection_ofTargetRestrictionAmbientHom_isCartesian u p a
      (pullbackProjection_targetFiberObj u p X)
  letI : (CategoricalPullback.π₁ u p).IsCartesian a φB := by
    dsimp [φB]
    infer_instance
  let φA : A.1 ⟶ X.1 :=
    (canonicalPullbackChoice (CategoricalPullback.π₁ u p)).map a X
  letI : (CategoricalPullback.π₁ u p).IsStronglyCartesian a φA :=
    (canonicalPullbackChoice (CategoricalPullback.π₁ u p)).isStronglyCartesian a X
  letI : (CategoricalPullback.π₁ u p).IsCartesian a φA := inferInstance
  let eAmbient : A.1 ≅ B.1 :=
    Functor.IsCartesian.domainUniqueUpToIso (CategoricalPullback.π₁ u p) a φB φA
  let eFiber : A ≅ B :=
    { hom := ⟨eAmbient.hom, by
        change (CategoricalPullback.π₁ u p).IsHomLift (𝟙 V) eAmbient.hom
        infer_instance⟩
      inv := ⟨eAmbient.inv, by
        change (CategoricalPullback.π₁ u p).IsHomLift (𝟙 V) eAmbient.inv
        infer_instance⟩
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact eAmbient.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact eAmbient.inv_hom_id }
  (pullbackProjection_targetFiberFunctor u p V).mapIso eFiber ≪≫
    pullbackProjection_targetFiberCounitIso u p R

end

end CategoryTheory
