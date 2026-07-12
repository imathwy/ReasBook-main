import StacksProject_2024.Chap08.Lemma_8_8_3.LiftBasedFunctor.Vertical.Functoriality

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: a triple common cover for comparing two consecutive
vertical arrows and their composite. -/
noncomputable def stackificationLiftVerticalTripleCommonCover
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y₀ y₁ y₂ : S'.p.Fiber U) :
    J.Cover U :=
  (stackificationLiftObjectCover (J := J) G hG y₀ ⊓
    stackificationLiftObjectCover (J := J) G hG y₁) ⊓
      stackificationLiftObjectCover (J := J) G hG y₂

/-- Helper for Chap08 Lemma 8 8 3: the `(y₀,y₁)` projection of the triple vertical cover. -/
noncomputable def stackificationLiftVerticalTripleCommonCover_01
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y₀ y₁ y₂ : S'.p.Fiber U)
    (I : (stackificationLiftVerticalTripleCommonCover (J := J) G hG y₀ y₁ y₂).Arrow) :
    (stackificationLiftVerticalCommonCover (J := J) G hG y₀ y₁).Arrow :=
  ⟨I.Y, I.f, by
    dsimp [stackificationLiftVerticalCommonCover,
      stackificationLiftVerticalTripleCommonCover] at I ⊢
    exact ⟨I.hf.1.1, I.hf.1.2⟩⟩

/-- Helper for Chap08 Lemma 8 8 3: the `(y₀,y₂)` projection of the triple vertical cover. -/
noncomputable def stackificationLiftVerticalTripleCommonCover_02
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y₀ y₁ y₂ : S'.p.Fiber U)
    (I : (stackificationLiftVerticalTripleCommonCover (J := J) G hG y₀ y₁ y₂).Arrow) :
    (stackificationLiftVerticalCommonCover (J := J) G hG y₀ y₂).Arrow :=
  ⟨I.Y, I.f, by
    dsimp [stackificationLiftVerticalCommonCover,
      stackificationLiftVerticalTripleCommonCover] at I ⊢
    exact ⟨I.hf.1.1, I.hf.2⟩⟩

/-- Helper for Chap08 Lemma 8 8 3: the `(y₁,y₂)` projection of the triple vertical cover. -/
noncomputable def stackificationLiftVerticalTripleCommonCover_12
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    {U : C} (y₀ y₁ y₂ : S'.p.Fiber U)
    (I : (stackificationLiftVerticalTripleCommonCover (J := J) G hG y₀ y₁ y₂).Arrow) :
    (stackificationLiftVerticalCommonCover (J := J) G hG y₁ y₂).Arrow :=
  ⟨I.Y, I.f, by
    dsimp [stackificationLiftVerticalCommonCover,
      stackificationLiftVerticalTripleCommonCover] at I ⊢
    exact ⟨I.hf.1.2, I.hf.2⟩⟩

/-- Helper for Chap08 Lemma 8 8 3: on the triple common cover, the local vertical formula
respects composition. -/
theorem stackificationLiftVerticalLocalMap_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y₀ y₁ y₂ : S'.p.Fiber U}
    (d₁ : y₀ ⟶ y₁) (d₂ : y₁ ⟶ y₂)
    (I : (stackificationLiftVerticalTripleCommonCover (J := J) G hG y₀ y₁ y₂).Arrow) :
    stackificationLiftVerticalLocalMap X G hG F d₁
        (stackificationLiftVerticalTripleCommonCover_01 (J := J) G hG y₀ y₁ y₂ I) ≫
      stackificationLiftVerticalLocalMap X G hG F d₂
        (stackificationLiftVerticalTripleCommonCover_12 (J := J) G hG y₀ y₁ y₂ I) =
      stackificationLiftVerticalLocalMap X G hG F (d₁ ≫ d₂)
        (stackificationLiftVerticalTripleCommonCover_02 (J := J) G hG y₀ y₁ y₂ I) := by
  simp only [stackificationLiftVerticalLocalMap]
  dsimp [stackificationLiftVerticalTripleCommonCover_01,
    stackificationLiftVerticalTripleCommonCover_02,
    stackificationLiftVerticalTripleCommonCover_12,
    stackificationLiftVerticalCommonCover_left,
    stackificationLiftVerticalCommonCover_right, GrothendieckTopology.Cover.Arrow.map]
  let I0 : (stackificationLiftObjectCover (J := J) G hG y₀).Arrow :=
    ⟨I.Y, I.f, by
      dsimp [stackificationLiftVerticalTripleCommonCover] at I
      exact I.hf.1.1⟩
  let I1 : (stackificationLiftObjectCover (J := J) G hG y₁).Arrow :=
    ⟨I.Y, I.f, by
      dsimp [stackificationLiftVerticalTripleCommonCover] at I
      exact I.hf.1.2⟩
  let I2 : (stackificationLiftObjectCover (J := J) G hG y₂).Arrow :=
    ⟨I.Y, I.f, by
      dsimp [stackificationLiftVerticalTripleCommonCover] at I
      exact I.hf.2⟩
  change
    ((stackificationLiftObjectGluedLocalIso X G hG F y₀ I0).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
            (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
            ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₁ ≫
                (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv) ≫
          (stackificationLiftObjectGluedLocalIso X G hG F y₁ I1).inv) ≫
        ((stackificationLiftObjectGluedLocalIso X G hG F y₁ I1).hom ≫
          stackificationLiftHomExtensionFiberMap X G hG F
            (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
            (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
            ((stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom ≫
              ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₂ ≫
                (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv) ≫
          (stackificationLiftObjectGluedLocalIso X G hG F y₂ I2).inv) =
      (stackificationLiftObjectGluedLocalIso X G hG F y₀ I0).hom ≫
        stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
          (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
          ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (d₁ ≫ d₂) ≫
              (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv) ≫
        (stackificationLiftObjectGluedLocalIso X G hG F y₂ I2).inv
  conv_lhs =>
    rw [← Category.assoc
      (stackificationLiftObjectGluedLocalIso X G hG F y₀ I0).hom
      (stackificationLiftHomExtensionFiberMap X G hG F
        (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
        (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
        ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
          ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₁ ≫
            (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv))
      (stackificationLiftObjectGluedLocalIso X G hG F y₁ I1).inv]
  rw [Category.assoc]
  rw [reassoc_of% (stackificationLiftObjectGluedLocalIso X G hG F y₁ I1).inv_hom_id]
  simp only [Category.assoc]
  have hE :
      stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
          (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
          ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₁ ≫
              (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv) ≫
        stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
          (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
          ((stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₂ ≫
              (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv) =
        stackificationLiftHomExtensionFiberMap X G hG F
          (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
          (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
          ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
            ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (d₁ ≫ d₂) ≫
              (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv) := by
    rw [← stackificationLiftHomExtensionFiberMap_comp X G hG F]
    congr 1
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    let a := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₁
    let b := ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₂
    let c := (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv
    have hcancel := (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv_hom_id
    change a ≫ (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv ≫
        (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom ≫ b ≫ c =
      (a ≫ b) ≫ c
    calc
      a ≫ (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv ≫
          (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom ≫ b ≫ c =
        a ≫ ((stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv ≫
          (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom) ≫ b ≫ c := by
          simp [Category.assoc]
      _ = a ≫ 𝟙 (I1.f ^*[canonicalPullbackChoice S'.p] y₁) ≫ b ≫ c := by
          exact congrArg (fun t => a ≫ t ≫ b ≫ c) hcancel
      _ = (a ≫ b) ≫ c := by
          change a ≫
              𝟙 (((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.obj y₁) ≫
              b ≫ c = (a ≫ b) ≫ c
          simp [Category.assoc]
  let E1 :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
      (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
      ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₁ ≫
          (stackificationLiftObjectModel (J := J) G hG y₁ I1).2.inv)
  let E2 :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y₁ I1).1
      (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
      ((stackificationLiftObjectModel (J := J) G hG y₁ I1).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map d₂ ≫
          (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv)
  let E02 :=
    stackificationLiftHomExtensionFiberMap X G hG F
      (stackificationLiftObjectModel (J := J) G hG y₀ I0).1
      (stackificationLiftObjectModel (J := J) G hG y₂ I2).1
      ((stackificationLiftObjectModel (J := J) G hG y₀ I0).2.hom ≫
        ((canonicalFiberPseudofunctor S'.p).map I.f.op.toLoc).toFunctor.map (d₁ ≫ d₂) ≫
          (stackificationLiftObjectModel (J := J) G hG y₂ I2).2.inv)
  let L0 := (stackificationLiftObjectGluedLocalIso X G hG F y₀ I0).hom
  let K2 := (stackificationLiftObjectGluedLocalIso X G hG F y₂ I2).inv
  change L0 ≫ E1 ≫ E2 ≫ K2 = L0 ≫ E02 ≫ K2
  calc
    L0 ≫ E1 ≫ E2 ≫ K2 = L0 ≫ (E1 ≫ E2) ≫ K2 := by
      simp [Category.assoc]
    _ = L0 ≫ E02 ≫ K2 := by
      exact congrArg (fun e => L0 ≫ e ≫ K2) hE

/-- Helper for Chap08 Lemma 8 8 3: the glued vertical map respects composition. -/
theorem stackificationLiftVerticalMap_comp
    (X : StackOver J)
    (G : S ⟶ S') (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X)
    {U : C} {y₀ y₁ y₂ : S'.p.Fiber U}
    (d₁ : y₀ ⟶ y₁) (d₂ : y₁ ⟶ y₂) :
    stackificationLiftVerticalMap X G hG F (d₁ ≫ d₂) =
      stackificationLiftVerticalMap X G hG F d₁ ≫
        stackificationLiftVerticalMap X G hG F d₂ := by
  apply stack_cover_hom_ext (J := J) X
    (stackificationLiftVerticalTripleCommonCover (J := J) G hG y₀ y₁ y₂)
  intro I
  let M := ((canonicalFiberPseudofunctor X.p).map I.f.op.toLoc).toFunctor
  let I01 := stackificationLiftVerticalTripleCommonCover_01 (J := J) G hG y₀ y₁ y₂ I
  let I02 := stackificationLiftVerticalTripleCommonCover_02 (J := J) G hG y₀ y₁ y₂ I
  let I12 := stackificationLiftVerticalTripleCommonCover_12 (J := J) G hG y₀ y₁ y₂ I
  change M.map (stackificationLiftVerticalMap X G hG F (d₁ ≫ d₂)) =
    M.map (stackificationLiftVerticalMap X G hG F d₁ ≫
      stackificationLiftVerticalMap X G hG F d₂)
  rw [M.map_comp]
  change
    ((canonicalFiberPseudofunctor X.p).map I02.f.op.toLoc).toFunctor.map
        (stackificationLiftVerticalMap X G hG F (d₁ ≫ d₂)) =
      ((canonicalFiberPseudofunctor X.p).map I01.f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d₁) ≫
        ((canonicalFiberPseudofunctor X.p).map I12.f.op.toLoc).toFunctor.map
          (stackificationLiftVerticalMap X G hG F d₂)
  rw [stackificationLiftVerticalMap_local X G hG F (d₁ ≫ d₂) I02]
  rw [stackificationLiftVerticalMap_local X G hG F d₁ I01]
  rw [stackificationLiftVerticalMap_local X G hG F d₂ I12]
  exact (stackificationLiftVerticalLocalMap_comp X G hG F d₁ d₂ I).symm

end

end CategoryTheory
