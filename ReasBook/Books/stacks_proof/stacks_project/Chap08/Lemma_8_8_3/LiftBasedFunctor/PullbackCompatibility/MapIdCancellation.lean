import StacksProject_2024.Chap08.Lemma_8_8_3.Prelude

universe u v u' v'

namespace CategoryTheory

open Opposite

namespace Pseudofunctor

/-- Helper for Chap08 Lemma 8 8 3: the identity comparison of a pseudofunctor cancels around
the image of a morphism by the identity map. -/
theorem mapId_inv_map_hom_hom
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) :
    (F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app A ≫
        (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
          (F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app B =
      e := by
  let idIso := F.mapId (LocallyDiscrete.mk (op U))
  change idIso.inv.toNatTrans.app A ≫
      (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        idIso.hom.toNatTrans.app B =
    e
  rw [← (idIso.inv.toNatTrans.naturality_assoc e
    (idIso.hom.toNatTrans.app B))]
  have hpair :
      idIso.inv.toNatTrans.app B ≫ idIso.hom.toNatTrans.app B =
        𝟙 _ := by
    exact Cat.Hom.inv_hom_id_toNatTrans_app idIso B
  calc
    e ≫ idIso.inv.toNatTrans.app B ≫ idIso.hom.toNatTrans.app B =
        e ≫ (idIso.inv.toNatTrans.app B ≫ idIso.hom.toNatTrans.app B) := by
      rfl
    _ = e ≫ 𝟙 _ := by
      exact congrArg (fun t => e ≫ t) hpair
    _ = e := by
      simp only [Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 3: the identity comparison of a pseudofunctor also converts
an ordinary morphism into its image under the identity map. -/
theorem mapId_hom_comp_inv
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) :
    (F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app A ≫ e ≫
        (F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app B =
      (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e := by
  let idIso := F.mapId (LocallyDiscrete.mk (op U))
  have hnat := idIso.hom.toNatTrans.naturality e
  have hnat' :
      (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
          idIso.hom.toNatTrans.app B =
        idIso.hom.toNatTrans.app A ≫ e := by
    simpa only [Functor.id_map] using hnat
  change idIso.hom.toNatTrans.app A ≫ e ≫ idIso.inv.toNatTrans.app B =
    (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e
  calc
    idIso.hom.toNatTrans.app A ≫ e ≫ idIso.inv.toNatTrans.app B =
        (idIso.hom.toNatTrans.app A ≫ e) ≫ idIso.inv.toNatTrans.app B := by
      exact (Category.assoc _ _ _).symm
    _ =
        ((F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
          idIso.hom.toNatTrans.app B) ≫ idIso.inv.toNatTrans.app B := by
      exact congrArg (fun t => t ≫ idIso.inv.toNatTrans.app B) hnat'.symm
    _ = (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
          (idIso.hom.toNatTrans.app B ≫ idIso.inv.toNatTrans.app B) := by
      simp only [Category.assoc]
    _ = (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫ 𝟙 _ := by
      exact congrArg
        (fun t => (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫ t)
        (Cat.Hom.hom_inv_id_toNatTrans_app idIso B)
    _ = (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e := by
      simp only [Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 3: a composition comparison cancels around the iterated
image of a morphism. -/
theorem mapComp_hom_map_inv
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {A B : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) :
    (F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        (F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).inv.toNatTrans.app B =
      (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e := by
  let κ := F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl
  have hnat := κ.hom.toNatTrans.naturality e
  have hnat' :
      (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫
          κ.hom.toNatTrans.app B =
        κ.hom.toNatTrans.app A ≫
          ((F.map g.op.toLoc).toFunctor.map
            ((F.map f.op.toLoc).toFunctor.map e)) := by
    simpa only [Cat.Hom.comp_toFunctor, Functor.comp_map] using hnat
  change κ.hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        κ.inv.toNatTrans.app B =
      (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e
  calc
    κ.hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        κ.inv.toNatTrans.app B =
      (κ.hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e))) ≫
        κ.inv.toNatTrans.app B := by
        exact (Category.assoc _ _ _).symm
    _ = ((F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫
          κ.hom.toNatTrans.app B) ≫
        κ.inv.toNatTrans.app B := by
        exact congrArg (fun t => t ≫ κ.inv.toNatTrans.app B) hnat'.symm
    _ = (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫
          (κ.hom.toNatTrans.app B ≫ κ.inv.toNatTrans.app B) := by
        simp only [Category.assoc]
    _ = (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫ 𝟙 _ := by
        exact congrArg
          (fun t => (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫ t)
          (Cat.Hom.hom_inv_id_toNatTrans_app κ B)
    _ = (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e := by
        simp only [Category.comp_id]

/-- Helper for Chap08 Lemma 8 8 3: a composition comparison cancels around an iterated
image, with an arbitrary right tail. -/
theorem mapComp_hom_map_inv_assoc
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    {A B : F.obj (LocallyDiscrete.mk (op U))}
    {T : F.obj (LocallyDiscrete.mk (op W))}
    (e : A ⟶ B)
    (k : (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.obj B ⟶ T) :
    (F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        ((F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).inv.toNatTrans.app B ≫
          k) =
      (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫ k := by
  calc
    (F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        ((F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).inv.toNatTrans.app B ≫
          k) =
      ((F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).hom.toNatTrans.app A ≫
        ((F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map e)) ≫
        (F.mapComp' f.op.toLoc g.op.toLoc (f.op.toLoc ≫ g.op.toLoc) rfl).inv.toNatTrans.app B) ≫
          k := by
        simp only [Category.assoc]
    _ = (F.map (f.op.toLoc ≫ g.op.toLoc)).toFunctor.map e ≫ k := by
        exact congrArg (fun t => t ≫ k) (mapComp_hom_map_inv F f g e)

/-- Helper for Chap08 Lemma 8 8 3: move an identity comparison past a mapped morphism on the
left, in the right-associated shape produced by descent-data components. -/
theorem mapId_map_hom_assoc
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B W : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) (k : B ⟶ W) :
    (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        ((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app B ≫ k) =
      (F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app A ≫ (e ≫ k) := by
  let idIso := F.mapId (LocallyDiscrete.mk (op U))
  have hnat :
      (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
          idIso.hom.toNatTrans.app B =
        idIso.hom.toNatTrans.app A ≫ e := by
    simpa only [Functor.id_map] using idIso.hom.toNatTrans.naturality e
  calc
    (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        (idIso.hom.toNatTrans.app B ≫ k) =
      ((F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        idIso.hom.toNatTrans.app B) ≫ k := by
        exact (Category.assoc _ _ _).symm
    _ = (idIso.hom.toNatTrans.app A ≫ e) ≫ k := by
        exact congrArg (fun t => t ≫ k) hnat
    _ = idIso.hom.toNatTrans.app A ≫ (e ≫ k) := by
        exact Category.assoc _ _ _

/-- Helper for Chap08 Lemma 8 8 3: a two-tail version of
`Pseudofunctor.mapId_map_hom_assoc`, matching expressions where an `eqToHom` cast has already
been grouped with the identity comparison. -/
theorem mapId_map_hom_assoc₂
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B W Z : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) (k : B ⟶ W) (l : W ⟶ Z) :
    (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        (((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app B ≫ k) ≫ l) =
      ((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app A ≫ (e ≫ k)) ≫ l := by
  rw [← Category.assoc]
  rw [mapId_map_hom_assoc F U e k]

/-- Helper for Chap08 Lemma 8 8 3: a three-tail version of
`Pseudofunctor.mapId_map_hom_assoc`, matching fully left-associated descent-data components. -/
theorem mapId_map_hom_assoc₃
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B W Z T : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) (k : B ⟶ W) (l : W ⟶ Z) (m : Z ⟶ T) :
    (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e ≫
        ((((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app B ≫ k) ≫ l) ≫ m) =
      (((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app A ≫ (e ≫ k)) ≫ l) ≫ m := by
  rw [← Category.assoc]
  rw [mapId_map_hom_assoc₂ F U e k l]

/-- Helper for Chap08 Lemma 8 8 3: move an inverse identity comparison past a mapped morphism on
the right, in the right-associated shape produced by descent-data components. -/
theorem mapId_inv_map_assoc
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B W : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) (k : W ⟶ A) :
    k ≫ ((F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app A ≫
        (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e) =
      (k ≫ e) ≫ (F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app B := by
  let idIso := F.mapId (LocallyDiscrete.mk (op U))
  have hnat :
      idIso.inv.toNatTrans.app A ≫
          (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e =
        e ≫ idIso.inv.toNatTrans.app B := by
    simpa only [Functor.id_map] using (idIso.inv.toNatTrans.naturality e).symm
  calc
    k ≫ (idIso.inv.toNatTrans.app A ≫
        (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e) =
      k ≫ (e ≫ idIso.inv.toNatTrans.app B) := by
        exact congrArg (fun t => k ≫ t) hnat
    _ = (k ≫ e) ≫ idIso.inv.toNatTrans.app B := by
        exact (Category.assoc _ _ _).symm

/-- Helper for Chap08 Lemma 8 8 3: a left-associated version of
`Pseudofunctor.mapId_inv_map_assoc`. -/
theorem mapId_inv_map_assoc₂
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    (U : C)
    {A B W : F.obj (LocallyDiscrete.mk (op U))}
    (e : A ⟶ B) (k : W ⟶ A) :
    (k ≫ (F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app A) ≫
        (F.map (𝟙 (LocallyDiscrete.mk (op U)))).toFunctor.map e =
      (k ≫ e) ≫ (F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app B := by
  rw [Category.assoc]
  exact mapId_inv_map_assoc F U e k

end Pseudofunctor

end CategoryTheory
