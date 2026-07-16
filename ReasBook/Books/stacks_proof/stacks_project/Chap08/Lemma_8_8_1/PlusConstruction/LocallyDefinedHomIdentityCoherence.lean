import stacks_proof.stacks_project.Chap04.CanonicalFiberPseudofunctor

universe u v uX vX

namespace CategoryTheory

open Bicategory
open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor

/-- Owner-normalization helper for `mapComp'`: if the displayed composite target is replaced by
an equal morphism, the comparison isomorphisms are heterogeneously equal. -/
theorem mapComp'_heq_of_eq
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}
    {U V W : LocallyDiscrete Cᵒᵖ} {f : U ⟶ V} {g : V ⟶ W}
    {k k' : U ⟶ W} (hk : k = k')
    (h : f ≫ g = k) (h' : f ≫ g = k') :
    HEq (F.mapComp' f g k h) (F.mapComp' f g k' h') := by
  subst hk
  have hw : h = h' := Subsingleton.elim _ _
  cases hw
  rfl

/-- Objectwise homogeneous version of `mapComp'_heq_of_eq` for the hom component. -/
theorem mapComp'_hom_app_heq_of_eq
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}
    {U V W : LocallyDiscrete Cᵒᵖ} {f : U ⟶ V} {g : V ⟶ W}
    {k k' : U ⟶ W} (hk : k = k')
    (h : f ≫ g = k) (h' : f ≫ g = k')
    (x : F.obj U) :
    HEq ((F.mapComp' f g k h).hom.toNatTrans.app x)
      ((F.mapComp' f g k' h').hom.toNatTrans.app x) := by
  subst hk
  have hw : h = h' := Subsingleton.elim _ _
  cases hw
  rfl

/-- Objectwise homogeneous version of `mapComp'_heq_of_eq` for the inverse component. -/
theorem mapComp'_inv_app_heq_of_eq
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}
    {U V W : LocallyDiscrete Cᵒᵖ} {f : U ⟶ V} {g : V ⟶ W}
    {k k' : U ⟶ W} (hk : k = k')
    (h : f ≫ g = k) (h' : f ≫ g = k')
    (x : F.obj U) :
    HEq ((F.mapComp' f g k h).inv.toNatTrans.app x)
      ((F.mapComp' f g k' h').inv.toNatTrans.app x) := by
  subst hk
  have hw : h = h' := Subsingleton.elim _ _
  cases hw
  rfl

/-- Objectwise postmapped version of `mapComp'_heq_of_eq` for the inverse component. -/
theorem map_mapComp'_inv_app_heq_of_eq
    {C : Type u} [Category.{v} C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX}}
    {U V W T : LocallyDiscrete Cᵒᵖ} {f : U ⟶ V} {g : V ⟶ W}
    {k k' : U ⟶ W} (r : W ⟶ T) (hk : k = k')
    (h : f ≫ g = k) (h' : f ≫ g = k')
    (x : F.obj U) :
    HEq
      ((F.map r).toFunctor.map ((F.mapComp' f g k h).inv.toNatTrans.app x))
      ((F.map r).toFunctor.map ((F.mapComp' f g k' h').inv.toNatTrans.app x)) := by
  subst hk
  have hw : h = h' := Subsingleton.elim _ _
  cases hw
  rfl

/-- For a pseudofunctor on the locally-discrete opposite, the inverse comparison for
`id_V` followed by `f` is heterogeneously the image of the identity comparison hom. -/
theorem mapComp_id_inv_app_heq_map_mapId_hom
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
    {U V : C} (f : U ⟶ V)
    (z : F.obj (LocallyDiscrete.mk (op V))) :
    HEq
      ((F.mapComp (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc).inv.toNatTrans.app z)
      ((F.map f.op.toLoc).toFunctor.map
        ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z)) := by
  have h0 := Pseudofunctor.mapComp'_eq_mapComp
    (F := F) (f := 𝟙 (LocallyDiscrete.mk (op V))) (g := f.op.toLoc)
  rw [← h0]
  have h1 :
      HEq
        ((F.mapComp' (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
            ((𝟙 (LocallyDiscrete.mk (op V))) ≫ f.op.toLoc) rfl).inv.toNatTrans.app z)
        ((F.mapComp' (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
            f.op.toLoc (by simp)).inv.toNatTrans.app z) := by
    exact Pseudofunctor.mapComp'_inv_app_heq_of_eq
      (F := F)
      (U := LocallyDiscrete.mk (op V))
      (V := LocallyDiscrete.mk (op V))
      (W := LocallyDiscrete.mk (op U))
      (f := 𝟙 (LocallyDiscrete.mk (op V)))
      (g := f.op.toLoc)
      (k := (𝟙 (LocallyDiscrete.mk (op V))) ≫ f.op.toLoc)
      (k' := f.op.toLoc)
      (hk := by simp)
      (h := rfl)
      (h' := by simp)
      z
  refine HEq.trans h1 ?_
  exact heq_of_eq (by
    simpa [op_id, Quiver.Hom.id_toLoc] using
      (Pseudofunctor.mapComp'_id_comp_inv_app
        (F := F) (f := f.op.toLoc) z))

/-- Stage 2 identity-coherence helper: the identity comparison of a pseudofunctor cancels around
the image of a morphism by the identity map.  This is the generic form needed when the local
identity representative is restricted to a cover member. -/
theorem mapId_inv_map_hom_hom_core
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
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

/-- Stage 2 identity-coherence helper: the dual cancellation converting a morphism conjugated by
the identity comparison into its image under the identity map. -/
theorem mapId_hom_comp_inv_core
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
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

/-- Stage 2 right-identity coherence helper: after restricting the literal identity
representative on the target side to a cover member, the two `f,q` comparison maps conjugate it
to the image of `mapId`, and the remaining `mapComp id f` owner is removed by heterogeneous
transport. -/
theorem mapComp_rightIdentityTail_heq
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
    {U V W : C} (f : U ⟶ V) (q : W ⟶ U)
    (z : F.obj (LocallyDiscrete.mk (op V)))
    {A : F.obj (LocallyDiscrete.mk (op W))}
    (e : A ⟶ (F.map q.op.toLoc).toFunctor.obj
      ((F.map f.op.toLoc).toFunctor.obj z)) :
    HEq
      (e ≫
        ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z) ≫
        (F.map (q ≫ f).op.toLoc).toFunctor.map
          ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
        ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
          ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z)) ≫
        (F.map q.op.toLoc).toFunctor.map
          ((F.mapComp (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc).inv.toNatTrans.app z))
      e := by
  have hnat1 :
      ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z) ≫
          (F.map (q ≫ f).op.toLoc).toFunctor.map
            ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
          ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
            ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z)) =
        (F.map q.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map
            ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z)) := by
    simpa [Category.assoc, Cat.Hom.id_toFunctor, Functor.id_obj] using
      (Pseudofunctor.mapComp'_naturality_1
        (F := F)
        (f := f.op.toLoc)
        (g := q.op.toLoc)
        (fg := (q ≫ f).op.toLoc)
        (hfg := by rfl)
        ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z))
  have hright :
      HEq
        ((F.map q.op.toLoc).toFunctor.map
            ((F.mapComp (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc).inv.toNatTrans.app z))
        ((F.map q.op.toLoc).toFunctor.map
            ((F.map f.op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z))) := by
    have h0 := Pseudofunctor.mapComp'_eq_mapComp
      (F := F) (f := 𝟙 (LocallyDiscrete.mk (op V))) (g := f.op.toLoc)
    rw [← h0]
    have h1 :
        HEq
          ((F.map q.op.toLoc).toFunctor.map
            ((F.mapComp' (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
              ((𝟙 (LocallyDiscrete.mk (op V))) ≫ f.op.toLoc) rfl).inv.toNatTrans.app z))
          ((F.map q.op.toLoc).toFunctor.map
            ((F.mapComp' (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc
              f.op.toLoc (by simp)).inv.toNatTrans.app z)) := by
      exact Pseudofunctor.map_mapComp'_inv_app_heq_of_eq
        (F := F)
        (r := q.op.toLoc)
        (hk := by simp)
        (h := rfl)
        (h' := by simp)
        z
    refine HEq.trans h1 ?_
    exact heq_of_eq (by
      exact congrArg (fun t => (F.map q.op.toLoc).toFunctor.map t) (by
        simpa [op_id, Quiver.Hom.id_toLoc] using
          (Pseudofunctor.mapComp'_id_comp_inv_app
            (F := F) (f := f.op.toLoc) z)))
  have hmul :
      HEq
        (((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z) ≫
            (F.map (q ≫ f).op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
            ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
              ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z)) ≫
            (F.map q.op.toLoc).toFunctor.map
              ((F.map f.op.toLoc).toFunctor.map
                ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z)))
        (𝟙 (((F.map q.op.toLoc).toFunctor.obj
          ((F.map f.op.toLoc).toFunctor.obj z)))) := by
    apply heq_of_eq
    calc
      (((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z) ≫
          (F.map (q ≫ f).op.toLoc).toFunctor.map
            ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
          ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
            ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z)) ≫
          (F.map q.op.toLoc).toFunctor.map
            ((F.map f.op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z)))
          =
        (F.map q.op.toLoc).toFunctor.map
            ((F.map f.op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z)) ≫
          (F.map q.op.toLoc).toFunctor.map
            ((F.map f.op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z)) := by
          simpa [Category.assoc] using
            congrArg
              (fun t => t ≫
                (F.map q.op.toLoc).toFunctor.map
                  ((F.map f.op.toLoc).toFunctor.map
                    ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z)))
              hnat1
      _ =
        (F.map q.op.toLoc).toFunctor.map
          (((F.map f.op.toLoc).toFunctor.map
            ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z)) ≫
            ((F.map f.op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z))) := by
          rw [← Functor.map_comp]
      _ =
        (F.map q.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map
            (((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
              ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z))) := by
          rw [← (F.map f.op.toLoc).toFunctor.map_comp]
      _ = 𝟙 _ := by
          rw [Cat.Hom.inv_hom_id_toNatTrans_app]
          simp
  have htail :
      HEq
        (((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z) ≫
            (F.map (q ≫ f).op.toLoc).toFunctor.map
              ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z) ≫
            ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
              ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z)) ≫
            (F.map q.op.toLoc).toFunctor.map
              ((F.mapComp (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc).inv.toNatTrans.app z))
        (𝟙 (((F.map q.op.toLoc).toFunctor.obj
          ((F.map f.op.toLoc).toFunctor.obj z)))) := by
    refine HEq.trans ?_ hmul
    let A0 :=
      ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).inv.toNatTrans.app z)
    let B0 :=
      (F.map (q ≫ f).op.toLoc).toFunctor.map
        ((F.mapId (LocallyDiscrete.mk (op V))).inv.toNatTrans.app z)
    let C0 :=
      ((F.mapComp' f.op.toLoc q.op.toLoc ((q ≫ f).op.toLoc) (by rfl)).hom.toNatTrans.app
        ((F.map (𝟙 (LocallyDiscrete.mk (op V)))).toFunctor.obj z))
    let D0 :=
      (F.map q.op.toLoc).toFunctor.map
        ((F.mapComp (𝟙 (LocallyDiscrete.mk (op V))) f.op.toLoc).inv.toNatTrans.app z)
    let D1 :=
      (F.map q.op.toLoc).toFunctor.map
        ((F.map f.op.toLoc).toFunctor.map
          ((F.mapId (LocallyDiscrete.mk (op V))).hom.toNatTrans.app z))
    have hreplace : HEq (((A0 ≫ B0) ≫ C0) ≫ D0) (((A0 ≫ B0) ≫ C0) ≫ D1) := by
      exact heq_comp (by simp) (by simp) (by simp) (heq_of_eq rfl) hright
    simpa [A0, B0, C0, D0, D1, Category.assoc] using hreplace
  refine HEq.trans ?_ (heq_of_eq (Category.comp_id e))
  refine heq_comp (by simp) (by simp) (by simp) (heq_of_eq rfl) htail

end Pseudofunctor

/-- Stage 2 identity-coherence helper: the identity-slice Hom equivalence is the action of the
canonical pseudofunctor on the identity base morphism. -/
theorem canonicalFiberPseudofunctor_presheafHomObjHomEquiv_eq_map_id_core
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    {U : C} {M N : p.Fiber U} (φ : M ⟶ N) :
    (canonicalFiberPseudofunctor p).presheafHomObjHomEquiv φ =
      ((canonicalFiberPseudofunctor p).map (𝟙 U).op.toLoc).toFunctor.map φ := by
  rw [Pseudofunctor.presheafHomObjHomEquiv_apply]
  simpa only [op_id, Quiver.Hom.id_toLoc, Category.assoc] using
    (Pseudofunctor.mapId_hom_comp_inv_core
      (F := canonicalFiberPseudofunctor p) U φ)

/-- Stage 2 identity-coherence helper: normalize an identity base arrow in the locally-discrete
opposite category. -/
theorem op_toLoc_id_core
    {C : Type u} [Category.{v} C] {U : C} :
    (𝟙 U).op.toLoc = 𝟙 (LocallyDiscrete.mk (op U)) :=
  rfl

/-- Stage 2 identity-coherence helper: normalize a base arrow with a leading identity before
turning it into a locally-discrete arrow. -/
theorem op_toLoc_id_comp_core
    {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) :
    (𝟙 V ≫ f).op.toLoc = f.op.toLoc := by
  rw [Category.id_comp]

/-- Stage 2 identity-coherence helper: normalize composition with the identity in the
locally-discrete opposite category. -/
theorem toLoc_comp_id_core
    {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) :
    f.op.toLoc ≫ (𝟙 V).op.toLoc = f.op.toLoc := by
  rw [← Quiver.Hom.comp_toLoc, ← op_comp, Category.id_comp]

/-- Stage 2 identity-coherence helper for the canonical fiber pseudofunctor: the hom component
of the pseudofunctor identity comparison is the chosen cartesian arrow for the identity pullback. -/
theorem canonicalFiberPseudofunctor_mapId_hom_app_eq_identityCart_core
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    (U : C) (z : p.Fiber U) :
    ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app z =
      (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
        exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z) := by
  apply Functor.Fiber.hom_ext
  simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor,
    PullbackChoice.pullbackIdIso] using
    (canonicalPullbackChoice p).pullbackIdComponentIso_inv_eq U z

/-- Stage 2 identity-coherence helper for the canonical fiber pseudofunctor: the inverse
comparison for `f` followed by an identity is the chosen identity-pullback cartesian arrow,
followed by the explicit transport from `f^*` to `(id ≫ f)^*`.  The transport is part of the
source-faithful bookkeeping and should not be erased by pretending the two owners are
definitionally equal. -/
theorem canonicalFiberPseudofunctor_mapComp_comp_id_inv_app_eq_identityCart_comp_transport_core
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : U ⟶ V) (z : p.Fiber V) :
    let Fp := canonicalFiberPseudofunctor p
    let zU := (Fp.map f.op.toLoc).toFunctor.obj z
    let cart : (𝟙 U) ^*[canonicalPullbackChoice p] zU ⟶ zU :=
      ⟨(canonicalPullbackChoice p).map (𝟙 U) zU, by
        exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) zU).toIsHomLift⟩
    let hbase : f = 𝟙 U ≫ f := (Category.id_comp f).symm
    let targetTransport :
        zU ⟶ (𝟙 U ≫ f) ^*[canonicalPullbackChoice p] z :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice p).pullbackFunctor k) hbase)).app z
    ((Fp.mapComp f.op.toLoc (𝟙 (LocallyDiscrete.mk (op U)))).inv.toNatTrans.app z) =
      cart ≫ targetTransport := by
  intro Fp zU cart hbase targetTransport
  apply Functor.Fiber.hom_ext
  let hc := canonicalPullbackChoice p
  let psi := ((hc.pullbackCompComponentIso f (𝟙 U) z).inv).1
  let psiR := (Functor.Fiber.fiberInclusion.map (cart ≫ targetTransport))
  change psi = psiR
  refine @Functor.IsStronglyCartesian.ext C T _ _ p _ _ _ _ (𝟙 U ≫ f)
    (hc.map (𝟙 U ≫ f) z) (hc.isStronglyCartesian (𝟙 U ≫ f) z)
    _ _ (𝟙 U) psi psiR ?_ ?_ ?_
  · dsimp [psi]
    exact ((hc.pullbackCompComponentIso f (𝟙 U) z).inv).2
  · dsimp [psiR]
    exact (cart ≫ targetTransport).2
  · dsimp [psi, psiR, cart, targetTransport, hbase, hc, zU, Fp,
      canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor]
    have htransport :
        (Functor.Fiber.fiberInclusion.map targetTransport) ≫
          (canonicalPullbackChoice p).map (𝟙 U ≫ f) z =
        (canonicalPullbackChoice p).map f z := by
      have haux {g : U ⟶ V} (e : f = g) :
          (Functor.Fiber.fiberInclusion.map ((eqToHom (congrArg
            (fun k => (canonicalPullbackChoice p).pullbackFunctor k) e)).app z)) ≫
            (canonicalPullbackChoice p).map g z =
          (canonicalPullbackChoice p).map f z := by
        cases e
        simp
      exact haux hbase
    calc
      ((canonicalPullbackChoice p).pullbackCompComponentIso f (𝟙 U) z).inv.1 ≫
          (canonicalPullbackChoice p).map (𝟙 U ≫ f) z
          = (canonicalPullbackChoice p).map (𝟙 U) (f ^*[canonicalPullbackChoice p] z) ≫
              (canonicalPullbackChoice p).map f z := by
            simpa using
              (canonicalPullbackChoice p).pullbackCompComponentIso_inv_fac f (𝟙 U) z
      _ = (canonicalPullbackChoice p).map (𝟙 U) (f ^*[canonicalPullbackChoice p] z) ≫
            (Functor.Fiber.fiberInclusion.map targetTransport ≫
              (canonicalPullbackChoice p).map (𝟙 U ≫ f) z) := by
            exact congrArg
              (fun k => (canonicalPullbackChoice p).map (𝟙 U)
                (f ^*[canonicalPullbackChoice p] z) ≫ k)
              htransport.symm
      _ = (Functor.Fiber.fiberInclusion.map (cart ≫ targetTransport)) ≫
            (canonicalPullbackChoice p).map (𝟙 U ≫ f) z := by
            rw [Functor.map_comp]
            change (canonicalPullbackChoice p).map (𝟙 U)
                (f ^*[canonicalPullbackChoice p] z) ≫
                targetTransport.1 ≫ (canonicalPullbackChoice p).map (𝟙 U ≫ f) z =
              ((canonicalPullbackChoice p).map (𝟙 U)
                (f ^*[canonicalPullbackChoice p] z) ≫ targetTransport.1) ≫
                (canonicalPullbackChoice p).map (𝟙 U ≫ f) z
            simp [Category.assoc]

namespace Pseudofunctor

/-- Stage 2 identity-coherence helper: after restricting the literal identity representative to
a cover member, the resulting `mapId.inv` term cancels the inverse composition comparison for
`id ≫ f`.  This is the first half of the source left-unit calculation. -/
theorem map_mapId_inv_comp_mapComp_id_inv_core
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vX, uX})
    {U V : C} (f : V ⟶ U)
    (M : F.obj (LocallyDiscrete.mk (op U))) :
    ((F.map f.op.toLoc).toFunctor.map
        ((F.mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app M)) ≫
      (F.mapComp' (𝟙 U).op.toLoc f.op.toLoc f.op.toLoc (by simp)).inv.toNatTrans.app M =
    𝟙 _ := by
  have hB :
      (F.mapComp' (𝟙 U).op.toLoc f.op.toLoc f.op.toLoc (by simp)).inv.toNatTrans.app M =
        (F.map f.op.toLoc).toFunctor.map
          ((F.mapId (LocallyDiscrete.mk (op U))).hom.toNatTrans.app M) ≫
        eqToHom (by simp) := by
    simpa only [op_id, Quiver.Hom.id_toLoc] using
      (Pseudofunctor.mapComp'_id_comp_inv_app
        (F := F) (f := f.op.toLoc) M)
  rw [hB]
  rw [← (F.map f.op.toLoc).toFunctor.map_comp_assoc]
  rw [Cat.Hom.inv_hom_id_toNatTrans_app]
  dsimp only [Cat.Hom.id_toFunctor, Functor.id_obj]
  simp only [Functor.map_id, Category.id_comp]
  rw [eqToHom_refl]

end Pseudofunctor

/-- Stage 2 identity-coherence helper for the canonical fiber pseudofunctor: after the local
identity calculation has reduced to the canonical pseudofunctor's identity/composition comparison
tail, the chosen identity pullback arrow cancels it. -/
theorem canonicalFiberPseudofunctor_mapComp_id_hom_app_comp_identityCart_core
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    {U V : C} (f : V ⟶ U) (z : p.Fiber U) :
    let cart : (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z :=
      ⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
        exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩
    (eqToHom (by simp) ≫
        ((canonicalFiberPseudofunctor p).mapComp'
          (𝟙 U).op.toLoc f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app z) ≫
      ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map cart =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z) := by
  intro cart
  have hcomp :
      ((canonicalFiberPseudofunctor p).mapComp'
          (𝟙 U).op.toLoc f.op.toLoc
          f.op.toLoc (by simp)).hom.toNatTrans.app z =
        eqToHom (by simp) ≫
          ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
            (((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z) := by
    simpa only [op_id, Quiver.Hom.id_toLoc] using
      (Pseudofunctor.mapComp'_id_comp_hom_app
        (F := canonicalFiberPseudofunctor p)
        (f := f.op.toLoc) z)
  erw [hcomp]
  dsimp only [cart]
  have hunit :
      ((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z) =
        𝟙 z := by
    apply Functor.Fiber.hom_ext
    simpa [canonicalFiberPseudofunctor, PullbackChoice.fiberPseudofunctor,
      PullbackChoice.pullbackIdIso, Category.assoc] using
      (canonicalPullbackChoice p).pullbackIdComponentIso_fac U z
  dsimp only [Cat.Hom.id_toFunctor, Functor.id_obj]
  simp only [Category.id_comp, eqToHom_refl]
  erw [← ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map_comp]
  change ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map
      ((((canonicalFiberPseudofunctor p).mapId (LocallyDiscrete.mk (op U))).inv.toNatTrans.app z) ≫
        (⟨(canonicalPullbackChoice p).map (𝟙 U) z, by
          exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) z).toIsHomLift⟩ :
          (𝟙 U) ^*[canonicalPullbackChoice p] z ⟶ z)) =
    ((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.map (𝟙 z)
  rw [hunit]
  simp

/-- Stage 2 identity-coherence helper for the source left-unit calculation: the target tail in
the local composite of the literal identity representative with a representative over `f`
reduces to the explicit transport from `f^*` to `(id ≫ f)^*`, after restriction along `q`. -/
theorem canonicalFiberPseudofunctor_leftIdentityTargetTail_comp_transport_core
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    {U V W : C} (f : U ⟶ V) (q : W ⟶ U) (z : p.Fiber V) :
    let Fp := canonicalFiberPseudofunctor p
    let zU := (Fp.map f.op.toLoc).toFunctor.obj z
    let hbase : f = 𝟙 U ≫ f := (Category.id_comp f).symm
    let targetTransport :
        zU ⟶ (𝟙 U ≫ f) ^*[canonicalPullbackChoice p] z :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice p).pullbackFunctor k) hbase)).app z
    (((Fp.mapComp' (𝟙 U).op.toLoc q.op.toLoc q.op.toLoc (by simp)).hom.toNatTrans.app zU) ≫
      (Fp.map q.op.toLoc).toFunctor.map
        ((Fp.mapComp f.op.toLoc (𝟙 U).op.toLoc).inv.toNatTrans.app z)) =
    (Fp.map q.op.toLoc).toFunctor.map targetTransport := by
  intro Fp zU hbase targetTransport
  let cart : (𝟙 U) ^*[canonicalPullbackChoice p] zU ⟶ zU :=
    ⟨(canonicalPullbackChoice p).map (𝟙 U) zU, by
      exact ((canonicalPullbackChoice p).isStronglyCartesian (𝟙 U) zU).toIsHomLift⟩
  have hcart := canonicalFiberPseudofunctor_mapComp_comp_id_inv_app_eq_identityCart_comp_transport_core
    (p := p) f z
  dsimp only [Fp, zU, hbase, targetTransport] at hcart
  have hcore := canonicalFiberPseudofunctor_mapComp_id_hom_app_comp_identityCart_core
    (p := p) q zU
  dsimp [Fp, zU, hbase, targetTransport] at hcart hcore ⊢
  rw [hcart]
  erw [Functor.map_comp]
  rw [← Category.assoc]
  rw [← Category.id_comp (((canonicalFiberPseudofunctor p).mapComp'
    (𝟙 (LocallyDiscrete.mk (op U))) q.op.toLoc q.op.toLoc (by simp)).hom.toNatTrans.app
      (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj z))]
  erw [hcore]
  have hmapid :
      ((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.map
        (𝟙 (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj z)) =
      𝟙 _ := ((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.map_id
        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj z)
  erw [hmapid]
  rw [Category.id_comp]
  rfl

/-- Stage 2 identity-coherence helper for the source left-unit calculation: a target object
transport induced by an equality of base arrows is a heterogeneous no-op after further
restriction.  This keeps the owner transport explicit while allowing later local-family
calculations to cancel the final transport tail. -/
theorem canonicalFiberPseudofunctor_map_eqToHom_transport_tail_heq
    {C : Type u} [Category.{v} C]
    {T : Type uX} [Category.{vX} T]
    (p : T ⥤ C) [p.IsFibered]
    {U V W : C} {f f' : U ⟶ V} (h : f = f') (q : W ⟶ U)
    (z : p.Fiber V)
    {A : (canonicalFiberPseudofunctor p).obj (LocallyDiscrete.mk (op W))}
    (e : A ⟶
      ((canonicalFiberPseudofunctor p).map q.op.toLoc).toFunctor.obj
        (((canonicalFiberPseudofunctor p).map f.op.toLoc).toFunctor.obj z)) :
    let Fp := canonicalFiberPseudofunctor p
    let zU := (Fp.map f.op.toLoc).toFunctor.obj z
    let targetTransport :
        zU ⟶ f' ^*[canonicalPullbackChoice p] z :=
      (eqToHom (congrArg (fun k => (canonicalPullbackChoice p).pullbackFunctor k) h)).app z
    HEq (e ≫ (Fp.map q.op.toLoc).toFunctor.map targetTransport) e := by
  intro Fp zU targetTransport
  cases h
  dsimp [targetTransport]
  apply heq_of_eq
  erw [Functor.map_id]
  exact Category.comp_id e

end CategoryTheory
