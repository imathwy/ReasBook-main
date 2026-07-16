import stacks_proof.stacks_project.Chap08.Lemma_8_12_8.FullFaithful

open CategoryTheory
open CategoryTheory.Limits
open scoped FibredCategoryOver
open scoped Functor

universe u v uS vS

namespace CategoryTheory

section

variable {C : Type u} {D : Type u}
variable [Category.{v} C] [Category.{v} D]

section Pushforward

variable (u : C ⥤ D)
variable [HasPullbacks C] [HasEqualizers C]
variable [PreservesLimitsOfShape WalkingCospan u]
variable [PreservesLimitsOfShape WalkingParallelPair u]

/-- Helper for Lemma 8.12.8: the first projection of a target pullback object is the base
object of its source. -/
private theorem pushforwardPullbackTargetBase_eq
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (x : X.S) :
    X.p.obj x = (H.obj.obj x).fst := by
  -- The based-functor equality for `H` says exactly that the pullback first projection is
  -- the original base object.
  simpa [FibredCategoryOver.toBasedCategory, FibredCategoryOver.p,
    FibredCategoryOver.pullback_p] using (BasedFunctor.w_obj H.obj x).symm

/-- Helper for Lemma 8.12.8: the first projection of a target pullback morphism is the source
base map transported through the endpoint identifications. -/
private theorem pushforwardPullbackTargetMap_fst
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {x y : X.S} (f : x ⟶ y) :
    (H.obj.map f).fst =
      eqToHom (pushforwardPullbackTargetBase_eq u X Y H x).symm ≫
        X.p.map f ≫
          eqToHom (pushforwardPullbackTargetBase_eq u X Y H y) := by
  -- Project the naturality equation of the based functor `H` to the base category.
  have h := Functor.congr_hom H.obj.w f
  simpa [FibredCategoryOver.toBasedCategory, FibredCategoryOver.p,
    FibredCategoryOver.pullback_p, pushforwardPullbackTargetBase_eq,
    Category.assoc] using h

/-- Helper for Lemma 8.12.8: the base arrow used to pull back the target object attached to a
prelocalized pushforward object. -/
private abbrev pushforwardPullbackTargetBaseMap
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    A.fst.left ⟶ Y.p.obj (H.obj.obj A.snd).snd :=
  pushforwardUnitSourceBaseMap u X A ≫
    u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H A.snd)) ≫
      (H.obj.obj A.snd).iso.hom

/-- Helper for Lemma 8.12.8: the target base arrows are natural for prelocalized pushforward
morphisms. -/
private theorem pushforwardPullbackTargetBaseMap_naturality
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    pushforwardPullbackTargetBaseMap u X Y H A ≫
        Y.p.map (H.obj.map f.snd).snd =
      f.fst.left ≫ pushforwardPullbackTargetBaseMap u X Y H B := by
  -- Combine naturality of the source-base map with the pullback square for `H.map f.snd`.
  have hsource :
      f.fst.left ≫ pushforwardUnitSourceBaseMap u X B =
        pushforwardUnitSourceBaseMap u X A ≫ u.map (X.p.map f.snd) := by
    simpa [pushforwardUnitSourcePrelocalizedChart, pushforwardUnitSourceBaseMap,
      pushforwardFibredCategoryUnitPrelocalized, Category.assoc] using
      congrArg (fun k ↦ k.fst.left)
        (pushforwardUnitSourcePrelocalizedChart_naturality u X f)
  have hfst := pushforwardPullbackTargetMap_fst u X Y H f.snd
  have hw := (H.obj.map f.snd).w
  calc
    pushforwardPullbackTargetBaseMap u X Y H A ≫
        Y.p.map (H.obj.map f.snd).snd =
      pushforwardUnitSourceBaseMap u X A ≫
        (u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H A.snd)) ≫
          ((H.obj.obj A.snd).iso.hom ≫
            Y.p.map (H.obj.map f.snd).snd)) := by
        simp [pushforwardPullbackTargetBaseMap, Category.assoc]
    _ =
      pushforwardUnitSourceBaseMap u X A ≫
        (u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H A.snd)) ≫
          (u.map (H.obj.map f.snd).fst ≫
            (H.obj.obj B.snd).iso.hom)) := by
        rw [← hw]
    _ =
      pushforwardUnitSourceBaseMap u X A ≫
        (u.map
          (eqToHom (pushforwardPullbackTargetBase_eq u X Y H A.snd) ≫
            (H.obj.map f.snd).fst) ≫
          (H.obj.obj B.snd).iso.hom) := by
        simp [Functor.map_comp, Category.assoc]
    _ =
      pushforwardUnitSourceBaseMap u X A ≫
        (u.map
          (X.p.map f.snd ≫
            eqToHom (pushforwardPullbackTargetBase_eq u X Y H B.snd)) ≫
          (H.obj.obj B.snd).iso.hom) := by
        rw [hfst]
        simp [Category.assoc]
    _ =
      pushforwardUnitSourceBaseMap u X A ≫
        u.map (X.p.map f.snd) ≫
        u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H B.snd)) ≫
        (H.obj.obj B.snd).iso.hom := by
        simp [Functor.map_comp, Category.assoc]
    _ =
      f.fst.left ≫ pushforwardUnitSourceBaseMap u X B ≫
        u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H B.snd)) ≫
        (H.obj.obj B.snd).iso.hom := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫
              u.map (eqToHom (pushforwardPullbackTargetBase_eq u X Y H B.snd)) ≫
                (H.obj.obj B.snd).iso.hom)
            hsource.symm
    _ = f.fst.left ≫ pushforwardPullbackTargetBaseMap u X Y H B := by
        simp [pushforwardPullbackTargetBaseMap, Category.assoc]

/-- Helper for Lemma 8.12.8: the chosen target object over the `D`-component of a prelocalized
pushforward object. -/
private noncomputable abbrev pushforwardPullbackTargetObj
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) : Y.S :=
  Functor.IsPreFibered.pullbackObj (p := Y.p) (a := (H.obj.obj A.snd).snd) rfl
    (pushforwardPullbackTargetBaseMap u X Y H A)

/-- Helper for Lemma 8.12.8: the chosen chart from the target object to the `Y`-component of
`H`. -/
private noncomputable abbrev pushforwardPullbackTargetChart
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    pushforwardPullbackTargetObj u X Y H A ⟶ (H.obj.obj A.snd).snd :=
  Functor.IsPreFibered.pullbackMap (p := Y.p) (a := (H.obj.obj A.snd).snd) rfl
    (pushforwardPullbackTargetBaseMap u X Y H A)

/-- Helper for Lemma 8.12.8: the chosen target object lies over the `D`-component of the
prelocalized pushforward object. -/
private theorem pushforwardPullbackTargetObj_proj
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    Y.p.obj (pushforwardPullbackTargetObj u X Y H A) = A.fst.left := by
  -- This is the projection formula for the chosen pullback object in `Y`.
  simpa [pushforwardPullbackTargetObj] using
    Functor.IsPreFibered.pullbackObj_proj (p := Y.p)
      (a := (H.obj.obj A.snd).snd) rfl
      (pushforwardPullbackTargetBaseMap u X Y H A)

/-- Helper for Lemma 8.12.8: the chosen target chart is strongly cartesian. -/
private theorem pushforwardPullbackTargetChart_isStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A)
      (pushforwardPullbackTargetChart u X Y H A) := by
  -- The chosen pullback map is Cartesian, and `Y.p` is fibered.
  exact Functor.IsFibered.isStronglyCartesian_of_isCartesian Y.p
    (pushforwardPullbackTargetBaseMap u X Y H A)
    (pushforwardPullbackTargetChart u X Y H A)

/-- Helper for Lemma 8.12.8: the chosen target chart is a hom-lift over its base arrow. -/
private theorem pushforwardPullbackTargetChart_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    Y.p.IsHomLift (pushforwardPullbackTargetBaseMap u X Y H A)
      (pushforwardPullbackTargetChart u X Y H A) := by
  -- Hom-lift data is part of the strongly cartesian structure.
  let hcart := pushforwardPullbackTargetChart_isStronglyCartesian u X Y H A
  exact hcart.toIsHomLift

/-- Helper for Lemma 8.12.8: the canonical target composite is a hom-lift over the natural
composite base arrow. -/
private theorem pushforwardPullbackTargetMapTarget_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    Y.p.IsHomLift
      (pushforwardPullbackTargetBaseMap u X Y H A ≫
        Y.p.map (H.obj.map f.snd).snd)
      (pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd) := by
  -- Compose the chart lift with the literal projection lift of the `Y`-component of `H.map`.
  letI : Y.p.IsHomLift (pushforwardPullbackTargetBaseMap u X Y H A)
      (pushforwardPullbackTargetChart u X Y H A) :=
    pushforwardPullbackTargetChart_isHomLift u X Y H A
  infer_instance

/-- Helper for Lemma 8.12.8: the target map induced by a prelocalized pushforward morphism. -/
private noncomputable abbrev pushforwardPullbackTargetMap
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    pushforwardPullbackTargetObj u X Y H A ⟶
      pushforwardPullbackTargetObj u X Y H B :=
  Functor.IsStronglyCartesian.map Y.p
    (pushforwardPullbackTargetBaseMap u X Y H B)
    (pushforwardPullbackTargetChart u X Y H B)
    (pushforwardPullbackTargetBaseMap_naturality u X Y H f)
    (pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd)

/-- Helper for Lemma 8.12.8: the induced target map factors through the chosen target chart. -/
private theorem pushforwardPullbackTargetMap_fac
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    pushforwardPullbackTargetMap u X Y H f ≫
        pushforwardPullbackTargetChart u X Y H B =
      pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd := by
  -- This is the defining factorization from the strong-cartesian universal property.
  exact Functor.IsStronglyCartesian.fac Y.p
    (pushforwardPullbackTargetBaseMap u X Y H B)
    (pushforwardPullbackTargetChart u X Y H B)
    (pushforwardPullbackTargetBaseMap_naturality u X Y H f)
    (pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd)

/-- Helper for Lemma 8.12.8: the induced target map is a hom-lift over the `D`-component of the
prelocalized morphism. -/
private theorem pushforwardPullbackTargetMap_isHomLift
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B : u ₚₚ X.p} (f : A ⟶ B) :
    Y.p.IsHomLift f.fst.left (pushforwardPullbackTargetMap u X Y H f) := by
  -- The universal-property map was chosen over the left `D`-component.
  exact Functor.IsStronglyCartesian.map_isHomLift Y.p
    (pushforwardPullbackTargetBaseMap u X Y H B)
    (pushforwardPullbackTargetChart u X Y H B)
    (pushforwardPullbackTargetBaseMap_naturality u X Y H f)
    (pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd)

/-- Helper for Lemma 8.12.8: the induced target map of an identity is the identity. -/
private theorem pushforwardPullbackTargetMap_id
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) :
    pushforwardPullbackTargetMap u X Y H (𝟙 A) =
      𝟙 (pushforwardPullbackTargetObj u X Y H A) := by
  -- Both maps are lifts over the identity and have the same composite with the target chart.
  let chart := pushforwardPullbackTargetChart u X Y H A
  letI : Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A) chart :=
    pushforwardPullbackTargetChart_isStronglyCartesian u X Y H A
  letI : Y.p.IsHomLift (𝟙 A.fst.left) (pushforwardPullbackTargetMap u X Y H (𝟙 A)) :=
    pushforwardPullbackTargetMap_isHomLift u X Y H (𝟙 A)
  letI : Y.p.IsHomLift (𝟙 A.fst.left) (𝟙 (pushforwardPullbackTargetObj u X Y H A)) := by
    exact IsHomLift.id (pushforwardPullbackTargetObj_proj u X Y H A)
  apply Functor.IsStronglyCartesian.ext Y.p
    (pushforwardPullbackTargetBaseMap u X Y H A) chart (𝟙 A.fst.left)
  rw [pushforwardPullbackTargetMap_fac]
  change chart ≫ (H.obj.map (𝟙 A.snd)).snd =
    𝟙 (pushforwardPullbackTargetObj u X Y H A) ≫ chart
  rw [H.obj.map_id]
  rw [Category.id_comp]
  exact Category.comp_id chart

/-- Helper for Lemma 8.12.8: the induced target map respects composition. -/
private theorem pushforwardPullbackTargetMap_comp
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    {A B E : u ₚₚ X.p} (f : A ⟶ B) (g : B ⟶ E) :
    pushforwardPullbackTargetMap u X Y H (f ≫ g) =
      pushforwardPullbackTargetMap u X Y H f ≫
        pushforwardPullbackTargetMap u X Y H g := by
  -- The two composites are lifts over the same base map and agree after the target chart.
  let chartE := pushforwardPullbackTargetChart u X Y H E
  letI : Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H E) chartE :=
    pushforwardPullbackTargetChart_isStronglyCartesian u X Y H E
  letI :
      Y.p.IsHomLift ((f ≫ g).fst.left)
        (pushforwardPullbackTargetMap u X Y H (f ≫ g)) :=
    pushforwardPullbackTargetMap_isHomLift u X Y H (f ≫ g)
  have hfgLift :
      Y.p.IsHomLift ((f ≫ g).fst.left)
        (pushforwardPullbackTargetMap u X Y H f ≫
          pushforwardPullbackTargetMap u X Y H g) := by
    change Y.p.IsHomLift (f.fst.left ≫ g.fst.left)
      (pushforwardPullbackTargetMap u X Y H f ≫
        pushforwardPullbackTargetMap u X Y H g)
    letI : Y.p.IsHomLift f.fst.left (pushforwardPullbackTargetMap u X Y H f) :=
      pushforwardPullbackTargetMap_isHomLift u X Y H f
    letI : Y.p.IsHomLift g.fst.left (pushforwardPullbackTargetMap u X Y H g) :=
      pushforwardPullbackTargetMap_isHomLift u X Y H g
    infer_instance
  letI :
      Y.p.IsHomLift ((f ≫ g).fst.left)
        (pushforwardPullbackTargetMap u X Y H f ≫
          pushforwardPullbackTargetMap u X Y H g) :=
    hfgLift
  apply Functor.IsStronglyCartesian.ext Y.p
    (pushforwardPullbackTargetBaseMap u X Y H E) chartE ((f ≫ g).fst.left)
  rw [pushforwardPullbackTargetMap_fac]
  rw [Category.assoc, pushforwardPullbackTargetMap_fac]
  rw [← Category.assoc, pushforwardPullbackTargetMap_fac]
  change
    pushforwardPullbackTargetChart u X Y H A ≫
        (H.obj.map (f.snd ≫ g.snd)).snd =
      (pushforwardPullbackTargetChart u X Y H A ≫
        (H.obj.map f.snd).snd) ≫ (H.obj.map g.snd).snd
  rw [H.obj.map_comp]
  have hsnd :
      (H.obj.map f.snd ≫ H.obj.map g.snd).snd =
        (H.obj.map f.snd).snd ≫ (H.obj.map g.snd).snd := rfl
  rw [hsnd]
  simp [Category.assoc]

/-- Helper for Lemma 8.12.8: a strongly cartesian morphism for a pullback projection has a
strongly cartesian second component in the original fibred category. -/
private theorem pullbackProjection_snd_isStronglyCartesian
    {S : Type uS} [Category.{vS} S] (p : S ⥤ D) [p.IsFibered]
    {a b : CategoricalPullback u p} (φ : a ⟶ b)
    (hφ : (CategoricalPullback.π₁ u p).IsStronglyCartesian
      ((CategoricalPullback.π₁ u p).map φ) φ) :
    p.IsStronglyCartesian (p.map φ.snd) φ.snd := by
  -- Compare `φ` with the pullback-projection lift built from a cartesian lift of its second
  -- projection, then transport cartesianness across the resulting domain isomorphism.
  classical
  let π := CategoricalPullback.π₁ u p
  let baseMap : p.obj a.snd ⟶ p.obj b.snd := p.map φ.snd
  obtain ⟨y, ψ, hψcart⟩ := IsPreFibered.exists_isCartesian p rfl baseMap
  letI : p.IsCartesian baseMap ψ := hψcart
  letI : p.IsStronglyCartesian baseMap ψ :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian p baseMap ψ
  have hy : p.obj y = p.obj a.snd := IsHomLift.domain_eq p baseMap ψ
  let y' : CategoricalPullback u p :=
    { fst := a.fst
      snd := y
      iso := a.iso ≪≫ eqToIso hy.symm }
  have hψfac : p.map ψ = eqToHom hy ≫ baseMap := by
    simpa [baseMap] using (IsHomLift.fac' p baseMap ψ)
  let ψ' : y' ⟶ b :=
    { fst := φ.fst
      snd := ψ
      w := by
        dsimp [y']
        calc
          u.map φ.fst ≫ b.iso.hom = a.iso.hom ≫ p.map φ.snd := φ.w
          _ = (a.iso.hom ≫ eqToHom hy.symm) ≫ p.map ψ := by
            rw [hψfac]
            simp [baseMap, Category.assoc] }
  have hψowner : p.IsStronglyCartesian (p.map ψ) ψ := by
    exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
      (p := p) (hb := rfl) (f := baseMap) (φ := ψ)
  have hψ'cart : π.IsStronglyCartesian (π.map ψ') ψ' := by
    exact pullbackProjection_isStronglyCartesian_of_snd u p ψ' hψowner
  letI : π.IsStronglyCartesian (π.map φ) φ := hφ
  letI : π.IsStronglyCartesian (π.map ψ') ψ' := hψ'cart
  have hbase_eq : π.map ψ' = (Iso.refl a.fst).hom ≫ π.map φ := by
    simp [π, ψ']
  let e := Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := π) (f := π.map φ) (f' := π.map ψ') (g := Iso.refl a.fst) hbase_eq φ ψ'
  have he_fac : e.hom ≫ φ = ψ' := by
    simpa [e] using Functor.IsStronglyCartesian.fac π (π.map φ) φ hbase_eq ψ'
  have hsnd_fac : e.hom.snd ≫ φ.snd = ψ := by
    simpa [ψ'] using congrArg CategoricalPullback.Hom.snd he_fac
  have hinv_snd_fac : e.inv.snd ≫ ψ = φ.snd := by
    rw [← hsnd_fac]
    have h := congrArg CategoricalPullback.Hom.snd e.inv_hom_id
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ φ.snd) h
  have hinv_snd_iso : IsIso e.inv.snd := by
    infer_instance
  have hinv_snd_lift : p.IsHomLift (p.map e.inv.snd) e.inv.snd := by
    infer_instance
  letI : IsIso e.inv.snd := hinv_snd_iso
  letI : p.IsHomLift (p.map e.inv.snd) e.inv.snd := hinv_snd_lift
  have hinv_snd_cart : p.IsStronglyCartesian (p.map e.inv.snd) e.inv.snd := by
    infer_instance
  letI : p.IsStronglyCartesian (p.map e.inv.snd) e.inv.snd := hinv_snd_cart
  letI : p.IsStronglyCartesian (p.map ψ) ψ := hψowner
  have hcomp : p.IsStronglyCartesian (p.map e.inv.snd ≫ p.map ψ) (e.inv.snd ≫ ψ) := by
    infer_instance
  have hbase_comp : p.map e.inv.snd ≫ p.map ψ = p.map φ.snd := by
    rw [← hinv_snd_fac]
    simp [Functor.map_comp]
  rw [← hinv_snd_fac]
  simpa [hbase_comp] using hcomp

/-- Helper for Lemma 8.12.8: the prelocalized target functor attached to a pullback-valued
morphism of fibred categories. -/
private noncomputable abbrev pushforwardPullbackTargetPrelocalizedFunctor
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory) :
    u ₚₚ X.p ⥤ Y.S where
  obj A := pushforwardPullbackTargetObj u X Y H A
  map f := pushforwardPullbackTargetMap u X Y H f
  map_id A := pushforwardPullbackTargetMap_id u X Y H A
  map_comp f g := pushforwardPullbackTargetMap_comp u X Y H f g

/-- Helper for Lemma 8.12.8: the prelocalized target functor lies over the source projection to
`D`. -/
private theorem pushforwardPullbackTargetPrelocalizedFunctor_comp_projection
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory) :
    pushforwardPullbackTargetPrelocalizedFunctor u X Y H ⋙ Y.p =
      Functor.pushforwardSourceProjection u X.p := by
  -- The object projection is the chosen pullback-object projection; morphisms are hom-lifts over
  -- the left `D`-component of the prelocalized morphism.
  refine Functor.ext (fun A ↦ pushforwardPullbackTargetObj_proj u X Y H A) ?_
  · intro A B f
    let θ := pushforwardPullbackTargetMap u X Y H f
    have hθ : Y.p.IsHomLift f.fst.left θ :=
      pushforwardPullbackTargetMap_isHomLift u X Y H f
    simpa [Functor.comp_map, Functor.pushforwardSourceProjection, θ] using
      (IsHomLift.fac' Y.p f.fst.left θ)

/-- Helper for Lemma 8.12.8: the prelocalized target functor sends pushforward denominators to
isomorphisms. -/
private theorem pushforwardPullbackTargetPrelocalizedFunctor_invertsFractions
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory) :
    (u.pushforwardFractions X.p).IsInvertedBy
      (pushforwardPullbackTargetPrelocalizedFunctor u X Y H) := by
  intro A B f hf
  have hfLeft : IsIso f.fst.left :=
    pushforwardFractions_left_isIso (u := u) (p := X.p) hf
  let θ := pushforwardPullbackTargetMap u X Y H f
  have hθLift : Y.p.IsHomLift f.fst.left θ :=
    pushforwardPullbackTargetMap_isHomLift u X Y H f
  letI : IsIso f.fst.left := hfLeft
  letI : Y.p.IsHomLift f.fst.left θ := hθLift
  have hθCart : Y.p.IsStronglyCartesian f.fst.left θ := by
    let chartB := pushforwardPullbackTargetChart u X Y H B
    have hchartB :
        Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H B) chartB :=
      pushforwardPullbackTargetChart_isStronglyCartesian u X Y H B
    have hcomp :
        Y.p.IsStronglyCartesian (f.fst.left ≫ pushforwardPullbackTargetBaseMap u X Y H B)
          (θ ≫ chartB) := by
      rw [pushforwardPullbackTargetMap_fac]
      have hchartA :
          Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A)
            (pushforwardPullbackTargetChart u X Y H A) :=
        pushforwardPullbackTargetChart_isStronglyCartesian u X Y H A
      have hHsnd :
          Y.p.IsStronglyCartesian (Y.p.map (H.obj.map f.snd).snd)
            (H.obj.map f.snd).snd := by
        have hHcart :
            (u ᵖ Y).p.IsStronglyCartesian
              ((u ᵖ Y).p.map (H.obj.map f.snd)) (H.obj.map f.snd) :=
          H.property f.snd hf.2
        exact pullbackProjection_snd_isStronglyCartesian u Y.p
          (H.obj.map f.snd) (by
            simpa [FibredCategoryOver.pullback_p] using hHcart)
      letI :
          Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A)
            (pushforwardPullbackTargetChart u X Y H A) :=
        hchartA
      letI :
          Y.p.IsStronglyCartesian (Y.p.map (H.obj.map f.snd).snd)
            (H.obj.map f.snd).snd :=
        hHsnd
      have hraw :
          Y.p.IsStronglyCartesian
            (pushforwardPullbackTargetBaseMap u X Y H A ≫
              Y.p.map (H.obj.map f.snd).snd)
            (pushforwardPullbackTargetChart u X Y H A ≫ (H.obj.map f.snd).snd) := by
        infer_instance
      have hnat := pushforwardPullbackTargetBaseMap_naturality u X Y H f
      rw [hnat] at hraw
      exact hraw
    letI :
        Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H B) chartB :=
      hchartB
    letI :
        Y.p.IsStronglyCartesian (f.fst.left ≫ pushforwardPullbackTargetBaseMap u X Y H B)
          (θ ≫ chartB) :=
      hcomp
    exact
      @Functor.IsStronglyCartesian.of_comp _ _ _ _ Y.p
        A.fst.left B.fst.left (Y.p.obj (H.obj.obj B.snd).snd)
        (pushforwardPullbackTargetObj u X Y H A)
        (pushforwardPullbackTargetObj u X Y H B)
        ((H.obj.obj B.snd).snd)
        f.fst.left (pushforwardPullbackTargetBaseMap u X Y H B)
        θ chartB hchartB hcomp hθLift
  change IsIso θ
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso Y.p f.fst.left θ

/-- Helper for Lemma 8.12.8: the target functor sends the canonical source-precomposition
charts to strongly cartesian morphisms in the target fibred category. -/
private theorem pushforwardPullbackTarget_sourcePrecompose_isStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) {V : D} (f : V ⟶ A.fst.left) :
    Y.p.IsStronglyCartesian f
      ((pushforwardPullbackTargetPrelocalizedFunctor u X Y H).map
        (Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) A f)) := by
  -- The image of a source-precomposition chart becomes the unique factor between the two
  -- chosen target pullback charts; composing with the target chart gives the source chart.
  let T := Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) A f
  let α := Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) A f
  let θ := pushforwardPullbackTargetMap u X Y H α
  let chartA := pushforwardPullbackTargetChart u X Y H A
  let chartT := pushforwardPullbackTargetChart u X Y H T
  have hθLift : Y.p.IsHomLift f θ :=
    pushforwardPullbackTargetMap_isHomLift u X Y H α
  have hchartA :
      Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A) chartA :=
    pushforwardPullbackTargetChart_isStronglyCartesian u X Y H A
  have hchartT :
      Y.p.IsStronglyCartesian (f ≫ pushforwardPullbackTargetBaseMap u X Y H A) chartT := by
    have hnat := pushforwardPullbackTargetBaseMap_naturality u X Y H α
    have hraw :
        Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H T) chartT :=
      pushforwardPullbackTargetChart_isStronglyCartesian u X Y H T
    have hbaseT :
        pushforwardPullbackTargetBaseMap u X Y H T =
          f ≫ pushforwardPullbackTargetBaseMap u X Y H A := by
      simpa [T, α, Functor.pushforwardSourcePrecomposeHom,
        Functor.pushforwardSourcePrecomposeObj] using hnat
    simpa [hbaseT] using hraw
  have hcomp :
      Y.p.IsStronglyCartesian (f ≫ pushforwardPullbackTargetBaseMap u X Y H A)
        (θ ≫ chartA) := by
    have hfac := pushforwardPullbackTargetMap_fac u X Y H α
    have hθchart : θ ≫ chartA = chartT := by
      rw [hfac]
      dsimp [α, Functor.pushforwardSourcePrecomposeHom]
      rw [H.obj.map_id]
      exact Category.comp_id chartT
    simpa [hθchart] using hchartT
  letI :
      Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A) chartA :=
    hchartA
  letI :
      Y.p.IsStronglyCartesian (f ≫ pushforwardPullbackTargetBaseMap u X Y H A)
        (θ ≫ chartA) :=
    hcomp
  exact
    @Functor.IsStronglyCartesian.of_comp _ _ _ _ Y.p
      V A.fst.left (Y.p.obj (H.obj.obj A.snd).snd)
      (pushforwardPullbackTargetObj u X Y H T)
      (pushforwardPullbackTargetObj u X Y H A)
      ((H.obj.obj A.snd).snd)
      f (pushforwardPullbackTargetBaseMap u X Y H A)
      θ chartA hchartA hcomp hθLift

/-- Helper for Lemma 8.12.8: the construction localization lift computes on morphisms in
the image of the localization functor. -/
private theorem localizationConstructionLift_map_Q
    {A : Type uS} [Category.{vS} A] {E : Type u} [Category.{v} E]
    {W : MorphismProperty A} (F : A ⥤ E) (hF : W.IsInvertedBy F)
    {X Y : A} (f : X ⟶ Y) :
    (Localization.Construction.lift F hF).map (W.Q.map f) = F.map f := by
  -- `Construction.fac` is propositionally functorial; the endpoint transports reduce to identities
  -- for objects coming directly from `Q`.
  have hsrc : eqToHom (Functor.congr_obj (Localization.Construction.fac F hF) X) = 𝟙 _ := by
    change eqToHom (by rfl : F.obj (W.Q.obj X).as.obj = F.obj X) = 𝟙 _
    rfl
  have htgt : eqToHom (Functor.congr_obj (Localization.Construction.fac F hF) Y).symm = 𝟙 _ := by
    change eqToHom (by rfl : F.obj Y = F.obj (W.Q.obj Y).as.obj) = 𝟙 _
    rfl
  have hfac := Functor.congr_hom (Localization.Construction.fac F hF) f
  have hfac' :
      (Localization.Construction.lift F hF).map (W.Q.map f) =
        eqToHom (Functor.congr_obj (Localization.Construction.fac F hF) X) ≫
          F.map f ≫
            eqToHom (Functor.congr_obj (Localization.Construction.fac F hF) Y).symm := by
    simpa [Functor.comp_map] using hfac
  rw [hfac', hsrc, htgt]
  calc
    𝟙 ((W.Q ⋙ Localization.Construction.lift F hF).obj X) ≫ F.map f ≫ 𝟙 (F.obj Y) =
        F.map f ≫ 𝟙 (F.obj Y) := by
      exact Category.id_comp (F.map f ≫ 𝟙 (F.obj Y))
    _ = F.map f := by
      rw [Category.comp_id]

/-- Helper for Lemma 8.12.8: the localized target lift sends source-precomposition charts to
strongly cartesian morphisms. -/
private theorem pushforwardPullbackTargetLift_sourcePrecompose_isStronglyCartesian
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D)
    (H : (FibredCategoryMor.objectProperty X (u ᵖ Y)).FullSubcategory)
    (A : u ₚₚ X.p) {V : D} (f : V ⟶ A.fst.left) :
    let Fpre := pushforwardPullbackTargetPrelocalizedFunctor u X Y H
    let hFpre : (u.pushforwardFractions X.p).IsInvertedBy Fpre :=
      pushforwardPullbackTargetPrelocalizedFunctor_invertsFractions u X Y H
    Y.p.IsStronglyCartesian f
      ((Localization.Construction.lift Fpre hFpre).map
        ((u.pushforwardFractions X.p).Q.map
          (Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) A f))) := by
  -- Compute the localization lift on `Q.map`, then use the target chart lemma before localization.
  dsimp only
  rw [localizationConstructionLift_map_Q]
  exact pushforwardPullbackTarget_sourcePrecompose_isStronglyCartesian u X Y H A f

/-- Helper for Lemma 8.12.8: the lifted pullback comparison is essentially surjective. -/
theorem pushforwardPullbackFibredMorphismLift_essSurj
    (X : FibredCategoryOver C) (Y : FibredCategoryOver D) :
    (pushforwardPullbackFibredMorphismLift u X Y).EssSurj := by
  -- TODO: descend the `Y`-component of a target object `H : X ⟶ uᵖ Y` through the pushforward
  -- localization, then compare the lifted object with `H` on unit-source objects via
  -- `pushforwardUnitSourceChart_unit`.
  constructor
  intro H
  -- Descend the target component of `H` along the pushforward localization and package it as a
  -- morphism of fibred categories over `D`.
  let Fpre := pushforwardPullbackTargetPrelocalizedFunctor u X Y H
  let hFpre : (u.pushforwardFractions X.p).IsInvertedBy Fpre :=
    pushforwardPullbackTargetPrelocalizedFunctor_invertsFractions u X Y H
  have hFloc :
      Localization.Construction.lift Fpre hFpre ⋙ Y.p =
        (FibredCategoryOver.pushforward u X).p := by
    rw [FibredCategoryOver.pushforward_p]
    apply Localization.Construction.uniq
    rw [← Functor.assoc, Localization.Construction.fac]
    rw [Functor.pushforwardProjection, Localization.Construction.fac]
    exact pushforwardPullbackTargetPrelocalizedFunctor_comp_projection u X Y H
  let Floc : (FibredCategoryOver.pushforward u X).S ⥤ Y.S :=
    Localization.Construction.lift Fpre hFpre
  let Gbf : (FibredCategoryOver.pushforward u X).toBasedCategory ⥤ᵇ Y.toBasedCategory :=
    { toFunctor := Floc
      w := hFloc }
  have hGbf : BasedFunctor.PreservesStronglyCartesian Gbf := by
    intro A B φ hφ
    -- Compare `φ` with the canonical source-precomposition chart ending at a chosen
    -- preimage of `B`, then transport the target strong-cartesian result across the
    -- resulting domain isomorphism.
    let P := (FibredCategoryOver.pushforward u X).p
    let Q := (u.pushforwardFractions X.p).Q
    let B₀ := Q.objPreimage B
    let eB := Q.objObjPreimageIso B
    let f₀ : P.obj A ⟶ B₀.fst.left := P.map φ ≫ P.map eB.inv
    let T := Functor.pushforwardSourcePrecomposeObj (u := u) (p := X.p) B₀ f₀
    let α := Functor.pushforwardSourcePrecomposeHom (u := u) (p := X.p) B₀ f₀
    let β : Q.obj T ⟶ Q.obj B₀ := Q.map α
    let ψ : Q.obj T ⟶ B := β ≫ eB.hom
    have hβSource : P.IsStronglyCartesian f₀ β := by
      simpa [P, Q, β, α, f₀, FibredCategoryOver.pushforward_p] using
        pushforwardProjection_Q_sourcePrecompose_isStronglyCartesian
          (u := u) (p := X.p) B₀ f₀
    have heBSource : P.IsStronglyCartesian (P.map eB.hom) eB.hom := by
      have heBLift : P.IsHomLift (P.map eB.hom) eB.hom := by
        infer_instance
      have heBIso : IsIso eB.hom := by
        infer_instance
      exact @Functor.IsStronglyCartesian.of_isIso _ _ _ _ P _ _ _ _
        (P.map eB.hom) eB.hom heBLift heBIso
    have hψSource :
        P.IsStronglyCartesian (f₀ ≫ P.map eB.hom) ψ := by
      letI : P.IsStronglyCartesian f₀ β := hβSource
      letI : P.IsStronglyCartesian (P.map eB.hom) eB.hom := heBSource
      simpa [ψ] using
        (@Functor.IsStronglyCartesian.comp _ _ _ _ P
          _ _ _ _ _ _ _ _ _ _ hβSource heBSource)
    have hbaseψ :
        f₀ ≫ P.map eB.hom = (Iso.refl (P.obj A)).hom ≫ P.map φ := by
      have hcancel : P.map eB.inv ≫ P.map eB.hom = 𝟙 (P.obj B) := by
        calc
          P.map eB.inv ≫ P.map eB.hom = P.map (eB.inv ≫ eB.hom) := by
            exact (P.map_comp eB.inv eB.hom).symm
          _ = P.map (𝟙 B) := by
            exact congrArg (fun k ↦ P.map k) eB.inv_hom_id
          _ = 𝟙 (P.obj B) := by
            exact P.map_id B
      calc
        f₀ ≫ P.map eB.hom =
            (P.map φ ≫ P.map eB.inv) ≫ P.map eB.hom := rfl
        _ = P.map φ ≫ (P.map eB.inv ≫ P.map eB.hom) := by
            rw [Category.assoc]
        _ = P.map φ ≫ 𝟙 (P.obj B) := by
            rw [hcancel]
        _ = (Iso.refl (P.obj A)).hom ≫ P.map φ := by
            simp
    have hφSource : P.IsStronglyCartesian (P.map φ) φ := by
      simpa [P] using hφ
    letI : P.IsStronglyCartesian (P.map φ) φ := hφSource
    letI : P.IsStronglyCartesian (f₀ ≫ P.map eB.hom) ψ := hψSource
    let e : Q.obj T ≅ A :=
      Functor.IsStronglyCartesian.domainIsoOfBaseIso
        (p := P) hbaseψ φ ψ
    have he_fac : e.hom ≫ φ = ψ := by
      change
        (Functor.IsStronglyCartesian.domainIsoOfBaseIso
          (p := P) hbaseψ φ ψ).hom ≫ φ = ψ
      rw [Functor.IsStronglyCartesian.domainIsoOfBaseIso_hom]
      exact Functor.IsStronglyCartesian.fac P (P.map φ) φ hbaseψ ψ
    have he_inv_fac : e.inv ≫ ψ = φ := by
      rw [← he_fac]
      simp [Category.assoc]
    have hβTarget : Y.p.IsStronglyCartesian f₀ (Floc.map β) := by
      simpa [Floc, Fpre, hFpre, Q, β, α, f₀] using
        pushforwardPullbackTargetLift_sourcePrecompose_isStronglyCartesian u X Y H B₀ f₀
    have heBTarget : Y.p.IsStronglyCartesian (Y.p.map (Floc.map eB.hom))
        (Floc.map eB.hom) := by
      have hLift : Y.p.IsHomLift (Y.p.map (Floc.map eB.hom)) (Floc.map eB.hom) := by
        infer_instance
      have hIso : IsIso (Floc.map eB.hom) := by
        infer_instance
      exact @Functor.IsStronglyCartesian.of_isIso _ _ _ _ Y.p _ _ _ _
        (Y.p.map (Floc.map eB.hom)) (Floc.map eB.hom) hLift hIso
    have hψTarget : Y.p.IsStronglyCartesian (Y.p.map (Gbf.map ψ)) (Gbf.map ψ) := by
      have hβTargetOwner : Y.p.IsStronglyCartesian (Y.p.map (Floc.map β))
          (Floc.map β) := by
        letI : Y.p.IsStronglyCartesian f₀ (Floc.map β) := hβTarget
        exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
          (p := Y.p) (hb := IsHomLift.codomain_eq Y.p f₀ (Floc.map β))
          (f := f₀) (φ := Floc.map β)
      have hcomp :
          Y.p.IsStronglyCartesian
            (Y.p.map (Floc.map β) ≫ Y.p.map (Floc.map eB.hom))
            (Floc.map β ≫ Floc.map eB.hom) := by
        letI : Y.p.IsStronglyCartesian (Y.p.map (Floc.map β)) (Floc.map β) :=
          hβTargetOwner
        letI : Y.p.IsStronglyCartesian (Y.p.map (Floc.map eB.hom))
          (Floc.map eB.hom) := heBTarget
        exact @Functor.IsStronglyCartesian.comp _ _ _ _ Y.p
          _ _ _ _ _ _ _ _ _ _ hβTargetOwner heBTarget
      have hmapψ : Gbf.map ψ = Floc.map β ≫ Floc.map eB.hom := by
        change Floc.map ψ = Floc.map β ≫ Floc.map eB.hom
        dsimp [ψ]
        exact Floc.map_comp β eB.hom
      rw [hmapψ]
      exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
        (p := Y.p) (hb := rfl)
        (f := Y.p.map (Floc.map β) ≫ Y.p.map (Floc.map eB.hom))
        (φ := Floc.map β ≫ Floc.map eB.hom)
    have heTarget : Y.p.IsStronglyCartesian (Y.p.map (Gbf.map e.inv)) (Gbf.map e.inv) := by
      have hLift : Y.p.IsHomLift (Y.p.map (Gbf.map e.inv)) (Gbf.map e.inv) := by
        infer_instance
      have hIso : IsIso (Gbf.map e.inv) := by
        infer_instance
      exact @Functor.IsStronglyCartesian.of_isIso _ _ _ _ Y.p _ _ _ _
        (Y.p.map (Gbf.map e.inv)) (Gbf.map e.inv) hLift hIso
    have hφTargetExternal :
        Y.p.IsStronglyCartesian (Y.p.map (Gbf.map e.inv) ≫ Y.p.map (Gbf.map ψ))
          (Gbf.map φ) := by
      have hcomp :
          Y.p.IsStronglyCartesian (Y.p.map (Gbf.map e.inv) ≫ Y.p.map (Gbf.map ψ))
            (Gbf.map e.inv ≫ Gbf.map ψ) := by
        letI : Y.p.IsStronglyCartesian (Y.p.map (Gbf.map e.inv)) (Gbf.map e.inv) :=
          heTarget
        letI : Y.p.IsStronglyCartesian (Y.p.map (Gbf.map ψ)) (Gbf.map ψ) :=
          hψTarget
        exact @Functor.IsStronglyCartesian.comp _ _ _ _ Y.p
          _ _ _ _ _ _ _ _ _ _ heTarget hψTarget
      have hmapφ : Gbf.map e.inv ≫ Gbf.map ψ = Gbf.map φ := by
        rw [← Gbf.toFunctor.map_comp]
        exact congrArg (fun k ↦ Gbf.map k) he_inv_fac
      simpa [hmapφ] using hcomp
    exact BasedFunctor.isStronglyCartesian_rebase_over_target_eq
      (p := Y.p) (hb := rfl)
      (f := Y.p.map (Gbf.map e.inv) ≫ Y.p.map (Gbf.map ψ))
      (φ := Gbf.map φ)
  let G :
      WideSubcategory
        ((fibredCategoryOverSubTwoCategory D).hom
          (FibredCategoryOver.pushforward u X) Y).hom :=
    ⟨⟨Gbf, hGbf⟩⟩
  refine ⟨G, ?_⟩
  -- Compare the descended object with `H` after applying the pullback-comparison lift,
  -- using the unit-source chart identity on objects from `X`.
  refine ⟨ObjectProperty.isoMk (FibredCategoryMor.objectProperty X (u ᵖ Y)) ?_⟩
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun x ↦ ?component) ?natural) ?homLift
  · let A := (pushforwardFibredCategoryUnitPrelocalized u X).obj x
    have hsourceIso :
        (((pushforwardPullbackFibredMorphismLift u X Y).obj G).obj.obj x).iso.hom =
          eqToHom (pushforwardPullbackTargetObj_proj u X Y H A).symm := by
      simp [A, G, Gbf, Floc, Fpre, pushforwardPullbackFibredMorphismLift,
        pushforwardPullbackBasedFunctor, pushforwardPullbackComparisonFunctorObj,
        pushforwardPullbackComparisonSquare, pushforwardFibredCategoryUnit,
        pushforwardFibredCategoryUnitPrelocalized]
      congr 1
    let chart := pushforwardPullbackTargetChart u X Y H A
    have hchartIso : IsIso chart := by
      have hcart :
          Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A) chart := by
        exact pushforwardPullbackTargetChart_isStronglyCartesian u X Y H A
      have hbaseIso : IsIso (pushforwardPullbackTargetBaseMap u X Y H A) := by
        dsimp [A, pushforwardPullbackTargetBaseMap, pushforwardUnitSourceBaseMap,
          pushforwardFibredCategoryUnitPrelocalized]
        infer_instance
      letI :
          Y.p.IsStronglyCartesian (pushforwardPullbackTargetBaseMap u X Y H A) chart := hcart
      letI : IsIso (pushforwardPullbackTargetBaseMap u X Y H A) := hbaseIso
      exact Functor.IsStronglyCartesian.isIso_of_base_isIso Y.p
        (pushforwardPullbackTargetBaseMap u X Y H A) chart
    letI : IsIso chart := hchartIso
    let eRight :
        (((pushforwardPullbackFibredMorphismLift u X Y).obj G).obj.obj x).snd ≅
          (H.obj.obj x).snd := by
      change pushforwardPullbackTargetObj u X Y H A ≅ (H.obj.obj A.snd).snd
      exact asIso chart
    refine CategoricalPullback.mkIso
      (eqToIso (pushforwardPullbackTargetBase_eq u X Y H x)) eRight ?_
    have hbase :
        u.map (eqToIso (pushforwardPullbackTargetBase_eq u X Y H x)).hom ≫
            (H.obj.obj x).iso.hom =
          pushforwardPullbackTargetBaseMap u X Y H A := by
      simp [A, pushforwardPullbackTargetBaseMap, pushforwardUnitSourceBaseMap,
        pushforwardFibredCategoryUnitPrelocalized]
    have hchartLift : Y.p.IsHomLift (pushforwardPullbackTargetBaseMap u X Y H A) chart := by
      exact pushforwardPullbackTargetChart_isHomLift u X Y H A
    letI : Y.p.IsHomLift (pushforwardPullbackTargetBaseMap u X Y H A) chart := hchartLift
    have hfac := IsHomLift.fac Y.p (pushforwardPullbackTargetBaseMap u X Y H A) chart
    have hchartBase :
        pushforwardPullbackTargetBaseMap u X Y H A =
          eqToHom (pushforwardPullbackTargetObj_proj u X Y H A).symm ≫
            Y.p.map chart := by
      simpa [chart, Category.assoc] using hfac
    calc
      u.map (eqToIso (pushforwardPullbackTargetBase_eq u X Y H x)).hom ≫
          (H.obj.obj x).iso.hom =
        pushforwardPullbackTargetBaseMap u X Y H A := hbase
      _ = eqToHom (pushforwardPullbackTargetObj_proj u X Y H A).symm ≫
            Y.p.map chart := hchartBase
      _ =
          (((pushforwardPullbackFibredMorphismLift u X Y).obj G).obj.obj x).iso.hom ≫
            Y.p.map eRight.hom := by
        have heRight : eRight.hom = chart := rfl
        rw [hsourceIso, heRight]
        congr 1
  · intro x y f
    apply CategoricalPullback.hom_ext
    · -- On first projections, unfold only the comparison functor and use the based-functor
      -- equality for `H` to rewrite its transported base map.
      change X.p.map f ≫ eqToHom (pushforwardPullbackTargetBase_eq u X Y H y) =
        eqToHom (pushforwardPullbackTargetBase_eq u X Y H x) ≫ (H.obj.map f).fst
      rw [pushforwardPullbackTargetMap_fst]
      rw [← Category.assoc, eqToHom_trans]
      simp only [eqToHom_refl, Category.id_comp]
    · -- On second projections, compute the localization lift on the unit morphism before
      -- applying the target-chart factorization lemma.
      change
        Floc.map ((pushforwardFibredCategoryUnit u X).map f) ≫
            pushforwardPullbackTargetChart u X Y H
              ((pushforwardFibredCategoryUnitPrelocalized u X).obj y) =
          pushforwardPullbackTargetChart u X Y H
              ((pushforwardFibredCategoryUnitPrelocalized u X).obj x) ≫
            (H.obj.map f).snd
      have hunitMap :
          Floc.map ((pushforwardFibredCategoryUnit u X).map f) =
            pushforwardPullbackTargetMap u X Y H
              ((pushforwardFibredCategoryUnitPrelocalized u X).map f) := by
        simpa [Floc, Fpre, pushforwardFibredCategoryUnit, Functor.comp_map] using
          localizationConstructionLift_map_Q
            (F := pushforwardPullbackTargetPrelocalizedFunctor u X Y H)
            (hF := hFpre)
            ((pushforwardFibredCategoryUnitPrelocalized u X).map f)
      rw [hunitMap]
      exact pushforwardPullbackTargetMap_fac u X Y H
        ((pushforwardFibredCategoryUnitPrelocalized u X).map f)
  · intro x
    refine IsHomLift.of_fac' (u ᵖ Y).p (𝟙 (X.p.obj x)) _ rfl
      (pushforwardPullbackTargetBase_eq u X Y H x).symm ?_
    change eqToHom (pushforwardPullbackTargetBase_eq u X Y H x) =
      eqToHom rfl ≫ 𝟙 (X.p.obj x) ≫
        eqToHom (pushforwardPullbackTargetBase_eq u X Y H x)
    simp

end Pushforward

end

end CategoryTheory
