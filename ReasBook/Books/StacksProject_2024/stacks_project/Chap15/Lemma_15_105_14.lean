import Mathlib
import StacksProject_2024.stacks_project.Chap10.Lemma_10_143_8
import StacksProject_2024.stacks_project.Chap10.Lemma_10_39_6
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_5
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_3
import StacksProject_2024.stacks_project.Chap10.Lemma_10_154_2
import StacksProject_2024.stacks_project.Chap15.Definition_15_105_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_105_7
import StacksProject_2024.stacks_project.Chap15.Lemma_15_45_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MorphismProperty
open CommRingCat
open scoped TensorProduct

universe u v w

namespace RingHom

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- An `R`-algebra map `f : R →+* S` is a filtered colimit of weakly étale `R`-algebras. This
thin source-facing wrapper hides the same-universe `ULift` bookkeeping needed to express the
canonical owner
`CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`. -/
abbrev IsFilteredColimitOfWeaklyEtale (f : R →+* S) : Prop :=
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1}
    (toMorphismProperty fun {R S} [CommRing R] [CommRing S] (f : R →+* S) ↦
      let _ : Algebra R S := f.toAlgebra
      Algebra.IsWeaklyEtale R S)
    (ofHom (algebraMap (ULift.{v} R) (ULift S)))

end

/-- Helper for Lemma 15.105.14: a stage property carried through
`RingHom.toMorphismProperty` is the underlying weakly étale algebra condition. -/
theorem filtered_colimit_stage_isWeaklyEtale
    {R S : CommRingCat.{w}} {f : R ⟶ S}
    (hf :
      (RingHom.toMorphismProperty
        (fun {R S} [CommRing R] [CommRing S] (f : R →+* S) ↦
          let _ : Algebra R S := f.toAlgebra
          Algebra.IsWeaklyEtale R S)) f) :
    let _ : Algebra R S := f.hom.toAlgebra
    Algebra.IsWeaklyEtale R S := by
  -- Unfold the bridge from ring-hom predicates to categorical morphism properties once.
  simpa [RingHom.toMorphismProperty] using hf

section UnderFlat

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat

/-- Helper for Lemma 15.105.14: turn the stage maps in an `ind` presentation into a functor to
the under-category over the fixed source ring. -/
private abbrev weaklyEtale_ind_underFunctor {A : CommRingCat.{u}} {J : Type u} [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D) :
    J ⥤ Under A :=
  { obj := fun j ↦ Under.mk (t.app j)
    map := fun {i j} g ↦ Under.homMk (D.map g) (by
      -- The `Under`-morphism condition is exactly the naturality square for the stage map `t`.
      simpa using (t.naturality g).symm) }

/-- Helper for Lemma 15.105.14: the target cocone of an `ind` presentation lifts canonically to
the corresponding cocone in the under-category. -/
private abbrev weaklyEtale_ind_underCocone {A B : CommRingCat.{u}} {J : Type u}
    [SmallCategory J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f) :
    Cocone (weaklyEtale_ind_underFunctor (A := A) D t) :=
  { pt := Under.mk f
    ι :=
      { app := fun j ↦ Under.homMk (s.app j) (hcompat j)
        naturality := by
          intro i j g
          -- Equality of `Under` morphisms reduces to equality of their right components.
          refine CategoryTheory.CommaMorphism.ext rfl ?_
          simpa using s.naturality g } }

/-- Helper for Lemma 15.105.14: if the underlying cocone in `CommRingCat` is colimiting, then the
lifted cocone in the under-category is also colimiting. -/
private noncomputable def weaklyEtale_ind_underCocone_isColimit_of_isColimit
    {A B : CommRingCat.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    (D : J ⥤ CommRingCat.{u}) (t : (Functor.const J).obj A ⟶ D)
    (s : D ⟶ (Functor.const J).obj B) (f : A ⟶ B)
    (hcompat : ∀ j : J, t.app j ≫ s.app j = f)
    (hs : IsColimit (Cocone.mk B s)) :
    IsColimit (weaklyEtale_ind_underCocone D t s f hcompat) := by
  classical
  refine IsColimit.mk ?_ ?_ ?_
  · intro c
    let j₀ : J := Classical.choice (CategoryTheory.IsFiltered.nonempty (C := J))
    refine Under.homMk (hs.desc ((Under.forget A).mapCocone c)) ?_
    -- The lifted desc morphism must respect the fixed source map; one stage equation reduces this
    -- to the ordinary colimit computation after forgetting from `Under`.
    change f ≫ hs.desc ((Under.forget A).mapCocone c) = c.pt.hom
    rw [← hcompat j₀]
    have hfac₀ :
        s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c) = (c.ι.app j₀).right := by
      simpa using hs.fac ((Under.forget A).mapCocone c) j₀
    have hdesc :
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c) =
          t.app j₀ ≫ (c.ι.app j₀).right := by
      calc
        (t.app j₀ ≫ s.app j₀) ≫ hs.desc ((Under.forget A).mapCocone c)
            = t.app j₀ ≫ (s.app j₀ ≫ hs.desc ((Under.forget A).mapCocone c)) := by
                simp [Category.assoc]
        _ = t.app j₀ ≫ (c.ι.app j₀).right := by
              exact congrArg (fun z ↦ t.app j₀ ≫ z) hfac₀
    exact hdesc.trans <| by
      simpa using (c.ι.app j₀).w.symm
  · intro c j
    -- After forgetting to rings, this is exactly the usual colimit fac equation on the `j`-th
    -- stage, and equality of under-morphisms is determined by the right component.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    simpa using hs.fac ((Under.forget A).mapCocone c) j
  · intro c m hm
    -- Uniqueness is checked after forgetting to rings, where `hs` already supplies the universal
    -- property.
    refine CategoryTheory.CommaMorphism.ext rfl ?_
    apply hs.hom_ext
    intro j
    have hmj :
        s.app j ≫ m.right = (c.ι.app j).right := by
      simpa [weaklyEtale_ind_underCocone] using
        congrArg CategoryTheory.CommaMorphism.right (hm j)
    have hfac :
        s.app j ≫ hs.desc ((Under.forget A).mapCocone c) = (c.ι.app j).right := by
      simpa using hs.fac ((Under.forget A).mapCocone c) j
    exact hmj.trans hfac.symm

/-- Helper for Lemma 15.105.14: forget a commutative ring under `A` to its underlying
`A`-module. -/
private abbrev under_forget_to_module (A : CommRingCat.{u}) : Under A ⥤ ModuleCat A where
  obj B := ModuleCat.of A B
  map f := ModuleCat.ofHom (CommRingCat.toAlgHom f).toLinearMap

/-- Helper for Lemma 15.105.14: an object under `CommRingCat.of A` carries the canonical
`A`-module structure induced by its structure map. -/
private instance under_module (A : Type u) [CommRing A] (B : Under (CommRingCat.of A)) :
    Module A B := by
  let _ : Algebra A B.right := B.hom.hom.toAlgebra
  infer_instance

/-- Helper for Lemma 15.105.14: a filtered colimit in `Under (CommRingCat.of A)` is flat once
every stage is flat over the fixed base ring `A`. -/
private lemma under_colimit_flat_of_stagewise_flat {A : Type u} [CommRing A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of A)) (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat A (F.obj j)] :
    Module.Flat A c.pt.right := by
  let cM := (under_forget_to_module (CommRingCat.of A)).mapCocone c
  letI : ∀ j, Module.Flat A ((F ⋙ under_forget_to_module (CommRingCat.of A)).obj j) :=
    fun j ↦ by
      simpa [under_forget_to_module] using (inferInstance : Module.Flat A (F.obj j))
  have hcM : IsColimit cM := by
    -- Forget the under-diagram to additive groups, where the relevant filtered colimits are
    -- preserved, and then reflect the resulting colimit back to `ModuleCat`.
    apply isColimitOfReflects (forget₂ (ModuleCat A) AddCommGrpCat)
    simpa [under_forget_to_module] using
      (isColimitOfPreserves
        (CategoryTheory.Under.forget (CommRingCat.of A) ⋙
          forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) hc)
  -- Apply the Chapter 10 filtered-colimit flatness theorem to the transported module diagram.
  simpa using
    flat_of_isColimit_filtered_system
      (F := F ⋙ under_forget_to_module (CommRingCat.of A)) cM hcM

end UnderFlat

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}

/-- Helper for Lemma 15.105.14: a filtered colimit of weakly étale algebras is flat over the
base ring. -/
theorem IsFilteredColimitOfWeaklyEtale.flat
    (h : f.IsFilteredColimitOfWeaklyEtale) :
    f.Flat := by
  let _ : Algebra R S := f.toAlgebra
  let _ : Algebra R (ULift S) := ULift.algebra
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  -- Unpack the same-universe `ind` witness once and keep the chosen presentation fixed.
  dsimp [RingHom.IsFilteredColimitOfWeaklyEtale] at h
  rcases h with ⟨J, _, _, D, t, s, hs, hstage⟩
  let F := weaklyEtale_ind_underFunctor (A := CommRingCat.of (ULift.{v} R)) D t
  have hsUnder :
      CategoryTheory.Limits.IsColimit
        (weaklyEtale_ind_underCocone D t s
          (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
          (fun j ↦ (hstage j).2)) := by
    exact weaklyEtale_ind_underCocone_isColimit_of_isColimit
      (D := D) (t := t) (s := s)
      (f := CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
      (hcompat := fun j ↦ (hstage j).2) hs
  letI : ∀ j, Module.Flat (ULift.{v} R) (F.obj j) :=
    fun j ↦ by
      let _ : Algebra (ULift.{v} R) (D.obj j) := (t.app j).hom.toAlgebra
      have hweak :
          Algebra.IsWeaklyEtale (ULift.{v} R) (D.obj j) :=
        by
          simpa [RingHom.toMorphismProperty] using (hstage j).1
      have hflatStageHom :
          (algebraMap (ULift.{v} R) (D.obj j)).Flat := by
        simpa [RingHom.algebraMap_toAlgebra] using hweak.flat
      have hflatStage :
          Module.Flat (ULift.{v} R) (D.obj j) :=
        RingHom.flat_algebraMap_iff.mp hflatStageHom
      simpa [F, weaklyEtale_ind_underFunctor] using hflatStage
  have hflatULift : Module.Flat (ULift.{v} R) (ULift S) := by
    -- The `Under` colimit now matches the source-proof presentation exactly, so the stagewise
    -- weakly-étale flatness theorem applies without further reindexing.
    simpa [F, weaklyEtale_ind_underCocone] using
      under_colimit_flat_of_stagewise_flat
        (A := ULift.{v} R) F
        (weaklyEtale_ind_underCocone D t s
          (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))
          (fun j ↦ (hstage j).2))
        hsUnder
  have hflatUp : (algebraMap (ULift.{v} R) (ULift S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr hflatULift
  have hsource :
      ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv.symm : R ≃+* ULift.{v} R).bijective
  have htarget :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).Flat :=
    RingHom.Flat.of_bijective (ULift.ringEquiv : ULift S ≃+* S).bijective
  have hcomp :
      (((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom))).Flat := by
    exact RingHom.Flat.comp (RingHom.Flat.comp hsource hflatUp) htarget
  have hEq :
      ((ULift.ringEquiv : ULift S ≃+* S).toRingHom).comp
        ((algebraMap (ULift.{v} R) (ULift S)).comp
          ((ULift.ringEquiv.symm : R ≃+* ULift.{v} R).toRingHom)) = f := by
    ext x
    rfl
  rw [← hEq]
  exact hcomp

end

end RingHom

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

open CategoryTheory Limits

/-- Helper for Lemma 15.105.14: for a localization `B = S⁻¹A`, the canonical localization
identification `B ⊗[A] B ≃ₐ[B] B` agrees with the tensor-square multiplication map. -/
theorem isLocalization_algebraLid_toRingHom_eq
    (M : Submonoid A) [IsLocalization M B] :
    ((IsLocalization.algebraLid M B B).toAlgHom.restrictScalars A).toRingHom =
      (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom := by
  -- Compare the two algebra maps on the two canonical tensor-product generators.
  letI : TensorProduct.CompatibleSMul A B B B :=
    IsLocalization.tensorProduct_compatibleSMul M B B B
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both maps preserve zero.
    simp
  · intro b₁ b₂
    -- The localization identification multiplies pure tensors exactly as `lmul'`.
    simpa [IsLocalization.algebraLid, Algebra.smul_def,
      Algebra.TensorProduct.lmul'_apply_tmul] using
      (Algebra.TensorProduct.lidOfCompatibleSMul_tmul A B B b₁ b₂).symm
  · intro x y hx hy
    -- Additivity reduces the claim to the induction hypotheses.
    simpa using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Lemma 15.105.14: the tensor-square multiplication map
`C ⊗[A] C → C` is a `C`-algebra hom for the left `C`-algebra structure on the tensor product. -/
private theorem tensor_square_multiplication_left_commutes
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (c : C) :
    (Algebra.TensorProduct.lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom
        (algebraMap C (C ⊗[A] C) c) =
      algebraMap C C c := by
  -- The left `C`-algebra map is the tensor inclusion `c ↦ c ⊗ 1`, and `lmul'` multiplies it back
  -- to `c`.
  change
    (Algebra.TensorProduct.lmul' A)
        ((Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] C) c) =
      c
  simp [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lmul'_apply_tmul]

/-- Helper for Lemma 15.105.14: the multiplication map `C ⊗[A] C → C` viewed over the left
tensor factor as base ring `C`. -/
private abbrev tensor_square_multiplication_leftAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C] :
    C ⊗[A] C →ₐ[C] C :=
  { toRingHom := (Algebra.TensorProduct.lmul' A : C ⊗[A] C →ₐ[A] C).toRingHom
    commutes' := tensor_square_multiplication_left_commutes (A := A) (C := C) }

/-- Helper for Lemma 15.105.14: after canceling the base change
`B ⊗[C] (C ⊗[A] C) ≃ B ⊗[A] C` and then collapsing `B ⊗[C] C ≃ B`, the base change of the
tensor-square multiplication map on `C` becomes the stage multiplication map `B ⊗[A] C → B`. -/
private theorem tensor_stage_baseChange_mul_eq_stage_multiplication
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B] :
    ((Algebra.TensorProduct.rid C B B).toRingHom.comp
        (Algebra.TensorProduct.map (AlgHom.id C B)
          (tensor_square_multiplication_leftAlgHom (A := A) (C := C))).toRingHom) =
      ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
        (fun _ _ ↦ Commute.all _ _)).toRingHom).comp
        (Algebra.TensorProduct.cancelBaseChange A C B B C).toRingHom := by
  -- Compare the two transported maps on pure tensors in `B ⊗[C] (C ⊗[A] C)`.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both ring maps preserve zero.
    simp
  · intro b z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · -- The inner tensor factor is additive, so zero is immediate.
      simp
    · intro c₁ c₂
      -- On a pure tensor `b ⊗ (c₁ ⊗ c₂)`, the base-change map multiplies `c₁` into `b` and keeps
      -- `c₂` as the remaining tensor factor.
      change
        (Algebra.TensorProduct.rid C B B)
            ((Algebra.TensorProduct.map (AlgHom.id C B)
                (tensor_square_multiplication_leftAlgHom (A := A) (C := C)))
              (b ⊗ₜ[C] (c₁ ⊗ₜ[A] c₂))) =
          (Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
            (fun _ _ ↦ Commute.all _ _))
            ((Algebra.TensorProduct.cancelBaseChange A C B B C)
              (b ⊗ₜ[C] (c₁ ⊗ₜ[A] c₂)))
      simp [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
        Algebra.TensorProduct.lift_tmul]
      simpa [Algebra.smul_def, map_mul, mul_assoc, mul_comm, mul_left_comm]
    · intro z₁ z₂ hz₁ hz₂
      -- Additivity in the inner tensor factor reduces to the induction hypotheses.
      rw [TensorProduct.tmul_add]
      simpa [RingHom.comp_apply, map_add] using congrArg₂ HAdd.hAdd hz₁ hz₂
  · intro x y hx hy
    -- Additivity in the outer tensor factor reduces to the induction hypotheses.
    calc
      ((Algebra.TensorProduct.rid C B B).toRingHom.comp
            (Algebra.TensorProduct.map (AlgHom.id C B)
              (tensor_square_multiplication_leftAlgHom (A := A) (C := C))).toRingHom)
          (x + y)
          = ((Algebra.TensorProduct.rid C B B).toRingHom.comp
                (Algebra.TensorProduct.map (AlgHom.id C B)
                  (tensor_square_multiplication_leftAlgHom (A := A) (C := C))).toRingHom) x +
              ((Algebra.TensorProduct.rid C B B).toRingHom.comp
                (Algebra.TensorProduct.map (AlgHom.id C B)
                  (tensor_square_multiplication_leftAlgHom (A := A) (C := C))).toRingHom) y := by
                simp [RingHom.comp_apply]
      _ = ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
              (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
            (Algebra.TensorProduct.cancelBaseChange A C B B C).toRingHom) x +
            ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
              (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
            (Algebra.TensorProduct.cancelBaseChange A C B B C).toRingHom) y := by
              rw [hx, hy]
      _ = ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
              (fun _ _ ↦ Commute.all _ _)).toRingHom.comp
            (Algebra.TensorProduct.cancelBaseChange A C B B C).toRingHom)
            (x + y) := by
              simp [RingHom.comp_apply]

/-- Helper for Lemma 15.105.14: each base-changed stage multiplication map
`B ⊗[A] C → B` is flat when `A → C` is weakly étale. -/
private theorem tensor_stage_to_base_flat
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra C B]
    [IsScalarTower A C B]
    (hAC : Algebra.IsWeaklyEtale A C) :
    let _ : Algebra (B ⊗[A] C) B :=
      (Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
        (fun _ _ ↦ Commute.all _ _)).toAlgebra
    Module.Flat (B ⊗[A] C) B := by
  let stageMul : B ⊗[A] C →ₐ[A] B :=
    Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
      (fun _ _ ↦ Commute.all _ _)
  let baseChangeMul : B ⊗[C] (C ⊗[A] C) →ₐ[C] B ⊗[C] C :=
    Algebra.TensorProduct.map (AlgHom.id C B)
      (tensor_square_multiplication_leftAlgHom (A := A) (C := C))
  let cancelStage : B ⊗[C] (C ⊗[A] C) ≃ₐ[B] B ⊗[A] C :=
    Algebra.TensorProduct.cancelBaseChange A C B B C
  -- First base change the flat multiplication map `C ⊗[A] C → C` along `C → B`.
  have hidFlat : (AlgHom.id C B : B →ₐ[C] B).Flat := by
    simpa using RingHom.Flat.id B
  have hbaseChangeFlat : baseChangeMul.toRingHom.Flat := by
    simpa [baseChangeMul] using
      (RingHom.Flat.tensorProductMap
        (A := B) (B := C ⊗[A] C) (C := B) (D := C)
        hidFlat
        (show
            (tensor_square_multiplication_leftAlgHom (A := A) (C := C)).toRingHom.Flat
          from hAC.flat_tensorSquareMultiplication))
  have hridFlat : (Algebra.TensorProduct.rid C B B).toRingHom.Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.rid C B B).bijective
  have hcancelFlat : cancelStage.symm.toRingHom.Flat :=
    RingHom.Flat.of_bijective cancelStage.symm.bijective
  have htransported :
      (((Algebra.TensorProduct.rid C B B).toRingHom.comp baseChangeMul.toRingHom).comp
          cancelStage.symm.toRingHom).Flat := by
    -- Compose the base-changed flat map with the two canonical tensor equivalences.
    exact RingHom.Flat.comp hcancelFlat (RingHom.Flat.comp hbaseChangeFlat hridFlat)
  have hcancelComp :
      cancelStage.toRingHom.comp cancelStage.symm.toRingHom = RingHom.id (B ⊗[A] C) := by
    apply DFunLike.ext
    intro x
    exact cancelStage.apply_symm_apply x
  have hstageEq :
      (((Algebra.TensorProduct.rid C B B).toRingHom.comp baseChangeMul.toRingHom).comp
          cancelStage.symm.toRingHom) =
        stageMul.toRingHom := by
    -- Route correction: prove the forward comparison once, then postcompose with the inverse
    -- tensor equivalence to land on the actual stage multiplication.
    rw [tensor_stage_baseChange_mul_eq_stage_multiplication (A := A) (B := B) (C := C)]
    rw [RingHom.comp_assoc]
    rw [hcancelComp]
    apply DFunLike.ext
    intro x
    rfl
  have hstageFlat : stageMul.toRingHom.Flat := by
    rw [← hstageEq]
    exact htransported
  let _ : Algebra (B ⊗[A] C) B := stageMul.toAlgebra
  have halgebraMapFlat : (algebraMap (B ⊗[A] C) B).Flat := by
    -- Convert the transported ring-hom flatness into the canonical algebra-map formulation.
    simpa [RingHom.algebraMap_toAlgebra, stageMul] using hstageFlat
  exact RingHom.flat_algebraMap_iff.mp halgebraMapFlat

/-- Helper for Lemma 15.105.14: mapping the left tensor factor through a stage map and then
multiplying in `B ⊗[A] B` recovers the corresponding stage multiplication map
`X ⊗[A] B → B`. -/
private theorem tensor_stage_map_comp_lmul_eq_stage_multiplication
    {X : Type u} [CommRing X] [Algebra A X] [Algebra X B] [IsScalarTower A X B] :
    ((Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom).comp
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X B) (AlgHom.id A B)).toRingHom =
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A X B) (AlgHom.id A B)
        (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  -- Reduce the comparison of the two tensor-stage maps to pure tensors in `X ⊗[A] B`.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both ring maps preserve zero.
    simp
  · intro x b
    -- On pure tensors, both maps send `x ⊗ b` to the image of `x` in `B` multiplied by `b`.
    simp [RingHom.comp_apply, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lmul'_apply_tmul]
  · intro x y hx hy
    -- Additivity reduces the general tensor to the induction hypotheses.
    simpa [RingHom.comp_apply] using congrArg₂ HAdd.hAdd hx hy

section TensorStagePushout

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 15.105.14: pushing an `A`-algebra stage `X` forward along `A → B`
identifies the resulting under-category pushout object with the tensor stage `X ⊗[A] B`. -/
private noncomputable def under_pushout_obj_iso_tensor_stage
    {X : Type u} [CommRing X] [Algebra A X] :
    ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A X)))) ≅
      Under.mk (ofHom (algebraMap B (X ⊗[A] B))) := by
  -- Rewrite the pushed-out under-object as the ordinary categorical pushout.
  rw [Under.pushout_obj]
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B)))
        (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The tensor product satisfies the same universal property, so the two under-objects coincide.
  refine Under.isoMk hpush.isoPushout.symm ?_
  simp

/-- Helper for Lemma 15.105.14: after identifying the pushed-out stage object with `X ⊗[A] B`,
the left pushout generator is the canonical tensor inclusion from `X`. -/
@[reassoc (attr := simp)]
private lemma under_pushout_inl_tensor_stage_hom
    {X : Type u} [CommRing X] [Algebra A X] :
    pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
      ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := X)).hom).right =
        ofHom (algebraMap X (X ⊗[A] B)) := by
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B)))
        (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The comparison morphism preserves the universal left leg of the pushout.
  simpa [under_pushout_obj_iso_tensor_stage, hpush] using hpush.inl_isoPushout_inv

/-- Helper for Lemma 15.105.14: after identifying the pushed-out stage object with `X ⊗[A] B`,
the right pushout generator is the canonical tensor inclusion from `B`. -/
@[reassoc (attr := simp)]
private lemma under_pushout_inr_tensor_stage_hom
    {X : Type u} [CommRing X] [Algebra A X] :
    pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
      ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := X)).hom).right =
        ofHom (algebraMap B (X ⊗[A] B)) := by
  let hpush :
      IsPushout (ofHom (algebraMap A X)) (ofHom (algebraMap A B))
        (ofHom (algebraMap X (X ⊗[A] B)))
        (ofHom (algebraMap B (X ⊗[A] B))) :=
    CommRingCat.isPushout_of_isPushout A X B (X ⊗[A] B)
  -- The comparison morphism preserves the universal right leg of the pushout.
  simpa [under_pushout_obj_iso_tensor_stage, hpush] using hpush.inr_isoPushout_inv

/-- Helper for Lemma 15.105.14: transporting a morphism in the pushed-out under-diagram agrees
with the concrete tensor-stage map induced by the original stage morphism. -/
private lemma under_pushout_map_eq_tensor_stage_map
    {X Y : Type u} [CommRing X] [CommRing Y]
    [Algebra A X] [Algebra A Y] [Algebra X Y] [IsScalarTower A X Y] :
    let eX : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A X)))) ≅
          of (X ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := X))
    let eY : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (ofHom (algebraMap A Y)))) ≅
          of (Y ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y))
    (Under.forget (of B)).map
        ((Under.pushout (ofHom (algebraMap A B))).map
          (Under.homMk (ofHom (algebraMap X Y)) (by
            dsimp
            ext x
            simpa [CommRingCat.hom_comp, RingHom.comp_apply] using
              congrArg (fun f : A →+* Y ↦ f x) (IsScalarTower.algebraMap_eq A X Y).symm))) ≫
      eY.hom =
        eX.hom ≫
          ofHom (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
  have hsq_pushout :
      ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) =
        ofHom (algebraMap A B) ≫
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
    -- First rewrite the left side using the scalar-tower identity, then apply the pushout square.
    calc
      ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) =
        ofHom (algebraMap A Y) ≫
          pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
          simpa [Category.assoc, CommRingCat.hom_comp] using
            congrArg
              (fun k ↦ k ≫ pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (show ofHom (algebraMap A X) ≫ ofHom (algebraMap X Y) =
                  ofHom (algebraMap A Y) by
                apply CommRingCat.hom_ext
                ext x
                simpa [CommRingCat.hom_comp, RingHom.comp_apply] using
                  congrArg (fun f : A →+* Y ↦ f x) (IsScalarTower.algebraMap_eq A X Y).symm)
      _ = ofHom (algebraMap A B) ≫
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) := by
          simpa using
            (pushout.condition (f := ofHom (algebraMap A Y)) (g := ofHom (algebraMap A B)))
  -- Compare the transported morphisms after precomposing with the two pushout generators.
  dsimp
  apply pushout.hom_ext
  · have hdesc :
        pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            pushout.desc
              (ofHom (algebraMap X Y) ≫
                pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (by
                simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
            ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right =
          ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
              ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right := by
      -- The pushed-out map is defined by `pushout.desc`, so the `inl` leg computes directly.
      simpa using
        (pushout.inl_desc_assoc
          (ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right))
    calc
      pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
          pushout.desc
            (ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right
          = ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
                ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right := hdesc
      _ = ofHom (algebraMap X Y) ≫ ofHom (algebraMap Y (Y ⊗[A] B)) := by
        exact congrArg (fun k ↦ ofHom (algebraMap X Y) ≫ k) <| by
          simpa [CommRingCat.hom_comp] using
            (under_pushout_inl_tensor_stage_hom (A := A) (B := B) (X := Y))
      _ = pushout.inl (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := X)).hom).right ≫
            ofHom
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
        rw [under_pushout_inl_tensor_stage_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        simp [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  · have hdesc :
        pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            pushout.desc
              (ofHom (algebraMap X Y) ≫
                pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
              (by
                simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
            ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right =
          pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
            ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right := by
      -- The `inr` leg is unchanged by the pushed-out morphism.
      simpa using
        (pushout.inr_desc_assoc
          (ofHom (algebraMap X Y) ≫
            pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
          (by
            simpa [CommRingCat.hom_comp] using hsq_pushout)
          (((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right))
    calc
      pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
          pushout.desc
            (ofHom (algebraMap X Y) ≫
              pushout.inl (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)))
            (by
              simpa [CommRingCat.hom_comp] using hsq_pushout) ≫
          ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right
          = pushout.inr (ofHom (algebraMap A Y)) (ofHom (algebraMap A B)) ≫
              ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := Y)).hom).right := hdesc
      _ = ofHom (algebraMap B (Y ⊗[A] B)) := by
        simpa [CommRingCat.hom_comp] using
          (under_pushout_inr_tensor_stage_hom (A := A) (B := B) (X := Y))
      _ = pushout.inr (ofHom (algebraMap A X)) (ofHom (algebraMap A B)) ≫
            ((under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := X)).hom).right ≫
            ofHom
              (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B)) := by
        rw [under_pushout_inr_tensor_stage_hom_assoc]
        apply CommRingCat.hom_ext
        ext x
        change (1 : Y) ⊗ₜ[A] x =
          (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A X Y) (AlgHom.id A B))
            ((1 : X) ⊗ₜ[A] x)
        simp [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- Helper for Lemma 15.105.14: each pushed-out cocone leg in the filtered-colimit presentation
matches the explicit right-tensor cocone leg induced by the corresponding stage map `D.obj j → B`.
-/
private lemma right_tensor_cocone_leg_eq_pushout_map
    {J : Type u} [SmallCategory J]
    {D : J ⥤ CommRingCat.{u}}
    (t : (Functor.const J).obj (CommRingCat.of A) ⟶ D)
    (s : D ⟶ (Functor.const J).obj (CommRingCat.of B))
    (hcompat : ∀ j : J, t.app j ≫ s.app j = ofHom (algebraMap A B))
    (j : J) :
    let _ : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
    let _ : Algebra (D.obj j) B := (s.app j).hom.toAlgebra
    let _ : IsScalarTower A (D.obj j) B := by
      refine IsScalarTower.of_algebraMap_eq' ?_
      simpa [CommRingCat.hom_comp] using (congrArg CommRingCat.Hom.hom (hcompat j)).symm
    let eStage : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj (Under.mk (t.app j))) ≅
          of (D.obj j ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := D.obj j))
    let eTarget : (Under.forget (of B)).obj
        ((Under.pushout (ofHom (algebraMap A B))).obj
          (Under.mk (ofHom (algebraMap A B)))) ≅
          of (B ⊗[A] B) :=
      (Under.forget (of B)).mapIso
        (under_pushout_obj_iso_tensor_stage (A := A) (B := B) (X := B))
    (Under.forget (of B)).map
        ((Under.pushout (ofHom (algebraMap A B))).map
          (Under.homMk (s.app j) (hcompat j))) ≫
      eTarget.hom =
        eStage.hom ≫
          ofHom
            (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (D.obj j) B) (AlgHom.id A B)) := by
  let _ : Algebra A (D.obj j) := (t.app j).hom.toAlgebra
  let _ : Algebra (D.obj j) B := (s.app j).hom.toAlgebra
  let _ : IsScalarTower A (D.obj j) B := by
    -- The chosen stage map `s.app j` is an `A`-algebra morphism by the cocone compatibility.
    refine IsScalarTower.of_algebraMap_eq' ?_
    simpa [CommRingCat.hom_comp] using (congrArg CommRingCat.Hom.hom (hcompat j)).symm
  -- This is the stagewise specialization of the general pushout-to-tensor comparison lemma above.
  simpa using
    (under_pushout_map_eq_tensor_stage_map (A := A) (B := B) (X := D.obj j) (Y := B))

end TensorStagePushout

section CommRightStage

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 15.105.14: swapping `C ⊗[A] B` to `B ⊗[A] C` and then applying the left
tensor-stage multiplication agrees with the native right-tensor stage multiplication
`C ⊗[A] B → B`. -/
private theorem tensor_stage_commRight_comp_eq_stage_multiplication
    {C : Type u} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] :
    ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
      (fun _ _ ↦ Commute.all _ _)).toRingHom).comp
        (Algebra.TensorProduct.commRight A C B).toRingEquiv.toRingHom =
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A C B) (AlgHom.id A B)
        (fun _ _ ↦ Commute.all _ _)).toRingHom := by
  -- Compare the two tensor-stage multiplications on pure tensors; `commRight` only swaps factors.
  apply RingHom.ext
  intro x
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · -- Both ring maps preserve zero.
    simp
  · intro c b
    -- On a pure tensor `c ⊗ b`, both composites multiply the image of `c` in `B` by `b`.
    change
      (Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
        (fun _ _ ↦ Commute.all _ _)) ((Algebra.TensorProduct.commRight A C B) (c ⊗ₜ[A] b)) =
        (algebraMap C B) c * b
    simp [Algebra.TensorProduct.lift_tmul, mul_comm]
  · intro x y hx hy
    -- Additivity reduces the general tensor to the induction hypotheses.
    simpa [RingHom.comp_apply] using congrArg₂ HAdd.hAdd hx hy

/-- Helper for Lemma 15.105.14: a stage map `g : C → B` compatible with the fixed `A`-algebra
structures induces the expected scalar tower `A → C → B`. -/
private theorem tensor_stage_isScalarTower
    {C : Type u} [CommRing C] [Algebra A C]
    (g : C →+* B) (hcompat : g.comp (algebraMap A C) = algebraMap A B) :
    let _ : Algebra C B := g.toAlgebra
    IsScalarTower A C B := by
  let _ : Algebra C B := g.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' hcompat.symm

/-- Helper for Lemma 15.105.14: after transporting across `commRight`, each tensor stage map
`C ⊗[A] B → B` is flat whenever `A → C` is weakly étale and the structural map `C → B`
respects the `A`-algebra structures. -/
private theorem stage_right_tensor_flat
    {C : Type u} [CommRing C] [Algebra A C]
    (g : C →+* B) (hcompat : g.comp (algebraMap A C) = algebraMap A B)
    (hC : Algebra.IsWeaklyEtale A C) :
    let _ : Algebra C B := g.toAlgebra
    let _ : IsScalarTower A C B := tensor_stage_isScalarTower (A := A) (B := B) g hcompat
    let _ : Algebra (C ⊗[A] B) B :=
      (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A C B) (AlgHom.id A B)
        (fun _ _ ↦ Commute.all _ _)).toAlgebra
    Module.Flat (C ⊗[A] B) B := by
  let _ : Algebra C B := g.toAlgebra
  let _ : IsScalarTower A C B := tensor_stage_isScalarTower (A := A) (B := B) g hcompat
  let _ : Algebra (C ⊗[A] B) B :=
    (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A C B) (AlgHom.id A B)
      (fun _ _ ↦ Commute.all _ _)).toAlgebra
  let _ : Algebra (B ⊗[A] C) B :=
    (Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
      (fun _ _ ↦ Commute.all _ _)).toAlgebra
  -- First prove flatness for the left-tensor stage `B ⊗[A] C → B`.
  have hleftModule : Module.Flat (B ⊗[A] C) B :=
    tensor_stage_to_base_flat (A := A) (B := B) (C := C) hC
  have hleftAlg :
      ((Algebra.TensorProduct.lift (AlgHom.id A B) (IsScalarTower.toAlgHom A C B)
        (fun _ _ ↦ Commute.all _ _)).toRingHom).Flat := by
    -- Convert the already-proved module flatness into flatness of the corresponding algebra map.
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.flat_algebraMap_iff.mpr hleftModule)
  have hcomm :
      ((Algebra.TensorProduct.commRight A C B).toRingEquiv.toRingHom).Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.commRight A C B).bijective
  have hrightAlg :
      ((Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A C B) (AlgHom.id A B)
        (fun _ _ ↦ Commute.all _ _)).toRingHom).Flat := by
    -- Transport the left-tensor flatness across `commRight`.
    rw [← tensor_stage_commRight_comp_eq_stage_multiplication (A := A) (B := B) (C := C)]
    exact RingHom.Flat.comp hcomm hleftAlg
  have hrightAlgMap : (algebraMap (C ⊗[A] B) B).Flat := by
    -- The right-stage multiplication map is the algebra map for the local tensor-stage structure.
    simpa [RingHom.algebraMap_toAlgebra] using hrightAlg
  -- Convert the transported algebra-map flatness back to the module statement.
  exact RingHom.flat_algebraMap_iff.mp hrightAlgMap

end CommRightStage

/- Domain-style sampling for Lemma 15.105.14:
- primary domain: weakly étale commutative algebra and filtered-colimit presentations of ring maps;
- sampled owner declarations:
  `Algebra.IsWeaklyEtale`,
  `CategoryTheory.MorphismProperty.ind`,
  `RingHom.toMorphismProperty`,
  `RingHom.IsFilteredColimitOfWeaklyEtale`,
  `RingHom.algebraMap_isFilteredColimitOfEtale_of_isColimit`;
- best owner abstraction: the filtered-colimit hypothesis is the source-facing ring-hom owner
  `(algebraMap A B).IsFilteredColimitOfWeaklyEtale`, whose hidden core/canonical content is
  `CategoryTheory.MorphismProperty.ind (RingHom.toMorphismProperty (fun f ↦ Algebra.IsWeaklyEtale _ _))`;
- primitive data: the owner class `Algebra.IsWeaklyEtale` on each stage map;
- derived API: the source-facing closure statement that the colimit map `A → B` is weakly étale.

This file should therefore expose the filtered-colimit hypothesis through the ring-hom owner
`RingHom.IsFilteredColimitOfWeaklyEtale`, rather than through a raw `toMorphismProperty ... .ind`
term in theorem statements.
-/

-- Proof sketch: a localization map is étale by the canonical mathlib instance
-- `Algebra.Etale.of_isLocalizationAway` in the away-localization case, and more generally the
-- Stacks lemma allows one to view localizations as weakly étale directly. The weakly étale
-- statement then follows from the defining flatness properties of localization.
/-- Lemma 15.105.14 (1): if `B` is a localization of `A`, then the ring map `A → B` is weakly
étale. -/
theorem isWeaklyEtale_of_isLocalization (M : Submonoid A) [IsLocalization M B] :
    Algebra.IsWeaklyEtale A B := by
  -- A localization is flat over the base, and its tensor square collapses back to itself.
  refine
    { moduleFlat := by
        simpa using (IsLocalization.flat B M : Module.Flat A B)
      flat_tensorSquareMultiplication := by
        have hEq :
            ((IsLocalization.algebraLid M B B).toAlgHom.restrictScalars A).toRingHom =
              (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).toRingHom :=
          isLocalization_algebraLid_toRingHom_eq (A := A) (B := B) M
        have hflat :
            (((IsLocalization.algebraLid M B B).toAlgHom.restrictScalars A).toRingHom).Flat :=
          RingHom.Flat.of_bijective
            (by
              simpa using
                (IsLocalization.algebraLid M B B).bijective)
        rw [hEq] at hflat
        exact hflat }

/-- Lemma 15.105.14 (2): every étale ring map `A → B` is weakly étale. -/
instance isWeaklyEtale_of_etale [Algebra.Etale A B] :
    Algebra.IsWeaklyEtale A B := by
  -- Étaleness gives flatness of the structure map, and the tensor-square multiplication map is
  -- étale over the common base by Lemma `10.143.8`.
  refine
    { moduleFlat := by
        infer_instance
      flat_tensorSquareMultiplication := by
        let _ : Algebra.Etale B (B ⊗[A] B) := inferInstance
        let _ : Algebra.Etale A (B ⊗[A] B) :=
          Algebra.Etale.comp (R := A) (A := B) (B := B ⊗[A] B)
        let _ : Algebra B (B ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
        let _ : Algebra A (B ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
        let _ : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toAlgebra
        let _ : Algebra.Etale (B ⊗[A] B) B := Algebra.etale_of_etale_over_common_base
        have halg : (algebraMap (B ⊗[A] B) B).Flat := by
          exact RingHom.flat_algebraMap_iff.mpr inferInstance
        simpa [RingHom.algebraMap_toAlgebra] using halg }

-- Proof sketch: filtered colimits preserve flatness of the structural map `A → B`, and the
-- tensor-square multiplication map of the colimit is the filtered colimit of the corresponding
-- tensor-square multiplication maps of the stages. Since each stage is weakly étale, both
-- flatness conditions pass to the colimit.
/-- Helper for Lemma 15.105.14: the tensor-square multiplication map of a filtered colimit of
weakly étale `A`-algebras is flat. -/
private theorem tensorSquare_flat_of_isFilteredColimitOfWeaklyEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfWeaklyEtale) :
    (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).Flat := by
  -- TODO for Lemma 15.105.14: after unpacking the `ULift`-level filtered-colimit presentation,
  -- push the under-cocone out along `A → B`, identify the forgotten pushout cocone with the
  -- explicit right-tensor stage diagram `j ↦ D.obj j ⊗[A] B`, and then apply
  -- `flat_of_stagewise_restrictScalars_flat` using `stage_right_tensor_flat` on each stage.
  let _ : (algebraMap A B).IsFilteredColimitOfWeaklyEtale := hcolim
  sorry

/-- Lemma 15.105.14 (3): a filtered colimit of weakly étale `A`-algebras is weakly étale over
`A`. -/
theorem isWeaklyEtale_of_isFilteredColimitOfWeaklyEtale
    (hcolim : (algebraMap A B).IsFilteredColimitOfWeaklyEtale) :
    Algebra.IsWeaklyEtale A B := by
  refine
    { moduleFlat := ?_
      flat_tensorSquareMultiplication := ?_ }
  · -- The structure-map flatness is exactly the filtered-colimit flatness helper proved above.
    exact RingHom.flat_algebraMap_iff.mp <|
      RingHom.IsFilteredColimitOfWeaklyEtale.flat hcolim
  · -- The remaining flatness clause is the dedicated tensor-square colimit helper above.
    exact tensorSquare_flat_of_isFilteredColimitOfWeaklyEtale (A := A) (B := B) hcolim

end
