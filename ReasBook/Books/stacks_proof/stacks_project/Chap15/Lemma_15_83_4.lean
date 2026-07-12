import Mathlib
import StacksProject_2024.Chap10.Lemma_10_168_1
import StacksProject_2024.Chap15.Definition_15_83_1
import StacksProject_2024.Chap15.Example_15_64_5
import StacksProject_2024.Chap15.Lemma_15_82_6
import StacksProject_2024.Chap15.Lemma_15_82_12
import StacksProject_2024.Chap15.Lemma_15_83_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped DerivedTensorProduct TensorProduct

namespace Algebra

/-- Helper for Lemma 15.83.4: a linear equivalence gives an isomorphism in `ModuleCat`. -/
private def moduleCat_iso_of_linearEquiv
    {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    ModuleCat.of R M ≅ ModuleCat.of R N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap

/-- Helper for Lemma 15.83.4: restriction of scalars commutes with the degree-zero derived
object. -/
private noncomputable def restrictScalars_single0_iso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (M : ModuleCat B) :
    ((Functor.mapDerivedCategory (ModuleCat.restrictScalars f)).obj
      (ModuleCat.single0Functor.obj M)) ≅
      ModuleCat.single0Functor.obj ((ModuleCat.restrictScalars f).obj M) :=
  (((Functor.mapDerivedCategory (ModuleCat.restrictScalars f)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M)) ≪≫
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor (ModuleCat.restrictScalars f) (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      ((ModuleCat.restrictScalars f).obj M)).symm)

/-- Helper for Lemma 15.83.4: relative pseudo-coherence is invariant under isomorphism of
bundled modules. -/
private theorem moduleCat_isPseudoCoherentRelativeTo_of_iso
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {M N : ModuleCat A} (e : M ≅ N) :
    M.IsPseudoCoherentRelativeTo R ↔ N.IsPseudoCoherentRelativeTo R := by
  let P : ObjectProperty (DerivedCategory (ModuleCat A)) := fun K ↦ K.IsPseudoCoherentRelativeTo R
  constructor
  · intro hM
    -- Transport relative pseudo-coherence across the induced isomorphism of degree-zero objects.
    exact P.prop_of_iso (ModuleCat.single0Functor.mapIso e) hM
  · intro hN
    -- Apply the same transport along the inverse isomorphism.
    exact P.prop_of_iso (ModuleCat.single0Functor.mapIso e.symm) hN

/-- Helper for Lemma 15.83.4: an `R`-algebra equivalence intertwines the scalar actions coming
from a polynomial presentation of the target and the induced presentation of the source. -/
private theorem algEquiv_restrictScalars_regular_smul
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] B) :
    let β : MvPolynomial (Fin n) R →ₐ[R] A := e.symm.toAlgHom.comp α
    ∀ (p : MvPolynomial (Fin n) R) (a : A), e (β p * a) = α p * e a := by
  intro β p a
  change e (e.symm (α p) * a) = α p * e a
  rw [e.map_mul, AlgEquiv.apply_symm_apply]

/-- Helper for Lemma 15.83.4: an `R`-algebra equivalence identifies the regular modules after
restricting scalars along a polynomial presentation. -/
private def restrictScalars_regularModule_linearEquiv_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) {n : ℕ}
    (α : MvPolynomial (Fin n) R →ₐ[R] B) :
    let β : MvPolynomial (Fin n) R →ₐ[R] A := e.symm.toAlgHom.comp α
    A ≃ₗ[MvPolynomial (Fin n) R] B :=
  { toEquiv := e.toEquiv
    map_add' := e.map_add
    map_smul' := algEquiv_restrictScalars_regular_smul e α }

/-- Helper for Lemma 15.83.4: flatness of the left factor forces Tor independence with every
base algebra. -/
private theorem flat_stage_isTorIndependent_with_target
    {A₀ B₀ A : Type u} [CommRing A₀] [CommRing B₀] [CommRing A]
    [Algebra A₀ B₀] [Algebra A₀ A] [Module.Flat A₀ B₀] :
    IsTorIndependent A₀ B₀ A := by
  intro p hp
  have hp_outside : (-(p : ℤ)) ∉ Set.Icc (0 : ℤ) 0 := by
    -- Positive Tor degrees correspond to strictly negative homological degrees.
    intro hp_mem
    omega
  have htor0 :
      CategoryTheory.ModuleHasTorDimensionLE (ModuleCat.of A₀ B₀) 0 :=
    (ModuleCat.hasTorDimensionLE_zero_iff_flat (R := A₀) (M := ModuleCat.of A₀ B₀)).2 inferInstance
  have hzero_homology :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat A₀) (-(p : ℤ))).obj
          ((ModuleCat.single0Functor.obj (ModuleCat.of A₀ B₀)) ⊗[A₀]^L
            (ModuleCat.single0Functor.obj (ModuleCat.of A₀ A)))) := by
    -- Evaluate the tor-dimension-`0` owner on the test module `A`.
    simpa [CategoryTheory.ModuleHasTorDimensionLE] using
      htor0 (ModuleCat.of A₀ A) (-(p : ℤ)) hp_outside
  -- Move from the derived-tensor homology description back to the canonical `Tor` object.
  exact
    IsZero.of_iso hzero_homology
      (CategoryTheory.tor_single0_tensor_homology_iso_local
        (R := A₀) (ModuleCat.of A₀ B₀) (ModuleCat.of A₀ A) p).symm

/-- Helper for Lemma 15.83.4: the ring approximation itself can be viewed as an approximation of
the regular target module by taking every module stage to be the corresponding target stage ring.
-/
private noncomputable def regular_module_approximation_of_hom_approximation
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (A : DirectedFiniteTypeHomApproximation f)
    (hbij : A.HasBijectiveBaseChangeTransitions) :
    DirectedFinitePresentationModuleApproximation f S where
  toDirectedFiniteTypeHomApproximation := A
  hasBijectiveBaseChangeTransitions := hbij
  moduleStage := A.SStage
  instAddCommGroupModuleStage := fun i ↦ inferInstance
  instModuleModuleStage := fun i ↦ inferInstance
  instModuleFiniteModuleStage := fun i ↦ inferInstance
  moduleMap := fun {i j} h ↦
    { toFun := A.SMap i j h
      map_add' := fun x y ↦ map_add (A.SMap i j h) x y
      map_smul' := by
        intro r s
        -- Proof comment: the target transition is `A.SStage i`-linear because it is a ring map.
        change A.SMap i j h (r * s) = A.SMap i j h r * A.SMap i j h s
        exact map_mul (A.SMap i j h) r s }
  moduleMap_id := by
    intro i s
    -- Proof comment: the stage transition at `i ≤ i` is the identity in the directed system.
    simpa using (DirectedSystem.map_self (f := fun i j h ↦ A.SMap i j h) i s)
  moduleMap_comp := by
    intro i j k hij hjk s
    -- Proof comment: composition of the module transitions is exactly the ring directed-system
    -- composition law.
    simpa using (DirectedSystem.map_map' (f := fun i j h ↦ A.SMap i j h) hij hjk s)
  moduleToLimit := fun i ↦
    { toFun := A.targetStageToLimit i
      map_add' := fun x y ↦ map_add (A.targetStageToLimit i) x y
      map_smul' := by
        intro r s
        -- Proof comment: the map from a stage ring to the limit ring is linear over the stage
        -- scalar action for the same reason.
        change A.targetStageToLimit i (r * s) = A.targetStageToLimit i r * A.targetStageToLimit i s
        exact map_mul (A.targetStageToLimit i) r s }
  moduleToLimit_comp := by
    intro i j h s
    -- Proof comment: the chosen map to the limit is induced from the direct-limit structure, so
    -- it identifies each transition image with the same limit element.
    change A.targetStageToLimit j (A.SMap i j h s) = A.targetStageToLimit i s
    simpa [DirectedFiniteTypeHomApproximation.targetStageToLimit, RingHom.comp_apply] using
      congrArg A.colimitTarget.toRingHom
        (Ring.DirectLimit.of_f (G := A.SStage) (f := fun i j h ↦ A.SMap i j h) h s)
  transitionBaseChangeMap_bijective := by
    intro i j h
    -- Proof comment: tensoring the regular `A.SStage i`-module up to `A.SStage j` is just the
    -- standard right-unit tensor identification.
    simpa [LinearMap.liftBaseChange_tmul, TensorProduct.rid_tmul, Algebra.smul_def] using
      (TensorProduct.rid (A.SStage i) (A.SStage j)).bijective
  finalBaseChangeMap_bijective := by
    intro i
    -- Proof comment: the same right-unit tensor identification compares the limit module
    -- `S ⊗[A.SStage i] A.SStage i` with the regular `S`-module.
    simpa [LinearMap.liftBaseChange_tmul, TensorProduct.rid_tmul, Algebra.smul_def] using
      (TensorProduct.rid (A.SStage i) S).bijective

/-- Helper for Lemma 15.83.4: the source-proof descent step needs a ring-level specialization of
Lemma `10.168.1` that produces a flat finite-type `ℤ`-model for the algebra itself. -/
private theorem exists_flat_finiteType_z_model
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] :
    ∃ (A₀ : Type u) (_ : CommRing A₀) (r : A₀ →+* A)
      (_ : (Int.castRingHom A₀).FiniteType) (B₀ : Type u) (_ : CommRing B₀)
      (g : A₀ →+* B₀),
        g.FiniteType ∧
          Module.Flat A₀ B₀ ∧
          Nonempty
            (let _ : Algebra A₀ A := r.toAlgebra
             let _ : Algebra A₀ B₀ := g.toAlgebra
             let _ : Algebra A B := (algebraMap A B)
             A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  classical
  let f : A →+* B := algebraMap A B
  let hf : f.FinitePresentation := RingHom.finitePresentation_algebraMap.mpr inferInstance
  obtain ⟨approx, hbij⟩ := exists_directedFinitePresentationHomApproximation f hf
  let regApprox :=
    regular_module_approximation_of_hom_approximation f approx hbij
  have hflatLimit :
      let _ : Module A B := Module.compHom B f
      Module.Flat A B := inferInstance
  obtain ⟨i₀, hi₀⟩ := eventually_flat_stageModules_of_flat_limit regApprox hflatLimit
  have hflatStage : Module.Flat (approx.RStage i₀) (approx.SStage i₀) := by
    -- Proof comment: at the chosen stage, the approximating module is literally the stage ring.
    simpa using hi₀ i₀ le_rfl
  let _ : Algebra (approx.RStage i₀) A := (approx.sourceStageToLimit i₀).toAlgebra
  let _ : Algebra (approx.RStage i₀) (approx.SStage i₀) := (approx.stageMap i₀).toAlgebra
  let _ : Algebra (approx.SStage i₀) B := (approx.targetStageToLimit i₀).toAlgebra
  let _ : Algebra (approx.RStage i₀) B :=
    ((algebraMap A B).comp (approx.sourceStageToLimit i₀)).toAlgebra
  let _ : IsScalarTower (approx.RStage i₀) A B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower (approx.RStage i₀) (approx.SStage i₀) B :=
    approx.targetStageToLimit_isScalarTower i₀
  have hPushout : Algebra.IsPushout (approx.RStage i₀) A (approx.SStage i₀) B := by
    -- Proof comment: the final square of the regular-module approximation is the desired pushout.
    simpa using regApprox.finalSquare_isPushout i₀
  let _ : Algebra.IsPushout (approx.RStage i₀) A (approx.SStage i₀) B := hPushout
  refine ⟨approx.RStage i₀, inferInstance, approx.sourceStageToLimit i₀, approx.source_finiteType i₀,
    approx.SStage i₀, inferInstance, approx.stageMap i₀, approx.target_finiteType i₀,
    hflatStage, ?_⟩
  refine ⟨?_⟩
  -- Proof comment: identify the pushout tensor square with `B` by first cancelling the base
  -- change and then removing the redundant right tensor factor.
  exact
    (Algebra.IsPushout.cancelBaseChangeAlg
      (approx.RStage i₀) A (approx.SStage i₀) B (approx.SStage i₀)).symm.trans
      (Algebra.TensorProduct.rid (approx.SStage i₀) A B)

/-- Helper for Lemma 15.83.4: relative pseudo-coherence should transfer from the descended base
change algebra to the target algebra through an `A`-algebra equivalence. -/
private theorem pseudoCoherentRelativeTo_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A]
    (e : A ≃ₐ[R] B)
    (hA : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo R := by
  let _ : Algebra.FiniteType R B := Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType R A) e
  rw [ModuleCat.IsPseudoCoherentRelativeTo, DerivedCategory.IsPseudoCoherentRelativeTo] at hA ⊢
  intro m
  rw [DerivedCategory.IsMPseudoCoherentRelativeTo] at hA ⊢
  intro n α hα
  let β : MvPolynomial (Fin n) R →ₐ[R] A := e.symm.toAlgHom.comp α
  have hβ : Function.Surjective β := Function.Surjective.comp e.symm.surjective hα
  have hA' :
      ((ModuleCat.restrictScalars β.toRingHom).mapDerivedCategory.obj
        (ModuleCat.single0Functor.obj (ModuleCat.of A A))).IsMPseudoCoherent m :=
    hA m n β hβ
  let P : ObjectProperty (DerivedCategory (ModuleCat (MvPolynomial (Fin n) R))) :=
    fun K ↦ K.IsMPseudoCoherent m
  have hSingleA :
      (ModuleCat.single0Functor.obj
        (((ModuleCat.restrictScalars β.toRingHom).obj
          (ModuleCat.of A A)))).IsMPseudoCoherent m := by
    -- Rewrite the restricted degree-zero object as the degree-zero object of the restricted
    -- regular module.
    exact
      P.prop_of_iso
        (restrictScalars_single0_iso β.toRingHom (ModuleCat.of A A))
        hA'
  let eModule :
      ((ModuleCat.restrictScalars β.toRingHom).obj (ModuleCat.of A A)) ≅
        ((ModuleCat.restrictScalars α.toRingHom).obj (ModuleCat.of B B)) :=
    moduleCat_iso_of_linearEquiv
      (restrictScalars_regularModule_linearEquiv_of_algEquiv e α)
  have hSingleB :
      (ModuleCat.single0Functor.obj
        (((ModuleCat.restrictScalars α.toRingHom).obj
          (ModuleCat.of B B)))).IsMPseudoCoherent m := by
    -- Transport the regular module comparison across the induced isomorphism of single complexes.
    exact P.prop_of_iso (ModuleCat.single0Functor.mapIso eModule) hSingleA
  -- Convert back from the restricted module object to the restricted derived degree-zero object.
  exact
    P.prop_of_iso
      (restrictScalars_single0_iso α.toRingHom (ModuleCat.of B B)).symm
      hSingleB

/-- Helper for Lemma 15.83.4: the degree-zero single complex on a flat module is termwise flat. -/
private theorem single0_termwiseFlat_of_flat
    {R : Type u} [CommRing R] {M : ModuleCat R}
    (hFlat : Module.Flat R M) :
    ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M).IsTermwiseFlat := by
  -- Proof comment: in degree `0` this is the given flat module, and every other degree is the
  -- chosen zero module, which is flat.
  intro n
  change Module.Flat R
    (((if n = 0 then M else (0 : ModuleCat R) : ModuleCat R) : ModuleCat R) : Type u)
  by_cases h : n = 0
  · subst n
    simpa using hFlat
  · rw [if_neg h]
    let e : (0 : ModuleCat R) ≅ ModuleCat.of R PUnit :=
      (Limits.isZero_zero (ModuleCat R)).iso ((ModuleCat.isZero_iff_subsingleton).2 inferInstance)
    simpa using Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.83.4: for a flat algebra map, derived scalar extension of a degree-zero
module agrees with the degree-zero object of the ordinary scalar extension. -/
private noncomputable def derivedTensorWithAlgebra_single0_extendScalars_iso
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) :
    ((derivedTensorWithAlgebra (algebraMap A B)).obj (ModuleCat.single0Functor.obj M)) ≅
      ModuleCat.single0Functor.obj
        ((ModuleCat.extendScalars (algebraMap A B)).obj M) := by
  letI : Module.Flat A B := RingHom.flat_algebraMap_iff.mp hflat
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars (algebraMap A B)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat A B from inferInstance))
  let F₀ : ModuleCat A ⥤ ModuleCat B := ModuleCat.extendScalars (algebraMap A B)
  let F : HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat B) :=
    F₀.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh
  letI :
      F.HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)) :=
    extendScalarsToDerived_hasLeftDerivedFunctor (R := A) (A := B) (algebraMap A B)
  letI :
      F₀.mapDerivedCategory.IsLeftDerivedFunctor
        F₀.mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)) := by
    -- Proof comment: exact scalar extension inverts quasi-isomorphisms, so it already computes
    -- the left-derived scalar-extension owner.
    simpa [F₀] using
      (Functor.isLeftDerivedFunctor_of_inverts
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        F₀.mapDerivedCategory
        F₀.mapDerivedCategoryFactorsh)
  let eDerived :
      derivedTensorWithAlgebra (algebraMap A B) ≅ F₀.mapDerivedCategory :=
    let e :
        F₀.mapDerivedCategory ≅ derivedTensorWithAlgebra (algebraMap A B) :=
      Functor.leftDerivedNatIso
        F₀.mapDerivedCategory
        (F.totalLeftDerived
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat A))
          (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)))
        F₀.mapDerivedCategoryFactorsh.hom
        (Functor.totalLeftDerivedCounit
          F
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat A) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat A))
          (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ)))
        (HomotopyCategory.quasiIso (ModuleCat A) (ComplexShape.up ℤ))
        (Iso.refl F)
    e.symm
  -- Proof comment: identify flat derived scalar extension with exact scalar extension, then
  -- commute exact scalar extension with the degree-zero embedding.
  exact
    (eDerived.app (ModuleCat.single0Functor.obj M)) ≪≫
      (((F₀.mapDerivedCategory).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app M)) ≪≫
        (F₀.mapDerivedCategoryFactors.app
          ((CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) ≪≫
        DerivedCategory.Q.mapIso
          ((Functor.mapCochainComplexSingleFunctor
            (ModuleCat.extendScalars (algebraMap A B))
            (0 : ℤ)).app M) ≪≫
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app
          ((ModuleCat.extendScalars (algebraMap A B)).obj M)).symm)

/-- Helper for Lemma 15.83.4: extending scalars on the regular `B₀`-module to the tensor-product
algebra produces the regular module of `B₀ ⊗[A₀] A`. -/
private noncomputable def extendScalars_regular_tensorProduct_iso
    {A₀ B₀ A : Type u} [CommRing A₀] [CommRing B₀] [CommRing A]
    [Algebra A₀ B₀] [Algebra A₀ A] :
    ((ModuleCat.extendScalars (algebraMap B₀ (B₀ ⊗[A₀] A))).obj
      (ModuleCat.of B₀ B₀)) ≅
      ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A) := by
  let eCoeff :
      ↑((ModuleCat.restrictScalars (algebraMap B₀ (B₀ ⊗[A₀] A))).obj
        (ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A))) ≃ₗ[B₀ ⊗[A₀] A] (B₀ ⊗[A₀] A) :=
    { __ := AddEquiv.refl (B₀ ⊗[A₀] A)
      map_smul' := fun _ _ ↦ rfl }
  let eExtend :
      ((ModuleCat.extendScalars (algebraMap B₀ (B₀ ⊗[A₀] A))).obj
        (ModuleCat.of B₀ B₀)) ≅
        ModuleCat.of (B₀ ⊗[A₀] A) ((B₀ ⊗[A₀] A) ⊗[B₀] B₀) := by
    -- Proof comment: exact scalar extension on modules is the ordinary tensor-product module.
    simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
      (TensorProduct.AlgebraTensorModule.congr eCoeff (LinearEquiv.refl B₀ B₀)).toModuleIso
  let eRid :
      ModuleCat.of (B₀ ⊗[A₀] A) ((B₀ ⊗[A₀] A) ⊗[B₀] B₀) ≅
        ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A) := by
    -- Proof comment: the right tensor factor is the regular `B₀`-module, so the tensor product
    -- collapses to the ambient tensor-product algebra.
    simpa using (TensorProduct.rid B₀ (B₀ ⊗[A₀] A)).toModuleIso
  exact eExtend ≪≫ eRid

/-- Helper for Lemma 15.83.4: the derived base change of the regular degree-zero `B₀`-module is
the ordinary degree-zero regular module of `B₀ ⊗[A₀] A`. -/
private noncomputable def derivedTensorWithAlgebra_regular_single0_iso
    {A₀ B₀ A : Type u} [CommRing A₀] [CommRing B₀] [CommRing A]
    [Algebra A₀ B₀] [Algebra A₀ A] [Module.Flat A₀ B₀] :
    ((derivedTensorWithAlgebra (algebraMap B₀ (B₀ ⊗[A₀] A))).obj
      (ModuleCat.single0Functor.obj (ModuleCat.of B₀ B₀))) ≅
      ModuleCat.single0Functor.obj
        (ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A)) := by
  -- Proof comment: first replace the derived tensor product by the strict scalar extension of the
  -- one-term complex, then rewrite that strict scalar extension back to the degree-zero regular
  -- module of the tensor-product algebra.
  exact
    (derivedTensorWithAlgebra_single0_extendScalars_iso
      (A := B₀) (B := B₀ ⊗[A₀] A)
      (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (ModuleCat.of B₀ B₀)) ≪≫
      ModuleCat.single0Functor.mapIso
        (extendScalars_regular_tensorProduct_iso (A₀ := A₀) (B₀ := B₀) (A := A))

/-- Helper for Lemma 15.83.4: once the flat descended stage exists, Lemma `15.82.12` should be
specialized to the regular module and rewritten as the ordinary base-changed regular module. -/
private theorem regular_module_pseudoCoherentRelativeTo_of_torIndependent_baseChange
    {A₀ B₀ A : Type u} [CommRing A₀] [CommRing B₀] [CommRing A]
    [Algebra A₀ B₀] [Algebra A₀ A] [Algebra.FiniteType A₀ B₀] [IsNoetherianRing A₀]
    (hTor : IsTorIndependent A₀ B₀ A) :
    (ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A)).IsPseudoCoherentRelativeTo A := by
  let P : ObjectProperty (DerivedCategory (ModuleCat (B₀ ⊗[A₀] A))) :=
    fun K ↦ K.IsPseudoCoherentRelativeTo A
  have hStageDerived :
      (ModuleCat.single0Functor.obj (ModuleCat.of B₀ B₀)).IsPseudoCoherentRelativeTo A₀ := by
    -- Proof comment: this is exactly the regular-module field of the earlier finite-type
    -- Noetherian pseudo-coherent ring-map criterion.
    simpa [ModuleCat.IsPseudoCoherentRelativeTo] using
      (inferInstance : (ModuleCat.of B₀ B₀).IsPseudoCoherentRelativeTo A₀)
  have hBaseDerived :
      ((CategoryTheory.derivedTensorWithAlgebra
        (algebraMap B₀ (B₀ ⊗[A₀] A))).obj
        (ModuleCat.single0Functor.obj (ModuleCat.of B₀ B₀))).IsPseudoCoherentRelativeTo A := by
    -- Proof comment: apply the Tor-independent base-change theorem directly to the regular
    -- degree-zero `B₀`-module.
    simpa using
      (CategoryTheory.derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent
        (R := A₀) (A := B₀) (R' := A)
        (K := ModuleCat.single0Functor.obj (ModuleCat.of B₀ B₀))
        hTor hStageDerived)
  have hTargetDerived :
      (ModuleCat.single0Functor.obj
        (ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A))).IsPseudoCoherentRelativeTo A := by
    -- Proof comment: transport the derived conclusion across the explicit one-term comparison
    -- from Lemma `15.67.13` and the regular-module tensor-product identification.
    exact
      P.prop_of_iso
        (derivedTensorWithAlgebra_regular_single0_iso (A₀ := A₀) (B₀ := B₀) (A := A))
        hBaseDerived
  simpa [ModuleCat.IsPseudoCoherentRelativeTo] using hTargetDerived

/- Domain-style sampling for Lemma 15.83.4:
- primary domain: perfect ring maps for flat finitely presented algebras;
- sampled owner declarations:
  `RingHom.IsPerfectRingMap`,
  `RingHom.IsPseudoCoherentRingMap`,
  `CategoryTheory.ModuleHasFiniteTorDimension`,
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`;
- best owner abstraction: the source-facing conclusion belongs on the ring-map owner
  `(algebraMap A B).IsPerfectRingMap`; pseudo-coherence and finite Tor dimension should be derived
  from the canonical chapter owners rather than by a local wrapper;
- primitive vs. derived:
  primitive public data are the flatness and finite-presentation instances on `A → B`;
  derived API is the perfectness instance, whose fields come from the chapter owner
  `RingHom.IsPseudoCoherentRingMap` and the zero-step Tor-dimension bridge
  `ModuleCat.hasTorDimensionLE_zero_iff_flat`.

Source/core/bridge triage:
- `source-facing`: the instance below;
- `core/canonical`: `RingHom.IsPerfectRingMap`, `RingHom.IsPseudoCoherentRingMap`,
  `ModuleHasFiniteTorDimension`;
- `bridge/view`: the zero-step equivalence between module flatness and tor dimension at most `0`.
-/
/- Proof sketch: the pseudo-coherence field is the substantive part of the source argument,
obtained by descending the flat finitely presented map to a flat finite type model over a finite
type `ℤ`-algebra and applying the pseudo-coherence ascent/descent results from `15.82`. The finite
Tor-dimension field is the flat-implies-tor-dimension-`0` clause for the canonical module
`ModuleCat.of A B`. -/
/-- Lemma 15.83.4: a ring map `A → B` which is flat and of finite presentation is perfect. -/
@[stacks 067J]
instance isPerfectRingMap_of_flat_of_finitePresentation
    (A : Type u) (B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] : (algebraMap A B).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := by
    classical
    -- Route correction: the source proof still passes through a flat finite-type `ℤ`-model and
    -- Tor-independent base change; after the new stage-model descent, only the Chapter 15
    -- regular-module derived normalization remains.
    obtain ⟨A₀, _, r, hA₀finite, B₀, _, g, hgFiniteType, hflatStage, ⟨eFinal⟩⟩ :=
      exists_flat_finiteType_z_model A B
    let _ : Algebra A₀ A := r.toAlgebra
    let _ : Algebra A₀ B₀ := g.toAlgebra
    let _ : Module.Flat A₀ B₀ := hflatStage
    let _ : Algebra.FiniteType ℤ A₀ := hA₀finite
    let _ : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
    let _ : Algebra.FiniteType A₀ B₀ := RingHom.finiteType_algebraMap.mp hgFiniteType
    have hTor : IsTorIndependent A₀ B₀ A :=
      flat_stage_isTorIndependent_with_target (A₀ := A₀) (B₀ := B₀) (A := A)
    have hBase :
        (ModuleCat.of (B₀ ⊗[A₀] A) (B₀ ⊗[A₀] A)).IsPseudoCoherentRelativeTo A :=
      regular_module_pseudoCoherentRelativeTo_of_torIndependent_baseChange
        (A₀ := A₀) (B₀ := B₀) (A := A) hTor
    have hComm :
        (ModuleCat.of (A ⊗[A₀] B₀) (A ⊗[A₀] B₀)).IsPseudoCoherentRelativeTo A := by
      -- Proof comment: swap the tensor factors to match the source-proof presentation of the
      -- descended algebra.
      exact
        pseudoCoherentRelativeTo_of_algEquiv
          (R := A) (A := B₀ ⊗[A₀] A) (B := A ⊗[A₀] B₀)
          (Algebra.TensorProduct.commRight A₀ A B₀) hBase
    -- Proof comment: the descended tensor-product algebra is the original target ring by the
    -- pushout comparison from the ring approximation stage.
    exact pseudoCoherentRelativeTo_of_algEquiv (R := A) (A := A ⊗[A₀] B₀) (B := B) eFinal hComm
  hasFiniteTorDimension := by
    -- Flatness gives tor dimension at most `0`, hence finite tor dimension.
    exact
      ((ModuleCat.hasTorDimensionLE_zero_iff_flat (R := A) (M := ModuleCat.of A B)).2 inferInstance)
        .hasFiniteTorDimension

end Algebra
