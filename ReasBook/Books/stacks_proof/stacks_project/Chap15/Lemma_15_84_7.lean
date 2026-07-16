import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_67_3
import stacks_proof.stacks_project.Chap15.Lemma_15_84_4
import stacks_proof.stacks_project.Chap15.Lemma_15_84_6
import stacks_proof.stacks_project.Chap15.«15_74_0_2»
import stacks_proof.stacks_project.Chap15.«15_60_1_1»
import stacks_proof.stacks_project.Chap15.Lemma_15_84_2

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorWithAlgebra
open scoped TensorProduct

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {I : Type v} [Preorder I] [IsFiltered I]
variable (F : I ⥤ CommRingCat.{u}) [HasColimit F] (i₀ : I)
variable (A₀ : Type u) [CommRing A₀] [Algebra (F.obj i₀) A₀]

/- Domain-style sampling for Lemma 15.84.7:
- primary domain: filtered-colimit descent and Hom comparison for derived scalar extension along
  `A₀ → A₀ ⊗[R₀] R_j` and `A₀ → A₀ ⊗[R₀] colim_i R_i`;
- sampled owner declarations in this domain:
  `DerivedCategory.IsPerfectOver`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraCompIso`,
  `Lemma_15_75_18.stageToColimitHomMap`;
- best owner abstraction: the public source-facing layer here is the stagewise factorization and
  eventual-equality API for Homs after base change, while the iterated-vs-direct scalar-extension
  comparisons remain private bridges built from `derivedTensorWithAlgebraCompIso`;
- primitive vs. derived:
  primitive data are the filtered diagram `F`, the base stage `i₀`, the induced algebra maps
  `F.obj i₀ → F.obj j` and `F.obj j → colimit F`, and the canonical scalar-tower algebra maps
  they induce on `A₀ ⊗[F.obj i₀] F.obj j`;
  the Hom transition maps and descent/equality theorems are derived API over those canonical maps;
- source/core/bridge triage:
  `source-facing`: the three numbered descent/factorization/eventual-equality statements;
  `core/canonical`: `DerivedCategory.IsPerfectOver`, `derivedTensorWithAlgebra`, and
    `derivedTensorWithAlgebraCompIso`;
  `bridge/view`: the canonical scalar-tower / tensor-product transition maps and
    iterated-vs-direct comparison isomorphisms used to define the source-facing Hom maps. -/

private abbrev ringColimit : CommRingCat.{u} :=
  colimit F

instance stageAlgebra (j : Set.Ici i₀) : Algebra (F.obj i₀) (F.obj j.1) :=
  (F.map (homOfLE j.2)).hom.toAlgebra

instance colimitAlgebra : Algebra (F.obj i₀) (ringColimit F) :=
  (colimit.ι F i₀).hom.toAlgebra

private instance stageToColimitAlgebra (j : Set.Ici i₀) :
    Algebra (F.obj j.1) (ringColimit F) :=
  (colimit.ι F j.1).hom.toAlgebra

omit [IsFiltered I] in
private theorem stageToColimitRingHom_comp_eq (j : Set.Ici i₀) :
    (colimit.ι F j.1).hom.comp (F.map (homOfLE j.2)).hom = (colimit.ι F i₀).hom := by
  rw [← CommRingCat.hom_comp]
  simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE j.2))

omit [IsFiltered I] in
private theorem stageTransitionRingHom_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (F.map h).hom.comp (F.map (homOfLE j.2)).hom = (F.map (homOfLE k.2)).hom := by
  -- Proof comment: the direct map `R₀ → R_k` is the functorial composite
  -- `R₀ → R_j → R_k`.
  rw [← CommRingCat.hom_comp]
  have hcomp : homOfLE j.2 ≫ h = homOfLE k.2 := Subsingleton.elim _ _
  rw [← F.map_comp, hcomp]

omit [IsFiltered I] in
private instance stageToColimitIsScalarTower (j : Set.Ici i₀) :
    IsScalarTower (F.obj i₀) (F.obj j.1) (ringColimit F) :=
  IsScalarTower.of_algebraMap_eq' (stageToColimitRingHom_comp_eq F i₀ j).symm

private abbrev stageTransitionTensorMap {j k : Set.Ici i₀} (h : j ⟶ k) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] F.obj k.1 :=
  letI : Algebra (F.obj j.1) (F.obj k.1) := (F.map h).hom.toAlgebra
  letI : IsScalarTower (F.obj i₀) (F.obj j.1) (F.obj k.1) :=
    IsScalarTower.of_algebraMap_eq' (stageTransitionRingHom_comp_eq F i₀ h).symm
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (F.obj k.1))

private abbrev stageToColimitTensorMap (j : Set.Ici i₀) :
    A₀ ⊗[F.obj i₀] F.obj j.1 →+* A₀ ⊗[F.obj i₀] ringColimit F :=
  Algebra.TensorProduct.map (AlgHom.id (F.obj i₀) A₀)
    (IsScalarTower.toAlgHom (F.obj i₀) (F.obj j.1) (ringColimit F))

private theorem stageToColimitTensorMap_comp_eq (j : Set.Ici i₀) :
    (stageToColimitTensorMap F i₀ A₀ j).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
        algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F) := by
  -- Proof comment: the tensor-product map fixes the left tensor factor, so it preserves the
  -- canonical `A₀`-algebra structure.
  ext a
  simp [stageToColimitTensorMap, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.one_def]

private theorem stageTransitionTensorMap_comp_eq {j k : Set.Ici i₀} (h : j ⟶ k) :
    (stageTransitionTensorMap F i₀ A₀ h).comp
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) =
      algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1) := by
  -- Proof comment: the transition map also acts trivially on the left tensor factor.
  ext a
  simp [stageTransitionTensorMap, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.one_def]

local notation "DModA0" => DerivedCategory (ModuleCat A₀)

private instance stageToColimitTensorAlgebra (j : Set.Ici i₀) :
    Algebra (A₀ ⊗[F.obj i₀] F.obj j.1) (A₀ ⊗[F.obj i₀] ringColimit F) :=
  (stageToColimitTensorMap F i₀ A₀ j).toAlgebra

private abbrev stageBaseChange (j : Set.Ici i₀) :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))

private abbrev colimitBaseChange :
    DModA0 ⥤ DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))

private abbrev stageToColimitBaseChange (j : Set.Ici i₀) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  derivedTensorWithAlgebra (stageToColimitTensorMap F i₀ A₀ j)

private abbrev stageTransitionBaseChange {j k : Set.Ici i₀} (h : j ⟶ k) :
    DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj k.1)) :=
  derivedTensorWithAlgebra (stageTransitionTensorMap F i₀ A₀ h)

private noncomputable abbrev stageToColimitBaseChangeIso (j : Set.Ici i₀) :
    stageBaseChange F i₀ A₀ j ⋙ stageToColimitBaseChange F i₀ A₀ j ≅
      colimitBaseChange F i₀ A₀ :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageToColimitTensorMap F i₀ A₀ j)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))
    (stageToColimitTensorMap_comp_eq F i₀ A₀ j)

private noncomputable abbrev stageTransitionBaseChangeIso {j k : Set.Ici i₀} (h : j ⟶ k) :
    stageBaseChange F i₀ A₀ j ⋙ stageTransitionBaseChange F i₀ A₀ h ≅
      stageBaseChange F i₀ A₀ k :=
  derivedTensorWithAlgebraCompIso
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1))
    (stageTransitionTensorMap F i₀ A₀ h)
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj k.1))
    (stageTransitionTensorMap_comp_eq F i₀ A₀ h)

/-- Helper for Lemma 15.84.7: the cocone relation
`A_j → A_k → A = A_j → A` for the tensor-product stage rings. -/
private theorem stageToColimitThroughTransitionTensorMap_comp_eq
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    (stageToColimitTensorMap F i₀ A₀ k).comp (stageTransitionTensorMap F i₀ A₀ h) =
      stageToColimitTensorMap F i₀ A₀ j := by
  -- Proof comment: compare the two tensor-product maps on the left and right tensor generators.
  apply Algebra.TensorProduct.ext_ring
  · ext a
    simp [stageToColimitTensorMap, stageTransitionTensorMap,
      Algebra.TensorProduct.includeLeft_apply]
  · ext x
    simp [stageToColimitTensorMap, stageTransitionTensorMap,
      Algebra.TensorProduct.includeRight_apply, stageToColimitRingHom_comp_eq,
      stageTransitionRingHom_comp_eq]

/-- Helper for Lemma 15.84.7: the direct limit of the tensor-stage rings `A_j` viewed as a raw
ring. This packages the source-proof stage system before constructing the final comparison
isomorphism with `A = A₀ ⊗[R₀] colim_i R_i`. -/
private abbrev tensorStageDirectLimit :=
  Ring.DirectLimit
    (fun j : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj j.1)
    (fun j k h ↦ stageTransitionTensorMap F i₀ A₀ h)

/-- Helper for Lemma 15.84.7: the stage maps `A_j → A` assemble to the canonical comparison
ring homomorphism from the tensor-stage direct limit to the final tensor product over the colimit
ring. -/
private noncomputable def tensorStageDirectLimitToColimit :
    tensorStageDirectLimit F i₀ A₀ →+* (A₀ ⊗[F.obj i₀] ringColimit F) :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj j.1)
    (fun j k h ↦ stageTransitionTensorMap F i₀ A₀ h)
    (A₀ ⊗[F.obj i₀] ringColimit F)
    (fun j ↦ stageToColimitTensorMap F i₀ A₀ j)
    (fun j k h x ↦ by
      -- Proof comment: the cocone relation already proves the stagewise compatibility needed by
      -- `Ring.DirectLimit.lift`.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f :
            A₀ ⊗[F.obj i₀] F.obj j.1 →+*
              (A₀ ⊗[F.obj i₀] ringColimit F) ↦ f x)
          (stageToColimitThroughTransitionTensorMap_comp_eq
            (F := F) (i₀ := i₀) (A₀ := A₀) h))

/-- Helper for Lemma 15.84.7: on each tensor-stage leg, the direct-limit comparison map is the
original stage-to-colimit tensor map. -/
private theorem tensorStageDirectLimitToColimit_comp_of
    (j : Set.Ici i₀) :
    (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (Ring.DirectLimit.of
          (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
          (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
          j) =
      stageToColimitTensorMap F i₀ A₀ j := by
  ext x
  -- Proof comment: this is the defining computation rule for the universal `lift`.
  simpa [tensorStageDirectLimitToColimit] using
    (Ring.DirectLimit.lift_of
      (G := fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
      (f := fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
      (P := A₀ ⊗[F.obj i₀] ringColimit F)
      (g := fun k ↦ stageToColimitTensorMap F i₀ A₀ k)
      (Hg := fun k l h y ↦ by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun f :
              A₀ ⊗[F.obj i₀] F.obj k.1 →+*
                (A₀ ⊗[F.obj i₀] ringColimit F) ↦ f y)
            (stageToColimitThroughTransitionTensorMap_comp_eq
              (F := F) (i₀ := i₀) (A₀ := A₀) h))
      j x)

/-- Helper for Lemma 15.84.7: the stage maps `R_j → A_j → colim_j A_j` sending
`r` to the class of `1 ⊗ r` are compatible with the filtered transition maps. -/
private theorem tensorStageDirectLimit_fromColimitRight_stage_compat
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    ((Ring.DirectLimit.of
        (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
        (fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
        k).comp
        (Algebra.TensorProduct.includeRight :
          F.obj k.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj k.1).toRingHom).comp
      (F.map h).hom =
        (Ring.DirectLimit.of
          (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
          (fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
          j).comp
          (Algebra.TensorProduct.includeRight :
            F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1).toRingHom := by
  ext x
  -- Proof comment: the transition map carries the generator `1 ⊗ x` to
  -- `1 ⊗ F(h)(x)`, and that is exactly the relation imposed in the direct limit.
  calc
    Ring.DirectLimit.of
        (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
        (fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
        k
        ((Algebra.TensorProduct.includeRight :
          F.obj k.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj k.1) ((F.map h).hom x)) =
      Ring.DirectLimit.of
        (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
        (fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
        k
        ((stageTransitionTensorMap F i₀ A₀ h)
          ((Algebra.TensorProduct.includeRight :
            F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1) x)) := by
          congr 1
          simp [stageTransitionTensorMap, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.one_def]
    _ =
      Ring.DirectLimit.of
        (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
        (fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
        j
        ((Algebra.TensorProduct.includeRight :
          F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1) x) := by
          simpa using
            (Ring.DirectLimit.of_f
              (f := fun l m h' ↦ stageTransitionTensorMap F i₀ A₀ h')
              h
              ((Algebra.TensorProduct.includeRight :
                F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1) x)).symm

/-- Helper for Lemma 15.84.7: the colimit ring maps to the direct limit of the tensor-stage
rings by sending a stage element `r ∈ R_j` to the class of `1 ⊗ r` in the same tensor stage. -/
private noncomputable def tensorStageDirectLimit_fromColimitRight :
    ringColimit F →+* tensorStageDirectLimit F i₀ A₀ :=
  Ring.DirectLimit.lift
    (fun j : Set.Ici i₀ ↦ F.obj j.1)
    (fun j k h ↦ (F.map h).hom)
    (tensorStageDirectLimit F i₀ A₀)
    (fun j ↦
      (Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j).comp
        (Algebra.TensorProduct.includeRight :
          F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1).toRingHom)
    (fun j k h x ↦ by
      -- Proof comment: the direct-limit cocone relation is exactly the compatibility lemma above
      -- evaluated at the stage element `x`.
      simpa [RingHom.comp_apply] using
        congrArg
          (fun f : F.obj j.1 →+* tensorStageDirectLimit F i₀ A₀ ↦ f x)
          (tensorStageDirectLimit_fromColimitRight_stage_compat
            (F := F) (i₀ := i₀) (A₀ := A₀) h))

/-- Helper for Lemma 15.84.7: on each ring stage, the right-factor map to the tensor-stage direct
limit is the expected class of `1 ⊗ r`. -/
private theorem tensorStageDirectLimit_fromColimitRight_comp_of
    (j : Set.Ici i₀) :
    (tensorStageDirectLimit_fromColimitRight (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (colimit.ι F j.1).hom =
      (Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j).comp
        (Algebra.TensorProduct.includeRight :
          F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1).toRingHom := by
  ext x
  -- Proof comment: this is the defining computation rule for the universal `lift` from the
  -- filtered colimit of the rings `R_j`.
  simpa [tensorStageDirectLimit_fromColimitRight] using
    (Ring.DirectLimit.lift_of
      (G := fun k : Set.Ici i₀ ↦ F.obj k.1)
      (f := fun k l h ↦ (F.map h).hom)
      (P := tensorStageDirectLimit F i₀ A₀)
      (g := fun k ↦
        (Ring.DirectLimit.of
          (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
          (fun l m h ↦ stageTransitionTensorMap F i₀ A₀ h)
          k).comp
          (Algebra.TensorProduct.includeRight :
            F.obj k.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj k.1).toRingHom)
      (Hg := fun k l h x ↦ by
        simpa [RingHom.comp_apply] using
          congrArg
            (fun f : F.obj k.1 →+* tensorStageDirectLimit F i₀ A₀ ↦ f x)
            (tensorStageDirectLimit_fromColimitRight_stage_compat
              (F := F) (i₀ := i₀) (A₀ := A₀) h))
      j x)

/-- Helper for Lemma 15.84.7: the canonical `A₀`-algebra map into the tensor-stage direct limit
is the class of the left tensor generator in the initial stage `j = i₀`. -/
private noncomputable def tensorStageDirectLimitLeftMap :
    A₀ →+* tensorStageDirectLimit F i₀ A₀ :=
  (Ring.DirectLimit.of
      (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
      (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
      ⟨i₀, le_rfl⟩).comp
    (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj i₀))

/-- Helper for Lemma 15.84.7: the canonical `R₀`-algebra map into the tensor-stage direct limit
is the class of the right tensor generator in the initial stage `j = i₀`. -/
private noncomputable def tensorStageDirectLimitBaseMap :
    F.obj i₀ →+* tensorStageDirectLimit F i₀ A₀ :=
  (Ring.DirectLimit.of
      (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
      (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
      ⟨i₀, le_rfl⟩).comp
    (Algebra.TensorProduct.includeRight :
      F.obj i₀ →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj i₀).toRingHom

private instance tensorStageDirectLimitAlgebra :
    Algebra A₀ (tensorStageDirectLimit F i₀ A₀) :=
  (tensorStageDirectLimitLeftMap (F := F) (i₀ := i₀) (A₀ := A₀)).toAlgebra

private instance tensorStageDirectLimitBaseAlgebra :
    Algebra (F.obj i₀) (tensorStageDirectLimit F i₀ A₀) :=
  (tensorStageDirectLimitBaseMap (F := F) (i₀ := i₀) (A₀ := A₀)).toAlgebra

/-- Helper for Lemma 15.84.7: the canonical `A₀`-algebra map into the tensor-stage direct limit
can be computed on any stage `A_j`, because every transition fixes the left tensor factor. -/
private theorem tensorStageDirectLimitLeftMap_eq_comp_of
    (j : Set.Ici i₀) :
    tensorStageDirectLimitLeftMap (F := F) (i₀ := i₀) (A₀ := A₀) =
      (Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j).comp
        (algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) := by
  ext a
  -- Proof comment: move the left tensor generator from the initial stage to `j`; the transition
  -- map fixes it, so both classes in the direct limit coincide.
  calc
    Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        ⟨i₀, le_rfl⟩
        ((algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj i₀)) a) =
      Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j
        ((stageTransitionTensorMap F i₀ A₀ (homOfLE j.2))
          ((algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj i₀)) a)) := by
            simpa using
              (Ring.DirectLimit.of_f
                (f := fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
                (homOfLE j.2)
                ((algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj i₀)) a))
    _ =
      Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j
        ((algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj j.1)) a) := by
            simp [stageTransitionTensorMap, Algebra.TensorProduct.includeLeft_apply,
              Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.one_def]

/-- Helper for Lemma 15.84.7: the direct-limit comparison map preserves the chosen `A₀`-algebra
structure on the tensor-stage direct limit. -/
private theorem tensorStageDirectLimitToColimit_comp_leftMap :
    (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (tensorStageDirectLimitLeftMap (F := F) (i₀ := i₀) (A₀ := A₀)) =
      algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F) := by
  ext a
  -- Proof comment: evaluate at the initial stage and use that the tensor-product cocone map fixes
  -- the left tensor factor.
  simpa [tensorStageDirectLimitLeftMap, RingHom.comp_apply, Algebra.TensorProduct.one_def] using
    congrArg
      (fun f :
        A₀ ⊗[F.obj i₀] F.obj ⟨i₀, le_rfl⟩.1 →+*
          (A₀ ⊗[F.obj i₀] ringColimit F) ↦
        f ((algebraMap A₀ (A₀ ⊗[F.obj i₀] F.obj i₀)) a))
      (tensorStageDirectLimitToColimit_comp_of
        (F := F) (i₀ := i₀) (A₀ := A₀) ⟨i₀, le_rfl⟩)

/-- Helper for Lemma 15.84.7: the right-factor map from the colimit ring is an `R₀`-algebra map
for the direct-limit `R₀`-algebra structure coming from the stage `j = i₀`. -/
private noncomputable def tensorStageDirectLimit_fromColimitRightAlgHom :
    ringColimit F →ₐ[F.obj i₀] tensorStageDirectLimit F i₀ A₀ where
  toRingHom := tensorStageDirectLimit_fromColimitRight (F := F) (i₀ := i₀) (A₀ := A₀)
  commutes' r := by
    -- Proof comment: on the initial stage leg this is exactly the defining formula for
    -- `tensorStageDirectLimit_fromColimitRight`.
    simpa [tensorStageDirectLimitBaseMap, RingHom.comp_apply] using
      congrArg
        (fun f : F.obj i₀ →+* tensorStageDirectLimit F i₀ A₀ ↦ f r)
        (tensorStageDirectLimit_fromColimitRight_comp_of
          (F := F) (i₀ := i₀) (A₀ := A₀) ⟨i₀, le_rfl⟩)

/-- Helper for Lemma 15.84.7: the left-factor map to the tensor-stage direct limit is already an
`R₀`-algebra map. -/
private noncomputable def tensorStageDirectLimitLeftAlgHom :
    A₀ →ₐ[F.obj i₀] tensorStageDirectLimit F i₀ A₀ where
  toRingHom := tensorStageDirectLimitLeftMap (F := F) (i₀ := i₀) (A₀ := A₀)
  commutes' r := by
    -- Proof comment: in the tensor product over `R₀`, the left and right copies of `r` agree.
    simp [tensorStageDirectLimitLeftMap, tensorStageDirectLimitBaseMap,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.one_def]

/-- Helper for Lemma 15.84.7: the explicit inverse map from
`A₀ ⊗[R₀] colim_i R_i` back to the direct limit of the tensor-stage rings. It sends the left
tensor factor through the left-stage leg and the right tensor factor through the already-constructed
map from the ring colimit. -/
private noncomputable def tensorStageDirectLimitInverse :
    A₀ ⊗[F.obj i₀] ringColimit F →+* tensorStageDirectLimit F i₀ A₀ :=
  (Algebra.TensorProduct.lift
      (tensorStageDirectLimitLeftAlgHom (F := F) (i₀ := i₀) (A₀ := A₀))
      (tensorStageDirectLimit_fromColimitRightAlgHom (F := F) (i₀ := i₀) (A₀ := A₀))).toRingHom

/-- Helper for Lemma 15.84.7: the explicit inverse agrees with the canonical stage leg after
restricting along the map `A_j → A = A₀ ⊗[R₀] colim_i R_i`. -/
private theorem tensorStageDirectLimitInverse_comp_stageToColimitTensorMap
    (j : Set.Ici i₀) :
    (tensorStageDirectLimitInverse (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (stageToColimitTensorMap F i₀ A₀ j) =
      Ring.DirectLimit.of
        (fun k : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj k.1)
        (fun k l h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j := by
  -- Proof comment: compare both ring maps on the left and right tensor generators of `A_j`.
  apply Algebra.TensorProduct.ext_ring
  · ext a
    simp [tensorStageDirectLimitInverse, RingHom.comp_apply,
      tensorStageDirectLimitLeftMap_eq_comp_of, Algebra.TensorProduct.includeLeft_apply]
  · ext x
    simpa [tensorStageDirectLimitInverse, RingHom.comp_apply,
      stageToColimitTensorMap, Algebra.TensorProduct.includeRight_apply] using
      congrArg
        (fun f : F.obj j.1 →+* tensorStageDirectLimit F i₀ A₀ ↦ f x)
        (tensorStageDirectLimit_fromColimitRight_comp_of
          (F := F) (i₀ := i₀) (A₀ := A₀) j)

/-- Helper for Lemma 15.84.7: after composing the right-factor map to the tensor-stage direct
limit with the comparison to the colimit tensor product, one recovers the right tensor inclusion
`colim_i R_i → A₀ ⊗[R₀] colim_i R_i`. -/
private theorem tensorStageDirectLimitToColimit_comp_fromColimitRight :
    (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (tensorStageDirectLimit_fromColimitRight (F := F) (i₀ := i₀) (A₀ := A₀)) =
      (Algebra.TensorProduct.includeRight :
        ringColimit F →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] ringColimit F).toRingHom := by
  ext r
  -- Proof comment: represent `r` on one ring stage, move that representative into the tail
  -- system `j ≥ i₀`, and then both composites are the same class of `1 ⊗ r`.
  obtain ⟨i, ri, hri⟩ := Concrete.colimit_exists_rep F r
  obtain ⟨k, hi₀k, hik⟩ := exists_ge_ge i₀ i
  let j : Set.Ici i₀ := ⟨k, hi₀k⟩
  calc
    (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀))
        ((tensorStageDirectLimit_fromColimitRight (F := F) (i₀ := i₀) (A₀ := A₀)) r) =
      (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀))
        ((tensorStageDirectLimit_fromColimitRight (F := F) (i₀ := i₀) (A₀ := A₀))
          ((colimit.ι F k).hom ((F.map (homOfLE hik)).hom ri))) := by
            rw [hri]
            congr 1
            simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hik)).symm
    _ =
      (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀))
        ((Ring.DirectLimit.of
          (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
          (fun l m h ↦ stageTransitionTensorMap F i₀ A₀ h)
          j)
          ((Algebra.TensorProduct.includeRight :
            F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1)
            ((F.map (homOfLE hik)).hom ri))) := by
              simpa [RingHom.comp_apply] using
                congrArg
                  (fun f : F.obj j.1 →+* tensorStageDirectLimit F i₀ A₀ ↦
                    f ((F.map (homOfLE hik)).hom ri))
                  (tensorStageDirectLimit_fromColimitRight_comp_of
                    (F := F) (i₀ := i₀) (A₀ := A₀) j)
    _ =
      stageToColimitTensorMap F i₀ A₀ j
        ((Algebra.TensorProduct.includeRight :
          F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1)
          ((F.map (homOfLE hik)).hom ri)) := by
            simpa [RingHom.comp_apply] using
              congrArg
                (fun f :
                  A₀ ⊗[F.obj i₀] F.obj j.1 →+*
                    (A₀ ⊗[F.obj i₀] ringColimit F) ↦
                  f ((Algebra.TensorProduct.includeRight :
                    F.obj j.1 →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] F.obj j.1)
                    ((F.map (homOfLE hik)).hom ri)))
                (tensorStageDirectLimitToColimit_comp_of
                  (F := F) (i₀ := i₀) (A₀ := A₀) j)
    _ =
      (Algebra.TensorProduct.includeRight :
        ringColimit F →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] ringColimit F)
          ((colimit.ι F k).hom ((F.map (homOfLE hik)).hom ri)) := by
            simp [stageToColimitTensorMap, j]
    _ =
      (Algebra.TensorProduct.includeRight :
        ringColimit F →ₐ[F.obj i₀] A₀ ⊗[F.obj i₀] ringColimit F) r := by
            rw [hri]
            congr 1
            simpa using congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hik)).symm

/-- Helper for Lemma 15.84.7: the explicit inverse really is a right inverse to the direct-limit
comparison map on `A = A₀ ⊗[R₀] colim_i R_i`. -/
private theorem tensorStageDirectLimitToColimit_leftInverse :
    (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (tensorStageDirectLimitInverse (F := F) (i₀ := i₀) (A₀ := A₀)) =
      RingHom.id (A₀ ⊗[F.obj i₀] ringColimit F) := by
  -- Proof comment: evaluate the composite on the left and right tensor generators separately.
  apply Algebra.TensorProduct.ext_ring
  · ext a
    simp [tensorStageDirectLimitInverse, RingHom.comp_apply,
      tensorStageDirectLimitToColimit_comp_leftMap, Algebra.TensorProduct.includeLeft_apply]
  · ext r
    simpa [tensorStageDirectLimitInverse, RingHom.comp_apply,
      Algebra.TensorProduct.includeRight_apply] using
      congrArg
        (fun f :
          ringColimit F →+* (A₀ ⊗[F.obj i₀] ringColimit F) ↦ f r)
        (tensorStageDirectLimitToColimit_comp_fromColimitRight
          (F := F) (i₀ := i₀) (A₀ := A₀))

/-- Helper for Lemma 15.84.7: the explicit inverse is also a left inverse, so the direct limit of
the tensor-stage rings is canonically equal to the final tensor product `A₀ ⊗[R₀] colim_i R_i`. -/
private theorem tensorStageDirectLimitToColimit_rightInverse :
    (tensorStageDirectLimitInverse (F := F) (i₀ := i₀) (A₀ := A₀)).comp
        (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)) =
      RingHom.id (tensorStageDirectLimit F i₀ A₀) := by
  ext x
  -- Proof comment: every element of the direct limit comes from one stage, and on each stage leg
  -- the composite is the identity by the previous tensor-generator computation.
  refine Ring.DirectLimit.induction_on x ?_
  intro j y
  simpa [RingHom.comp_apply] using
    congrArg
      (fun f : A₀ ⊗[F.obj i₀] F.obj j.1 →+* tensorStageDirectLimit F i₀ A₀ ↦ f y)
      (tensorStageDirectLimitInverse_comp_stageToColimitTensorMap
        (F := F) (i₀ := i₀) (A₀ := A₀) j)

/-- Helper for Lemma 15.84.7: the direct-limit comparison map is an `A₀`-algebra homomorphism. -/
private noncomputable def tensorStageDirectLimitToColimitAlgHom :
    tensorStageDirectLimit F i₀ A₀ →ₐ[A₀] (A₀ ⊗[F.obj i₀] ringColimit F) where
  toRingHom := tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)
  commutes' a := by
    -- Proof comment: this is exactly the previously verified compatibility with the left tensor
    -- factor.
    simpa [RingHom.comp_apply] using
      congrArg
        (fun f : A₀ →+* (A₀ ⊗[F.obj i₀] ringColimit F) ↦ f a)
        (tensorStageDirectLimitToColimit_comp_leftMap
          (F := F) (i₀ := i₀) (A₀ := A₀))

/-- Helper for Lemma 15.84.7: every tensor over the colimit ring is already represented by some
stage tensor `A₀ ⊗[R₀] R_j` inside the direct limit of the tensor-stage rings. -/
private theorem tensorStageDirectLimitToColimit_surjective :
    Function.Surjective (tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)) := by
  let ψ := tensorStageDirectLimitToColimit (F := F) (i₀ := i₀) (A₀ := A₀)
  intro x
  letI : PreservesFilteredColimits (forget CommRingCat) := by
    infer_instance
  letI : PreservesFilteredColimitsOfSize.{v, u} (forget CommRingCat) := by
    infer_instance
  letI : PreservesColimit F (forget CommRingCat) := by
    infer_instance
  -- Proof comment: descend the right tensor factor to one ring stage, then move that stage into
  -- the tail system `j ≥ i₀` using filteredness.
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    simp [ψ]
  · intro a r
    obtain ⟨i, ri, hri⟩ := Concrete.colimit_exists_rep F r
    obtain ⟨k, hi₀k, hik⟩ := exists_ge_ge i₀ i
    let j : Set.Ici i₀ := ⟨k, hi₀k⟩
    refine ⟨Ring.DirectLimit.of
        (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
        (fun l m h ↦ stageTransitionTensorMap F i₀ A₀ h)
        j (a ⊗ₜ[F.obj i₀] (F.map (homOfLE hik)).hom ri), ?_⟩
    -- Proof comment: on a pure tensor, the image is the same pure tensor after replacing the
    -- colimit element by the chosen stage representative.
    calc
      ψ
          (Ring.DirectLimit.of
            (fun l : Set.Ici i₀ ↦ A₀ ⊗[F.obj i₀] F.obj l.1)
            (fun l m h ↦ stageTransitionTensorMap F i₀ A₀ h)
            j (a ⊗ₜ[F.obj i₀] (F.map (homOfLE hik)).hom ri)) =
        stageToColimitTensorMap F i₀ A₀ j
          (a ⊗ₜ[F.obj i₀] (F.map (homOfLE hik)).hom ri) := by
            simpa [RingHom.comp_apply] using
              congrArg
                (fun f :
                  A₀ ⊗[F.obj i₀] F.obj j.1 →+*
                    (A₀ ⊗[F.obj i₀] ringColimit F) ↦
                  f (a ⊗ₜ[F.obj i₀] (F.map (homOfLE hik)).hom ri))
                (tensorStageDirectLimitToColimit_comp_of
                  (F := F) (i₀ := i₀) (A₀ := A₀) j)
      _ = a ⊗ₜ[F.obj i₀] ((colimit.ι F k).hom ((F.map (homOfLE hik)).hom ri)) := by
            simp [stageToColimitTensorMap, j]
      _ = a ⊗ₜ[F.obj i₀] (colimit.ι F i ri) := by
            congr 1
            simpa using
              congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hik)).symm
      _ = a ⊗ₜ[F.obj i₀] r := by rw [hri]
  · intro x y hx hy
    rcases hx with ⟨x', rfl⟩
    rcases hy with ⟨y', rfl⟩
    refine ⟨x' + y', ?_⟩
    simp [ψ, map_add]

/-- Helper for Lemma 15.84.7: the direct limit of the tensor-stage rings is canonically
`A₀`-algebra isomorphic to the final tensor product `A₀ ⊗[R₀] colim_i R_i`. This is the explicit
source-faithful bridge needed for the later bounded-complex descent. -/
private noncomputable def tensorStageDirectLimitAlgEquiv :
    tensorStageDirectLimit F i₀ A₀ ≃ₐ[A₀] (A₀ ⊗[F.obj i₀] ringColimit F) :=
  AlgEquiv.ofBijective
    (tensorStageDirectLimitToColimitAlgHom (F := F) (i₀ := i₀) (A₀ := A₀))
    ⟨by
      intro x y hxy
      have happly := congrArg
        (tensorStageDirectLimitInverse (F := F) (i₀ := i₀) (A₀ := A₀))
        hxy
      simpa [tensorStageDirectLimitToColimit_rightInverse, RingHom.comp_apply] using happly,
      tensorStageDirectLimitToColimit_surjective (F := F) (i₀ := i₀) (A₀ := A₀)⟩

/-- Helper for Lemma 15.84.7: the direct base change `A_j → A` agrees with first passing to a
later stage `A_k` and then to the colimit tensor stage ring. -/
private noncomputable abbrev stageToColimitThroughTransitionBaseChangeIso
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k ≅
      stageToColimitBaseChange F i₀ A₀ j :=
  derivedTensorWithAlgebraCompIso
    (stageTransitionTensorMap F i₀ A₀ h)
    (stageToColimitTensorMap F i₀ A₀ k)
    (stageToColimitTensorMap F i₀ A₀ j)
    (stageToColimitThroughTransitionTensorMap_comp_eq F i₀ A₀ h)

/-- The canonical image in the colimit Hom-set of a stagewise morphism. -/
noncomputable def stageToColimitHomMap (j : Set.Ici i₀)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) :=
  let e := stageToColimitBaseChangeIso F i₀ A₀ j
  (e.app K₀).inv ≫ (stageToColimitBaseChange F i₀ A₀ j).map β ≫ (e.app L₀).hom

/-- The canonical image in a later-stage Hom-set of a stagewise morphism. -/
noncomputable def stageTransitionHomMap {j k : Set.Ici i₀} (h : j ⟶ k)
    {K₀ L₀ : DModA0}
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) ⟶
      (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj k.1]) :=
  let e := stageTransitionBaseChangeIso F i₀ A₀ h
  (e.app K₀).inv ≫ (stageTransitionBaseChange F i₀ A₀ h).map β ≫ (e.app L₀).hom

/-- Helper for Lemma 15.84.7: transporting first to a later stage and then to the colimit tensor
stage ring is a single conjugation by the whiskered transition comparison. -/
private theorem stageToColimitHomMap_through_whiskered_transition
    {K₀ L₀ : DModA0}
    {j k : Set.Ici i₀} (h : j ⟶ k)
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    stageToColimitHomMap F i₀ A₀ k (stageTransitionHomMap F i₀ A₀ h β) =
      let eK :=
        (stageToColimitBaseChange F i₀ A₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ A₀ h).app K₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ A₀ k).app K₀
      let eL :=
        (stageToColimitBaseChange F i₀ A₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ A₀ h).app L₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ A₀ k).app L₀
      eK.inv ≫
        ((stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k).map β) ≫
          eL.hom := by
  -- Proof comment: collapse the two successive conjugations into the single whiskered comparison
  -- isomorphism attached to `A_j → A_k → A`.
  simpa [stageToColimitHomMap, stageTransitionHomMap, Functor.mapIso, Functor.comp_map,
    Category.assoc]

/-- Helper for Lemma 15.84.7: replacing the last two tensor base changes by the direct
comparison `A_j → A` recovers the original direct map to the colimit tensor stage ring. -/
private theorem stageToColimitHomMap_through_stageToColimitComparison
    {K₀ L₀ : DModA0}
    {j k : Set.Ici i₀} (h : j ⟶ k)
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    stageToColimitHomMap F i₀ A₀ j β =
      let eK :=
        (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
          ((stageBaseChange F i₀ A₀ j).obj K₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ A₀ j).app K₀
      let eL :=
        (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
          ((stageBaseChange F i₀ A₀ j).obj L₀) ≪≫
            (stageToColimitBaseChangeIso F i₀ A₀ j).app L₀
      eK.inv ≫
        ((stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k).map β) ≫
          eL.hom := by
  -- Proof comment: regroup the three-step tensor extension, then use naturality of the direct
  -- `A_j → A` comparison isomorphism.
  dsimp [stageToColimitHomMap]
  have hmiddle :
      (stageToColimitBaseChange F i₀ A₀ j).map β =
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
            ((stageBaseChange F i₀ A₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
              ((stageBaseChange F i₀ A₀ j).obj L₀)).hom := by
    -- This is the naturality square of the direct `A_j → A` comparison iso.
    have hnat :=
      (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).hom.naturality β
    have hmiddle' :
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
            ((stageBaseChange F i₀ A₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
              ((stageBaseChange F i₀ A₀ j).obj L₀)).hom =
          (stageToColimitBaseChange F i₀ A₀ j).map β := by
      calc
        ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
            ((stageBaseChange F i₀ A₀ j).obj K₀)).inv ≫
          ((stageTransitionBaseChange F i₀ A₀ h ⋙ stageToColimitBaseChange F i₀ A₀ k).map β) ≫
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
              ((stageBaseChange F i₀ A₀ j).obj L₀)).hom =
            ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
                ((stageBaseChange F i₀ A₀ j).obj K₀)).inv ≫
              ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
                ((stageBaseChange F i₀ A₀ j).obj K₀)).hom ≫
                (stageToColimitBaseChange F i₀ A₀ j).map β := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
                        ((stageBaseChange F i₀ A₀ j).obj K₀)).inv ≫ f)
                  hnat
        _ = (stageToColimitBaseChange F i₀ A₀ j).map β := by
              simpa using
                (Iso.inv_hom_id_assoc
                  ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
                    ((stageBaseChange F i₀ A₀ j).obj K₀))
                  ((stageToColimitBaseChange F i₀ A₀ j).map β))
    exact hmiddle'.symm
  rw [hmiddle]
  simp [Category.assoc]

/-- Helper for Lemma 15.84.7: the homotopy-level scalar extension from `A₀` to the colimit tensor
stage ring whose total left derived functor is `colimitBaseChange`. -/
private noncomputable abbrev stageToColimitHomotopyFunctor :
    HomotopyCategory (ModuleCat A₀) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F)) :=
  let F₀ : ModuleCat A₀ ⥤ ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F) :=
    ModuleCat.extendScalars (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))
  letI : F₀.Additive :=
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F))).left_adjoint_additive
  mapHomotopyCategoryToDerived F₀

/-- Helper for Lemma 15.84.7: the direct homotopy scalar-extension bridge `A₀ → A` admits the
expected total left derived functor. -/
private theorem stageToColimitHomotopyFunctor_hasLeftDerivedFunctor :
    (stageToColimitHomotopyFunctor F i₀ A₀).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat A₀) (ComplexShape.up ℤ)) := by
  -- Proof comment: this is exactly the owner theorem for ordinary extension of scalars to the
  -- derived category, specialized to the tensor-stage colimit ring `A`.
  simpa [stageToColimitHomotopyFunctor, mapHomotopyCategoryToDerived] using
    (extendScalarsToDerived_hasLeftDerivedFunctor
      (algebraMap A₀ (A₀ ⊗[F.obj i₀] ringColimit F)))

/-- Helper for Lemma 15.84.7: whiskering the forward map of `leftDerivedNatIso` by the
localization functor and then composing with the target counit recovers the original
prederived comparison morphism. -/
private theorem Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {W : MorphismProperty C} [L.IsLocalization W]
    {F F' : C ⥤ H} {LF LF' : D ⥤ H}
    {α : L ⋙ LF ⟶ F} {α' : L ⋙ LF' ⟶ F'}
    [LF.IsLeftDerivedFunctor α W] [LF'.IsLeftDerivedFunctor α' W]
    (e : F' ≅ F) :
    Functor.whiskerLeft L (Functor.leftDerivedNatIso LF' LF α' α W e).hom ≫ α =
      α' ≫ e.hom := by
  -- Proof comment: expand `leftDerivedNatIso` to the underlying `leftDerivedNatTrans`, then use
  -- the defining left-derived factorization identity.
  simpa [Functor.leftDerivedNatIso] using
    (Functor.leftDerivedNatTrans_fac LF' LF α' α W e.hom)

/-- Helper for Lemma 15.84.7: after whiskering by `Qh` and postcomposing with the direct colimit
tensor-stage counit, the two parenthesizations of the three-step scalar-extension comparison
reduce to the same homotopy-level normalization problem. -/
private theorem stageToColimitComparison_assoc_coherence_qh_normalized
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    let qhA₀ :
        HomotopyCategory (ModuleCat A₀) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat A₀) :=
      DerivedCategory.Qh
    let qisA₀ :=
      HomotopyCategory.quasiIso (ModuleCat A₀) (ComplexShape.up ℤ)
    letI :
        (stageToColimitHomotopyFunctor F i₀ A₀).HasLeftDerivedFunctor qisA₀ :=
      stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀) (A₀ := A₀)
    Functor.whiskerLeft qhA₀
        (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ A₀ h)
              (stageToColimitBaseChange F i₀ A₀ k)) ≪≫
            stageToColimitBaseChangeIso F i₀ A₀ k).hom) ≫
          Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ =
      Functor.whiskerLeft qhA₀
        (((Functor.isoWhiskerLeft (stageBaseChange F i₀ A₀ j)
              (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h)) ≪≫
            stageToColimitBaseChangeIso F i₀ A₀ j).hom) ≫
          Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ := by
  -- Route correction: the opaque tail is again the `leftDerivedNatIso` inside
  -- `derivedTensorWithAlgebraCompIso`. Composing with the total-left-derived counit reduces both
  -- sides to the visible homotopy-level tensor-stage comparison data.
  dsimp [stageTransitionBaseChangeIso, stageToColimitBaseChangeIso,
    stageToColimitThroughTransitionBaseChangeIso]
  rw [Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit,
    Functor.leftDerivedNatIso_hom_assoc_totalLeftDerivedCounit]
  simp [derivedTensorWithAlgebraCompIso, stageTransitionTensorMap_comp_eq,
    stageToColimitThroughTransitionTensorMap_comp_eq, stageToColimitTensorMap_comp_eq,
    Category.assoc]

/-- Helper for Lemma 15.84.7: the direct stage-to-colimit tensor base change is determined by
its `Qh`-whiskered counit composite. -/
private theorem leftDerived_hom_ext_of_qh_counit_equality
    {G :
      DerivedCategory (ModuleCat A₀) ⥤
        DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] ringColimit F))}
    (η θ : G ⟶ colimitBaseChange F i₀ A₀) :
    let qhA₀ :
        HomotopyCategory (ModuleCat A₀) (ComplexShape.up ℤ) ⥤
          DerivedCategory (ModuleCat A₀) :=
      DerivedCategory.Qh
    let qisA₀ :=
      HomotopyCategory.quasiIso (ModuleCat A₀) (ComplexShape.up ℤ)
    letI :
        (stageToColimitHomotopyFunctor F i₀ A₀).HasLeftDerivedFunctor qisA₀ :=
      stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀) (A₀ := A₀)
    Functor.whiskerLeft qhA₀ η ≫
        Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ =
      Functor.whiskerLeft qhA₀ θ ≫
        Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ →
      η = θ := by
  intro qhA₀ qisA₀ hηθ
  letI :
      (stageToColimitHomotopyFunctor F i₀ A₀).HasLeftDerivedFunctor qisA₀ :=
    stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀) (A₀ := A₀)
  -- Proof comment: upgrade the direct `A₀ → A` tensor base change to the canonical
  -- left-derived owner for the homotopy-level scalar-extension bridge.
  letI :
      (colimitBaseChange F i₀ A₀).IsLeftDerivedFunctor
        (Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀)
        qisA₀ := by
    change
      (Functor.totalLeftDerived
        (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀).IsLeftDerivedFunctor
          (Functor.totalLeftDerivedCounit
            (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀)
          qisA₀
    infer_instance
  -- Proof comment: the right Kan extension universal property says equality after whiskering by
  -- `Qh` and composing with the counit already determines the map into the derived functor.
  let hkan :
      (colimitBaseChange F i₀ A₀).IsRightKanExtension
        (Functor.totalLeftDerivedCounit
          (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀) :=
    Functor.IsLeftDerivedFunctor.isRightKanExtension
      (LF := colimitBaseChange F i₀ A₀)
      (α := Functor.totalLeftDerivedCounit
        (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀)
      (W := qisA₀)
  obtain ⟨huniv⟩ := hkan.nonempty_isUniversal
  exact huniv.hom_ext hηθ

/-- Helper for Lemma 15.84.7: the two canonical comparison isomorphisms from the three-step
scalar extension `A₀ → A_j → A_k → A` to the direct scalar extension `A₀ → A` agree on forward
morphisms. -/
private theorem stageToColimitComparison_assoc_coherence_hom
    {X : DModA0}
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    (((stageToColimitBaseChange F i₀ A₀ k).mapIso
          ((stageTransitionBaseChangeIso F i₀ A₀ h).app X) ≪≫
        (stageToColimitBaseChangeIso F i₀ A₀ k).app X).hom) =
      (((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
            ((stageBaseChange F i₀ A₀ j).obj X) ≪≫
          (stageToColimitBaseChangeIso F i₀ A₀ j).app X).hom) := by
  let qhA₀ :
      HomotopyCategory (ModuleCat A₀) (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat A₀) :=
    DerivedCategory.Qh
  let qisA₀ :=
    HomotopyCategory.quasiIso (ModuleCat A₀) (ComplexShape.up ℤ)
  letI :
      (stageToColimitHomotopyFunctor F i₀ A₀).HasLeftDerivedFunctor qisA₀ :=
    stageToColimitHomotopyFunctor_hasLeftDerivedFunctor (F := F) (i₀ := i₀) (A₀ := A₀)
  have hnormalized :
      Functor.whiskerLeft qhA₀
          (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ A₀ h)
                (stageToColimitBaseChange F i₀ A₀ k)) ≪≫
              stageToColimitBaseChangeIso F i₀ A₀ k).hom) ≫
            Functor.totalLeftDerivedCounit
              (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ =
        Functor.whiskerLeft qhA₀
          (((Functor.isoWhiskerLeft (stageBaseChange F i₀ A₀ j)
                (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h)) ≪≫
              stageToColimitBaseChangeIso F i₀ A₀ j).hom) ≫
            Functor.totalLeftDerivedCounit
              (stageToColimitHomotopyFunctor F i₀ A₀) qhA₀ qisA₀ :=
    stageToColimitComparison_assoc_coherence_qh_normalized (F := F) (i₀ := i₀) (A₀ := A₀) h
  -- Route correction: once the normalized `Qh`-side equality is proved, the app-level statement
  -- follows by the left-derived uniqueness principle exactly as in the absolute case.
  have hcomparison :
      (((Functor.isoWhiskerRight (stageTransitionBaseChangeIso F i₀ A₀ h)
            (stageToColimitBaseChange F i₀ A₀ k)) ≪≫
          stageToColimitBaseChangeIso F i₀ A₀ k).hom) =
        (((Functor.isoWhiskerLeft (stageBaseChange F i₀ A₀ j)
              (stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h)) ≪≫
            stageToColimitBaseChangeIso F i₀ A₀ j).hom) := by
    apply leftDerived_hom_ext_of_qh_counit_equality (F := F) (i₀ := i₀) (A₀ := A₀)
    exact hnormalized
  -- Proof comment: evaluate the recovered natural-transformation equality at the object `X`.
  simpa using congrArg (fun τ ↦ τ.app X) hcomparison

/-- Helper for Lemma 15.84.7: once the comparison morphisms agree, the two corresponding
three-step tensor-stage comparison isomorphisms are equal. -/
private theorem stageToColimitComparison_assoc_coherence
    {X : DModA0}
    {j k : Set.Ici i₀} (h : j ⟶ k) :
    ((stageToColimitBaseChange F i₀ A₀ k).mapIso
        ((stageTransitionBaseChangeIso F i₀ A₀ h).app X) ≪≫
      (stageToColimitBaseChangeIso F i₀ A₀ k).app X) =
      ((stageToColimitThroughTransitionBaseChangeIso F i₀ A₀ h).app
          ((stageBaseChange F i₀ A₀ j).obj X) ≪≫
        (stageToColimitBaseChangeIso F i₀ A₀ j).app X) := by
  -- Proof comment: reduce the comparison of isomorphisms to the equality of their forward
  -- morphisms.
  apply Iso.ext
  exact stageToColimitComparison_assoc_coherence_hom
    (F := F) (i₀ := i₀) (A₀ := A₀) (X := X) h

-- Proof sketch: the cocone relation `R_j → R_k → colim F = R_j → colim F` induces the matching
-- equality for the tensor-product ring maps `A_j → A_k → A = A_j → A`. Naturality of the
-- iterated-vs-direct comparison isomorphisms then identifies the two induced maps on Hom-sets.
/-- The canonical images in the colimit Hom-set are compatible with transition to later stages.
This is the coherence needed for the source-facing filtered Hom-colimit comparison in
Lemma `15.84.7 (2)`. -/
@[stacks 0DHX]
theorem stageToColimitHomMap_transition
    {K₀ L₀ : DModA0} {j k : Set.Ici i₀} (h : j ⟶ k)
    (β :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])) :
    stageToColimitHomMap F i₀ A₀ k (stageTransitionHomMap F i₀ A₀ h β) =
      stageToColimitHomMap F i₀ A₀ j β := by
  -- Route correction: isolate the formal transport identities first, so the remaining work is
  -- exactly the tensor-stage associativity coherence for `A₀ → A_j → A_k → A`.
  rw [stageToColimitHomMap_through_whiskered_transition (F := F) (i₀ := i₀) (A₀ := A₀) h β]
  rw [stageToColimitHomMap_through_stageToColimitComparison
    (F := F) (i₀ := i₀) (A₀ := A₀) h β]
  -- Proof comment: apply the coherence of the three comparison isomorphisms to the source and
  -- target objects separately, then both transport formulas become definitionally identical.
  have hK :=
    stageToColimitComparison_assoc_coherence
      (F := F) (i₀ := i₀) (A₀ := A₀) (X := K₀) h
  have hL :=
    stageToColimitComparison_assoc_coherence
      (F := F) (i₀ := i₀) (A₀ := A₀) (X := L₀) h
  rw [hK, hL]
  rfl

section

variable [Module.Flat (F.obj i₀) A₀] [Algebra.FinitePresentation (F.obj i₀) A₀]

local notation "Acolim" => A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})
local notation "DModAcolim" => DerivedCategory (ModuleCat Acolim)
local notation "BoundedCpxAcolim" => Compᵇ((ModuleCat Acolim))
local notation "CpxA0" => CochainComplex (ModuleCat A₀) ℤ
local notation "MinusCpxA0" => CochainComplex.minus (ModuleCat A₀)

/-- Helper for Lemma 15.84.7: a bounded representative over
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i` whose terms are `R`-flat and finitely presented over
`A` descends to one tensor stage `A_j = A₀ ⊗[R₀] R_j`. -/
private theorem bounded_flat_finitePresentation_complex_descends_to_tensor_stage
    (P : BoundedCpxAcolim)
    (hFlat :
      CochainComplex.IsTermwiseFlat
        (((ModuleCat.restrictScalars
          (algebraMap (colimit F : CommRingCat.{u}) Acolim)).mapHomologicalComplex
            (up ℤ)).obj P.obj))
    (hFinite : ∀ n : ℤ, Module.FinitePresentation Acolim (P.obj.X n)) :
    ∃ (j : Set.Ici i₀)
      (Pj : Compᵇ((ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)))),
      CochainComplex.IsTermwiseFlat
        (((ModuleCat.restrictScalars
          (algebraMap (F.obj j.1) (A₀ ⊗[F.obj i₀] F.obj j.1))).mapHomologicalComplex
            (up ℤ)).obj Pj.obj) ∧
      (∀ n : ℤ,
        Module.FinitePresentation (A₀ ⊗[F.obj i₀] F.obj j.1) (Pj.obj.X n)) ∧
      IsIsomorphic (DerivedCategory.Q.obj P.obj)
        (DerivedCategory.Q.obj Pj.obj ⊗[A₀ ⊗[F.obj i₀] F.obj j.1]^L[Acolim]) := by
  let _ := hFlat
  let _ := hFinite
  -- TODO: first identify `Acolim` with the direct limit of the tensor-stage rings
  -- `A₀ ⊗[R₀] R_j`, then descend the finite support window of `P` termwise, descend the finitely
  -- many differentials, and finally stabilize the finitely many relations `d ≫ d = 0`.
  sorry

-- Proof sketch: combine the finite-presentation descent for flat finitely presented modules with
-- the representative criterion for `R`-perfect objects from Lemma `15.84.4`, then descend the
-- finitely many terms of a bounded representative to some stage `j ≥ i₀`.
/-- Lemma 15.84.7 (1): for `A_j = A₀ ⊗[R₀] R_j` and
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i`, every object of `D(A)` that is perfect over the
colimit ring descends to some stage as an object of `D(A_j)` that is perfect over `R_j`. -/
@[stacks 0DHX]
theorem exists_stage_of_isPerfectOver_filtered_base_change
    (K : DModAcolim)
    (hK : DerivedCategory.IsPerfectOver (colimit F : CommRingCat.{u}) K) :
    ∃ (j : Set.Ici i₀) (Kj : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1))),
      DerivedCategory.IsPerfectOver (F.obj j.1) Kj ∧
        IsIsomorphic K
          (Kj ⊗[A₀ ⊗[F.obj i₀] F.obj j.1]^L[
            Acolim]) := by
  -- Proof comment: first choose the bounded termwise-flat finitely presented representative given
  -- by Lemma `15.84.4`, then descend that single strict complex to one tensor stage.
  rcases
      (isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
        (R := (colimit F : CommRingCat.{u})) K).1 hK with
    ⟨P, hPflat, hPfinite, hPiso⟩
  obtain ⟨j, Pj, hPjflat, hPjfinite, hdesc⟩ :=
    bounded_flat_finitePresentation_complex_descends_to_tensor_stage
      (F := F) (i₀ := i₀) (A₀ := A₀) P hPflat hPfinite
  let Kj : DerivedCategory (ModuleCat (A₀ ⊗[F.obj i₀] F.obj j.1)) :=
    DerivedCategory.Q.obj Pj.obj
  have hKj : DerivedCategory.IsPerfectOver (F.obj j.1) Kj := by
    -- Proof comment: the descended strict stage complex already has the stagewise flatness and
    -- finite-presentation hypotheses required by the converse direction of Lemma `15.84.4`.
    refine
      (isPerfectOver_iff_exists_bounded_flat_finitePresentation_representative
        (R := F.obj j.1) Kj).2 ?_
    refine ⟨Pj, hPjflat, hPjfinite, ?_⟩
    exact ⟨Iso.refl _⟩
  rcases hPiso with ⟨eP⟩
  rcases hdesc with ⟨eDesc⟩
  refine ⟨j, Kj, hKj, ?_⟩
  -- Proof comment: compose the original identification of `K` with its bounded representative and
  -- the descended-stage comparison isomorphism.
  exact ⟨eP ≪≫ eDesc⟩

/-- Helper for Lemma 15.84.7: a pseudo-coherent source object of `D(A₀)` admits the bounded-above
termwise finite-free model used in the source proof of the Hom-colimit statements. -/
private theorem exists_boundedAbove_termwiseFiniteFree_representative_of_pseudoCoherent
    (K₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent) :
    ∃ P₀ : CpxA0,
      MinusCpxA0 P₀ ∧
        P₀.IsTermwiseFiniteFree ∧
        IsIsomorphic (DerivedCategory.Q.obj P₀) K₀ := by
  rcases hK₀ with ⟨P₀, ⟨b, hP₀strictLE⟩, hP₀finiteFree, ⟨α, hαiso⟩⟩
  refine ⟨P₀, ?_, hP₀finiteFree, ?_⟩
  · -- Proof comment: repackage the strict upper bound from the pseudo-coherent witness as the
    -- bounded-above owner expected by the fixed Hom-complex API.
    exact (CochainComplex.minus_iff (ModuleCat A₀) P₀).2 ⟨b, hP₀strictLE⟩
  · -- Proof comment: the quasi-isomorphism recorded in the pseudo-coherent witness is already the
    -- required derived isomorphism to `K₀`.
    exact ⟨asIso α⟩

/-- Helper for Lemma 15.84.7: the finite-tor-dimension hypothesis on `L₀` supplies one explicit
tor-amplitude interval for its restriction to the base ring `R₀`. -/
private theorem exists_torAmplitude_interval_of_restrict_hasFiniteTorDimension
    (L₀ : DModA0)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀)) :
    ∃ a b : ℤ,
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀)
        a b := by
  rcases hL₀ with ⟨a, b, hAmp⟩
  -- Proof comment: `HasFiniteTorDimension` is by definition the existence of one tor-amplitude
  -- interval, so no further transport is needed here.
  exact ⟨a, b, hAmp⟩

/-- Helper for Lemma 15.84.7: restricting scalars preserves a lower strict support bound on a
cochain complex over `A₀`. -/
private lemma restrictScalarsComplex_isStrictlyGE
    {E : CpxA0} {a : ℤ}
    (hE : E.IsStrictlyGE a) :
    (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapHomologicalComplex
      (up ℤ)).obj E).IsStrictlyGE a := by
  -- Proof comment: read the lower support degreewise and transport zero objects through
  -- restriction of scalars.
  rw [CochainComplex.isStrictlyGE_iff] at hE ⊢
  intro i hi
  change
    IsZero
      (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).obj (E.X i) :
          ModuleCat (F.obj i₀)))
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using hE i hi

/-- Helper for Lemma 15.84.7: restricting scalars preserves an upper strict support bound on a
cochain complex over `A₀`. -/
private lemma restrictScalarsComplex_isStrictlyLE
    {E : CpxA0} {b : ℤ}
    (hE : E.IsStrictlyLE b) :
    (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapHomologicalComplex
      (up ℤ)).obj E).IsStrictlyLE b := by
  -- Proof comment: the same degreewise transport preserves the upper vanishing range.
  rw [CochainComplex.isStrictlyLE_iff] at hE ⊢
  intro i hi
  change
    IsZero
      (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).obj (E.X i) :
          ModuleCat (F.obj i₀)))
  simpa [CategoryTheory.Functor.mapHomologicalComplex_obj_X] using hE i hi

/-- Helper for Lemma 15.84.7: above the cutoff, smart lower truncation keeps the original term of
an `A₀`-complex. -/
private noncomputable def truncGE_term_iso_of_gt
    (K : CpxA0) (a n : ℤ) (han : a < n) :
    (K.truncGE a).X n ≅ K.X n := by
  let i : ℕ := Int.toNat (n - a)
  have hi' : (ComplexShape.embeddingUpIntGE a).f i = n := by
    exact embeddingUpIntGE_toNat_sub_eq a n (le_of_lt han)
  have hboundary : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE i := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
    intro hi0
    have hEq : a = n := by
      simpa [i, hi0, ComplexShape.embeddingUpIntGE] using hi'
    omega
  -- Proof comment: the standard truncation API identifies every term strictly above the cutoff
  -- with the original one.
  exact K.truncGEXIso (e := ComplexShape.embeddingUpIntGE a) hi' hboundary

/-- Helper for Lemma 15.84.7: smart lower truncation of a bounded-above `A₀`-complex remains
bounded above, with a uniform cutoff `max a b`. -/
private theorem truncGE_isStrictlyLE_of_isStrictlyLE
    (K : CpxA0) (a b : ℤ) (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE (max a b) := by
  -- Proof comment: for every degree above `max a b`, the truncation term is identified with the
  -- original term, and the original complex already vanishes there.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have han : a < n := lt_of_le_of_lt (le_max_left a b) hn
  exact ((truncGE_term_iso_of_gt (K := K) a n han).isZero_iff).2 <| by
    rw [CochainComplex.isStrictlyLE_iff] at hK
    exact hK n (lt_of_le_of_lt (le_max_right a b) hn)

/-- Helper for Lemma 15.84.7: zero modules over the base ring are flat. -/
private theorem flat_of_isZero_module_over_base
    (M : ModuleCat (F.obj i₀)) (hM : IsZero M) :
    Module.Flat (F.obj i₀) M := by
  -- Proof comment: a zero module is linearly equivalent to the literal zero module, which is
  -- free and therefore flat.
  let Z : ModuleCat (F.obj i₀) := ModuleCat.of (F.obj i₀) PUnit
  have hZ : IsZero Z := ModuleCat.isZero_of_subsingleton Z
  letI : Subsingleton ↥Z := ModuleCat.subsingleton_of_isZero hZ
  letI : Module.Free (F.obj i₀) ↥Z :=
    Module.Free.of_subsingleton (R := F.obj i₀) (N := ↥Z)
  let _ : Module.Flat (F.obj i₀) Z := Module.Flat.of_free
  let e : M ≅ Z := hM.iso hZ
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- Helper for Lemma 15.84.7: a projective `A₀`-module is flat over the base ring `R₀` after
restriction of scalars, because `A₀` is flat over `R₀`. -/
private theorem projective_restrictScalars_flat
    (M : ModuleCat A₀) [Projective M] :
    Module.Flat (F.obj i₀)
      ((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).obj M) := by
  -- Proof comment: projective modules are flat over `A₀`, and flatness composes across the flat
  -- algebra map `R₀ → A₀`.
  let _ : Module.Flat A₀ M := Module.Flat.of_projective
  simpa using (Module.Flat.trans (F.obj i₀) A₀ M)

/-- Helper for Lemma 15.84.7: a tor-amplitude interval on the restricted object
`L₀|_{R₀}` should be realized by a bounded `A₀`-complex whose restricted terms are flat over
`R₀`. -/
private theorem exists_bounded_termwiseFlat_representative_over_base_of_torAmplitude
    (L₀ : DModA0) {a b : ℤ}
    (hL₀amp :
      HasTorAmplitudeIn
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀)
        a b) :
    ∃ F₀ : CpxA0,
      CochainComplex.bounded (ModuleCat A₀) F₀ ∧
      CochainComplex.IsTermwiseFlat
          (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapHomologicalComplex
            (up ℤ)).obj F₀) ∧
        IsIsomorphic (DerivedCategory.Q.obj F₀) L₀ := by
  let Res := ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)
  let ResCpx := Res.mapHomologicalComplex (up ℤ)
  let ResDer := Res.mapDerivedCategory
  let E : CpxA0 := DerivedCategory.Q.objPreimage L₀
  have hEabove : ∀ i : ℤ, b < i → IsZero (E.homology i) := by
    intro i hi
    -- Proof comment: upper homology vanishing is first read after restriction to the base ring
    -- and then reflected back through restriction of scalars.
    have hzeroL :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat (F.obj i₀)) i).obj
          (ResDer.obj L₀)) :=
      homology_isZero_of_hasTorAmplitudeIn_above
        (R := F.obj i₀) (ResDer.obj L₀) a b i hL₀amp hi
    have hzeroRE :
        IsZero ((ResCpx.obj E).homology i) := by
      exact
        ((DerivedCategory.homologyFunctorFactors (ModuleCat (F.obj i₀)) i).app
          (ResCpx.obj E)).isZero_iff.1 <|
            hzeroL.of_iso <|
              ((DerivedCategory.homologyFunctor (ModuleCat (F.obj i₀)) i).mapIso
                (((ResDer.mapIso (DerivedCategory.Q.objObjPreimageIso L₀)).symm) ≪≫
                  (Res.mapDerivedCategoryFactors.app E)))
    have hzeroResHom :
        IsZero (Res.obj (E.homology i)) := by
      exact hzeroRE.of_iso ((E.sc i).mapHomologyIso Res).symm
    exact
      isZero_of_restrictScalars_obj
        (f := algebraMap (F.obj i₀) A₀) (M := E.homology i) hzeroResHom
  have hELe : E.IsLE b := by
    -- Proof comment: vanishing of homology above `b` is the exact input required for the
    -- bounded-above projective replacement.
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hEabove i hi
  letI : E.IsLE b := hELe
  obtain ⟨P, hPLE, _⟩ :=
    exists_projectiveResolution_strictlyLE_with_termwise_epi
      (𝒜 := ModuleCat A₀) (K := E.truncLE b) b inferInstance
  let eP : DerivedCategory.Q.obj (P : CpxA0) ≅ L₀ :=
    (asIso (DerivedCategory.Q.map P.π)) ≪≫
      (asIso (DerivedCategory.Q.map (E.ιTruncLE b))) ≪≫
        (DerivedCategory.Q.objObjPreimageIso L₀)
  let RP : CochainComplex (ModuleCat (F.obj i₀)) ℤ := ResCpx.obj P
  have hRPflat : RP.IsTermwiseFlat := by
    -- Proof comment: every projective term of the chosen `A₀`-projective model is flat over the
    -- base ring after restriction of scalars.
    intro i
    let _ : Projective (P.X i) := inferInstance
    simpa [RP, ResCpx, Res] using
      projective_restrictScalars_flat (F := F) (i₀ := i₀) (A₀ := A₀) (M := P.X i)
  have hRPminus : CochainComplex.minus (ModuleCat (F.obj i₀)) RP := by
    -- Proof comment: the chosen projective model is strictly zero above `b`, and restriction of
    -- scalars preserves that upper support bound.
    exact
      (CochainComplex.minus_iff (ModuleCat (F.obj i₀)) RP).2
        ⟨b, restrictScalarsComplex_isStrictlyLE
          (F := F) (i₀ := i₀) (A₀ := A₀) hPLE⟩
  let eRes : ResDer.obj L₀ ≅ DerivedCategory.Q.obj RP :=
    (ResDer.mapIso eP.symm) ≪≫
      (Res.mapDerivedCategoryFactors.app (P : CpxA0))
  have hAmpRP : HasTorAmplitudeIn (DerivedCategory.Q.obj RP) a b := by
    -- Proof comment: transport the original interval to the restricted projective model.
    exact (hasTorAmplitudeIn_of_iso (R := F.obj i₀) eRes).1 hL₀amp
  have hPbelow : ∀ i : ℤ, i < a → IsZero (P.homology i) := by
    intro i hi
    -- Proof comment: lower homology vanishing is proved on the restricted derived object, then on
    -- the restricted strict model, and finally reflected back to the `A₀`-complex.
    have hzeroL :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat (F.obj i₀)) i).obj
          (ResDer.obj L₀)) :=
      homology_isZero_of_hasTorAmplitudeIn_below
        (R := F.obj i₀) (ResDer.obj L₀) a b i hL₀amp hi
    have hzeroQ :
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat (F.obj i₀)) i).obj
          (DerivedCategory.Q.obj RP)) := by
      exact hzeroL.of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat (F.obj i₀)) i).mapIso eRes)
    have hzeroRP : IsZero (RP.homology i) := by
      exact
        ((DerivedCategory.homologyFunctorFactors (ModuleCat (F.obj i₀)) i).app RP).isZero_iff.1
          hzeroQ
    have hzeroResHom : IsZero (Res.obj (P.homology i)) := by
      exact hzeroRP.of_iso ((P.sc i).mapHomologyIso Res).symm
    exact
      isZero_of_restrictScalars_obj
        (f := algebraMap (F.obj i₀) A₀) (M := P.homology i) hzeroResHom
  have hπ : QuasiIso (P.πTruncGE a) := by
    -- Proof comment: once the lower homology vanishes, smart lower truncation is a
    -- quasi-isomorphism.
    exact quasiIso_piTruncGE_of_isZero_homology_below a P hPbelow
  let F₀ : CpxA0 := P.truncGE a
  let RF₀ : CochainComplex (ModuleCat (F.obj i₀)) ℤ := ResCpx.obj F₀
  have hF₀GE : F₀.IsStrictlyGE a := by
    infer_instance
  have hF₀LE : F₀.IsStrictlyLE (max a b) := by
    -- Proof comment: the smart truncation keeps the original bounded-above support above the
    -- cutoff, so the result is still bounded.
    exact
      truncGE_isStrictlyLE_of_isStrictlyLE
        (F := F) (i₀ := i₀) (A₀ := A₀) P a b hPLE
  have hRF₀flat : RF₀.IsTermwiseFlat := by
    intro i
    by_cases hi_lt : i < a
    · have hRF₀GE :
          RF₀.IsStrictlyGE a :=
        restrictScalarsComplex_isStrictlyGE (F := F) (i₀ := i₀) (A₀ := A₀) hF₀GE
      rw [CochainComplex.isStrictlyGE_iff] at hRF₀GE
      have hzero : IsZero (RF₀.X i) := hRF₀GE i hi_lt
      -- Proof comment: degrees below the truncation cutoff are literally zero after restriction.
      exact
        flat_of_isZero_module_over_base
          (F := F) (i₀ := i₀) (A₀ := A₀) (M := RF₀.X i) hzero
    · by_cases hi_eq : i = a
      · subst hi_eq
        -- Proof comment: the new cutoff term is the standard cokernel controlled by the public
        -- flat cokernel theorem.
        simpa [RF₀, F₀] using
          CochainComplex.flat_cokernel_dFrom_of_boundedAbove_of_termwiseFlat_of_hasTorAmplitudeGE
            (R := F.obj i₀) RP a hRPminus hRPflat hAmpRP.hasTorAmplitudeGE
      · have hai : a < i := by
          omega
        let eF : RF₀.X i ≅ RP.X i :=
          Res.mapIso (truncGE_term_iso_of_gt (F := F) (i₀ := i₀) (A₀ := A₀) P a i hai)
        let _ : Module.Flat (F.obj i₀) (RP.X i : Type u) := hRPflat i
        have hRetract :
            eF.inv.hom.hom.comp eF.hom.hom = LinearMap.id := by
          ext x
          simp
        -- Proof comment: above the cutoff, the truncated term is a retract of the original
        -- projective-model term, so it inherits flatness over `R₀`.
        exact Module.Flat.of_retract eF.hom.hom eF.inv.hom.hom hRetract
  have hF₀bounded : CochainComplex.bounded (ModuleCat A₀) F₀ := by
    -- Proof comment: the lower truncation makes `F₀` bounded below by `a`, while the inherited
    -- upper cutoff is `max a b`.
    exact
      (CochainComplex.bounded_iff (ModuleCat A₀) F₀).2
        ⟨(CochainComplex.plus_iff (ModuleCat A₀) F₀).2 ⟨a, hF₀GE⟩,
          (CochainComplex.minus_iff (ModuleCat A₀) F₀).2 ⟨max a b, hF₀LE⟩⟩
  have hQπ : IsIso (DerivedCategory.Q.map (P.πTruncGE a)) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hπ
  let eF₀ : DerivedCategory.Q.obj F₀ ≅ L₀ :=
    (asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP
  exact ⟨F₀, hF₀bounded, hRF₀flat, ⟨eF₀⟩⟩

/-- Helper for Lemma 15.84.7: degree-zero shifted morphisms are the same as ordinary morphisms in
the derived category. -/
private noncomputable abbrev shiftedHom_zero_linearEquiv
    (K₀ L₀ : DModA0) :
    ShiftedHom K₀ L₀ (0 : ℤ) ≃ₗ[A₀] (K₀ ⟶ L₀) :=
  (LinearEquiv.ofBijective
      { toFun := ShiftedHom.mk₀ (0 : ℤ) rfl
        map_add' := by
          intro f g
          simp
        map_smul' := by
          intro r f
          simpa using ShiftedHom.mk₀_smul (0 : ℤ) rfl r f }
      (by
        constructor
        · intro f g hfg
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).injective <| by
            simpa using hfg
        · intro x
          refine ⟨(ShiftedHom.homEquiv (0 : ℤ) rfl).symm x, ?_⟩
          exact (ShiftedHom.homEquiv (0 : ℤ) rfl).apply_symm_apply x)).symm

/-- Helper for Lemma 15.84.7: once a derived internal-Hom package is fixed, its degree-zero
cohomology identifies with the ordinary Hom group. -/
private noncomputable abbrev derivedHom_zero_homology_linearEquiv_hom
    (H : MonoidalClosed DModA0) (K₀ L₀ : DModA0) :
    ((DerivedCategory.homologyFunctor (ModuleCat A₀) (0 : ℤ)).obj (RHom[H](K₀, L₀))) ≃ₗ[A₀]
      (K₀ ⟶ L₀) :=
  -- Proof comment: first pass from `H⁰(RHom(K₀,L₀))` to `ShiftedHom K₀ L₀ 0`, then collapse the
  -- zero shift to an ordinary morphism.
  (derivedHom_cohomology_iso_shiftedHom H K₀ L₀ (0 : ℤ)).trans
    (shiftedHom_zero_linearEquiv (A₀ := A₀) K₀ L₀)

/-- Helper for Lemma 15.84.7: once one bounded-above finite-free source model and one bounded
target model with restricted termwise `R₀`-flatness are fixed, both source-facing Hom-colimit
statements should be derived from a single represented-Hom comparison. -/
private theorem stage_factorization_and_eventual_eq_of_strict_models
    (K₀ L₀ : DModA0)
    (P₀ F₀ : CpxA0)
    (hP₀bounded : MinusCpxA0 P₀)
    (hP₀finiteFree : P₀.IsTermwiseFiniteFree)
    (hP₀iso : IsIsomorphic (DerivedCategory.Q.obj P₀) K₀)
    (hF₀bounded : CochainComplex.bounded (ModuleCat A₀) F₀)
    (hF₀flat :
      CochainComplex.IsTermwiseFlat
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapHomologicalComplex
          (up ℤ)).obj F₀))
    (hF₀iso : IsIsomorphic (DerivedCategory.Q.obj F₀) L₀) :
    (∀ α :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]),
      ∃ (j : Set.Ici i₀)
        (β :
          (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
            (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])),
        α = stageToColimitHomMap F i₀ A₀ j β) ∧
    (∀ (j : Set.Ici i₀)
      (β₁ β₂ :
        (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
          (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])),
      stageToColimitHomMap F i₀ A₀ j β₁ =
        stageToColimitHomMap F i₀ A₀ j β₂ →
          ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
            stageTransitionHomMap F i₀ A₀ hjk β₁ =
              stageTransitionHomMap F i₀ A₀ hjk β₂) := by
  -- TODO: form the fixed Hom complex `E₀ := ⟪P₀, F₀⟫`, identify the stage and colimit Hom groups
  -- with degree-zero homology via Lemma `15.84.6`, apply filtered-colimit exactness to the
  -- short row of the scalar-extended system, and then transport surjectivity/injectivity back to
  -- the source-facing maps `stageToColimitHomMap` and `stageTransitionHomMap`.
  let _ := hP₀bounded
  let _ := hP₀finiteFree
  let _ := hP₀iso
  let _ := hF₀bounded
  let _ := hF₀flat
  let _ := hF₀iso
  sorry

-- Proof sketch: represent the morphism group after base change to `A` by the bounded Hom complex
-- from Lemma `15.84.6`, descend the finitely presented terms of that complex to a sufficiently
-- large stage using filtered-colimit exactness, and read off a stage morphism inducing `α`.
/-- Lemma 15.84.7 (2): if `K₀, L₀ ∈ D(A₀)` with `K₀` pseudo-coherent and `L₀` of finite tor
dimension over `R₀`, then every morphism after base change to
`A = A₀ ⊗[R₀] \operatorname{colim}_i R_i` comes from some stage
`A_j = A₀ ⊗[R₀] R_j`. -/
@[stacks 0DHX]
theorem exists_stage_factorization_of_hom_of_pseudoCoherent_of_finiteTorDimension
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (α :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] (colimit F : CommRingCat.{u})])) :
    ∃ (j : Set.Ici i₀)
      (β :
        (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
          (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1])),
      α = stageToColimitHomMap F i₀ A₀ j β := by
  obtain ⟨P₀, hP₀bounded, hP₀finiteFree, hP₀iso⟩ :=
    exists_boundedAbove_termwiseFiniteFree_representative_of_pseudoCoherent
      (F := F) (i₀ := i₀) (A₀ := A₀) K₀ hK₀
  obtain ⟨a, b, hL₀amp⟩ :=
    exists_torAmplitude_interval_of_restrict_hasFiniteTorDimension
      (F := F) (i₀ := i₀) (A₀ := A₀) L₀ hL₀
  obtain ⟨F₀, hF₀bounded, hF₀flat, hF₀iso⟩ :=
    exists_bounded_termwiseFlat_representative_over_base_of_torAmplitude
      (F := F) (i₀ := i₀) (A₀ := A₀) L₀ hL₀amp
  -- Proof comment: the remaining work is the fixed strict-model package requested by the latest
  -- replan, so the public surjectivity theorem is now just its first projection.
  exact
    (stage_factorization_and_eventual_eq_of_strict_models
      (F := F) (i₀ := i₀) (A₀ := A₀)
      K₀ L₀ P₀ F₀ hP₀bounded hP₀finiteFree hP₀iso hF₀bounded hF₀flat hF₀iso).1 α

-- Proof sketch: compute equality in the final Hom group by the same descended Hom complex as in
-- part `(2)`; filtered-colimit exactness implies that two stage classes with equal image in the
-- colimit agree after passing to a sufficiently large later stage.
/-- Lemma 15.84.7 (3): under the same hypotheses on `K₀` and `L₀`, if two morphisms at some
stage `A_j` become equal after base change to `A`, then they already become equal after further
base change to a later stage `A_k` with `k ≥ j`. Together with part `(2)`, this is the Hom-side
filtered-colimit description from the lemma. -/
@[stacks 0DHX]
theorem eventually_eq_of_stage_morphisms_with_equal_colimit_images
    (K₀ L₀ : DModA0) (hK₀ : K₀.IsPseudoCoherent)
    (hL₀ :
      HasFiniteTorDimension
        (((ModuleCat.restrictScalars (algebraMap (F.obj i₀) A₀)).mapDerivedCategory).obj L₀))
    (j : Set.Ici i₀)
    (β₁ β₂ :
      (K₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]) ⟶
        (L₀ ⊗[A₀]^L[A₀ ⊗[F.obj i₀] F.obj j.1]))
    (hβ :
      stageToColimitHomMap F i₀ A₀ j β₁ =
        stageToColimitHomMap F i₀ A₀ j β₂) :
    ∃ (k : Set.Ici i₀) (hjk : j ⟶ k),
      stageTransitionHomMap F i₀ A₀ hjk β₁ =
        stageTransitionHomMap F i₀ A₀ hjk β₂ := by
  obtain ⟨P₀, hP₀bounded, hP₀finiteFree, hP₀iso⟩ :=
    exists_boundedAbove_termwiseFiniteFree_representative_of_pseudoCoherent
      (F := F) (i₀ := i₀) (A₀ := A₀) K₀ hK₀
  obtain ⟨a, b, hL₀amp⟩ :=
    exists_torAmplitude_interval_of_restrict_hasFiniteTorDimension
      (F := F) (i₀ := i₀) (A₀ := A₀) L₀ hL₀
  obtain ⟨F₀, hF₀bounded, hF₀flat, hF₀iso⟩ :=
    exists_bounded_termwiseFlat_representative_over_base_of_torAmplitude
      (F := F) (i₀ := i₀) (A₀ := A₀) L₀ hL₀amp
  -- Proof comment: the same fixed strict-model package controls injectivity, so the public
  -- eventual-equality theorem is its second projection.
  exact
    (stage_factorization_and_eventual_eq_of_strict_models
      (F := F) (i₀ := i₀) (A₀ := A₀)
      K₀ L₀ P₀ F₀ hP₀bounded hP₀finiteFree hP₀iso hF₀bounded hF₀flat hF₀iso).2
      j β₁ β₂ hβ

/- The three statements above give the essential-surjectivity and filtered Hom-colimit data
expressing that the triangulated category of `R`-perfect complexes over `A` is the filtered
colimit of the triangulated categories of `R_j`-perfect complexes over `A_j`. -/

end

end

end CategoryTheory
