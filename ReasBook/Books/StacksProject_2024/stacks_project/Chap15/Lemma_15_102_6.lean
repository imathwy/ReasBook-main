import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.stacks_project.Chap04.Example_4_22_6
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_13
import StacksProject_2024.stacks_project.Chap15.Lemma_15_59_14
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_5
import StacksProject_2024.stacks_project.Chap15.Lemma_15_102_Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite
open SequentialProObjectMorphismRep

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

open scoped IdealPowerSubmodule

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "singleCpx0" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev Q : CpxA ⥤ DMod := DerivedCategory.Q

local instance : MonoidalCategory KMod :=
  homotopyCategory_monoidalCategory

private noncomputable instance : (Q : CpxA ⥤ DMod).Monoidal := by
  change
    (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙ Qh)).Monoidal
  infer_instance

private abbrev ringAsModule : ModuleCat A :=
  ModuleCat.of A A

private abbrev idealPowerRingStage (I : Ideal A) (n : ℕ) : ModuleCat A :=
  idealPowerStage I n ringAsModule

/- Domain-style sampling for Lemma 15.102.6:
- primary domain: ideal-power towers of cochain complexes in `D(A)` and their comparison with the
  derived tensor tower;
- sampled owner declarations:
  `idealPowerDerivedInverseSystem`,
  `derivedTensorProduct`,
  `idealPowerSubmoduleFunctor`,
  `Functor.mapHomologicalComplex`,
  `NatTrans.mapHomologicalComplex`;
- best owner abstraction: the source-facing source tower is the canonical derived tensor tower
  `idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (DerivedCategory.Q.obj M)`, built from
  the chapter owner `idealPowerDerivedInverseSystem`; the explicit tensor-on-complex model
  `((I^(n+1)A) ⊗_A M^•)_n` is only bridge data for the proof;
- primitive data: the ideal `I`, the cochain complex `M`, the canonical ideal-power stage
  `idealPowerStage I (n + 1) (ModuleCat.of A A)`, and the multiplication map
  `I^(n+1)A ⊗ M^i → I^(n+1) M^i`;
- derived API: the canonical derived tensor tower, the ideal-power subcomplex tower, and the
  resulting pro-isomorphism statement.

Source/core/bridge triage:
- `source-facing`: the derived tensor tower `(I^(n+1)[0] ⊗^L_A M^•)_n`, the ideal-power tower
  `(I^(n+1) M^•)_n`, and the pro-isomorphism comparison between them;
- `core/canonical`: `idealPowerDerivedInverseSystem`, `derivedTensorProduct`,
  `idealPowerSubmoduleFunctor`, `idealPowerSubmoduleInclusionNatTrans`,
  `Functor.mapHomologicalComplex`, and `NatTrans.mapHomologicalComplex`;
- `bridge/view`: the explicit tensor-on-complex model and the degreewise multiplication maps
  `I^(n+1)A ⊗ M^i → I^(n+1) M^i`. -/

private abbrev idealPowerTensorToSubmoduleBilinear
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    I^[n] A →ₗ[A] M →ₗ[A] I^[n] M where
  toFun a :=
    { toFun := fun m ↦
        ⟨(a : A) • m,
          by
            have ha : (a : A) ∈ (I ^ n : Ideal A) := by
              simpa [idealPowerSubmodule] using a.2
            exact Submodule.smul_mem_smul ha (by simp : m ∈ (⊤ : Submodule A M))⟩
      map_add' x y := by
        ext
        simp [smul_add]
      map_smul' r x := by
        ext
        simpa [smul_smul] using congrArg (fun t : A ↦ t • x) (mul_comm (a : A) r) }
  map_add' a b := by
    ext m
    simp [add_smul]
  map_smul' r a := by
    ext m
    simpa [smul_smul] using congrArg (fun t : A ↦ t • m) (mul_comm (a : A) r)

private abbrev idealPowerTensorToSubmodule
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    (tensorLeft (idealPowerRingStage I n)).obj M ⟶ idealPowerStage I n M :=
  ModuleCat.ofHom (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n M))

/-- Helper for Lemma 15.102.6: forgetting the target ideal-power stage turns the tensor-side
multiplication map into ordinary scalar multiplication by the stage element. -/
private theorem idealPowerTensorToSubmodule_forget
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    idealPowerSubtype I n M ∘ₗ TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n M) =
      TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I n A)) := by
  -- Both maps evaluate a pure tensor `a ⊗ x` as the ambient scalar action `a • x`.
  apply TensorProduct.ext'
  intro a x
  rfl

private theorem idealPowerTensorToSubmodule_naturality_linear
    (I : Ideal A) (n : ℕ) {X Y : ModuleCat A} (f : X ⟶ Y) :
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n Y) ∘ₗ
        ModuleCat.Hom.hom ((tensorLeft (idealPowerRingStage I n)).map f) =
      idealPowerSubmoduleMap I f.hom n ∘ₗ
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n X) := by
  -- Both composites act on a pure tensor by applying `f` to the module factor and then using the
  -- same ideal-power scalar action.
  apply TensorProduct.ext'
  intro a x
  change
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n Y)
        (((tensorLeft (idealPowerRingStage I n)).map f).hom (a ⊗ₜ[A] x)) =
      idealPowerSubmoduleMap I f.hom n
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n X) (a ⊗ₜ[A] x))
  change
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n Y) (a ⊗ₜ[A] f.hom x) =
      idealPowerSubmoduleMap I f.hom n
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n X) (a ⊗ₜ[A] x))
  rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
  change (⟨a.1 • f.hom x, ?_⟩ : I^[n] Y) = ⟨f.hom (a.1 • x), ?_⟩
  apply Subtype.ext
  simpa using (f.hom.map_smul a.1 x).symm

private abbrev idealPowerTensorToSubmoduleNatTrans
    (I : Ideal A) (n : ℕ) :
    tensorLeft (idealPowerRingStage I n) ⟶ idealPowerSubmoduleFunctor I n where
  app M := idealPowerTensorToSubmodule I n M
  naturality {X} {Y} f := by
    apply ModuleCat.hom_ext
    exact idealPowerTensorToSubmodule_naturality_linear I n f

private abbrev idealPowerRingStep (I : Ideal A) (n : ℕ) :
    idealPowerRingStage I (n + 2) ⟶ idealPowerRingStage I (n + 1) :=
  (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app ringAsModule

-- The bridge cochain complex `I^(n+1)A ⊗_A M^\bullet` used internally to compare the
-- source-facing derived tensor tower with the ideal-power tower.
private abbrev idealPowerTensorComplex (I : Ideal A) (M : CpxA) (n : ℕ) : CpxA :=
  ((tensorLeft (idealPowerRingStage I (n + 1))).mapHomologicalComplex (up ℤ)).obj M

private abbrev idealPowerTensorComplexFunctor (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (tensorLeft (idealPowerRingStage I (n + 1))).mapHomologicalComplex (up ℤ)

private abbrev idealPowerTensorStepNatTrans (I : Ideal A) (n : ℕ) :
    tensorLeft (idealPowerRingStage I (n + 2)) ⟶
      tensorLeft (idealPowerRingStage I (n + 1)) :=
  (tensoringLeft (ModuleCat A)).map (idealPowerRingStep I n)

private abbrev idealPowerTensorComplexStepNatTrans (I : Ideal A) (n : ℕ) :
    idealPowerTensorComplexFunctor I (n + 1) ⟶ idealPowerTensorComplexFunctor I n :=
  NatTrans.mapHomologicalComplex (idealPowerTensorStepNatTrans I n) (up ℤ)

private abbrev idealPowerTensorStepLinear (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    TensorProduct A (idealPowerRingStage I (n + 2)) M →ₗ[A]
      TensorProduct A (idealPowerRingStage I (n + 1)) M :=
  ModuleCat.Hom.hom ((idealPowerTensorStepNatTrans I n).app M)

private abbrev idealPowerSubmoduleStepLinear (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    idealPowerStage I (n + 2) M →ₗ[A] idealPowerStage I (n + 1) M :=
  ModuleCat.Hom.hom ((idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app M)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.102.6: the tensor-side step map is exactly right tensoring the canonical
inclusion `I^[n+2] A ↪ I^[n+1] A` by the module factor. -/
private theorem idealPowerTensorStepLinear_eq_rTensor_inclusion
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    idealPowerTensorStepLinear I n M =
      (Submodule.inclusion (idealPowerSubmodule_mono I (Nat.le_succ (n + 1)))).rTensor M := by
  -- The tensor-step natural transformation was defined from that same inclusion.
  rfl

/-- Helper for Lemma 15.102.6: scalar multiplication through a submodule inclusion commutes with
tensoring that inclusion on the left factor. -/
private theorem tensor_lsmul_comp_rTensor_inclusion
    {X : Type u} [AddCommGroup X] [Module A X]
    {K L : Submodule A A} (hLK : L ≤ K) :
    TensorProduct.lift ((LinearMap.lsmul A X).comp K.subtype) ∘ₗ
        (Submodule.inclusion hLK).rTensor X =
      TensorProduct.lift ((LinearMap.lsmul A X).comp L.subtype) := by
  -- Both routes send `a ⊗ x` to the ambient scalar action of the same underlying element `a`.
  apply TensorProduct.ext'
  intro a x
  simp [LinearMap.comp_apply, LinearMap.lsmul_apply]

/-- Helper for Lemma 15.102.6: right tensoring a submodule inclusion sends a pure tensor to the
corresponding pure tensor in the larger stage. -/
private theorem Submodule.inclusion_rTensor_tmul
    {M : Type u} [AddCommGroup M] [Module A M]
    {K L : Submodule A A} (hLK : L ≤ K) (a : L) (x : M) :
    ((Submodule.inclusion hLK).rTensor M) (a ⊗ₜ[A] x) =
      (Submodule.inclusion hLK a) ⊗ₜ[A] x := by
  -- Proof comment: `rTensor` is defined by mapping pure tensors on the left factor.
  rfl

/-- Helper for Lemma 15.102.6: the tensor-step route evaluates a pure tensor by the ambient scalar
action of its ideal-power stage element. -/
private theorem idealPowerTensorToSubmodule_forget_apply_after_step
    (I : Ideal A) (n : ℕ) (M : ModuleCat A)
    (a : idealPowerRingStage I (n + 2)) (x : M) :
    (idealPowerSubtype I (n + 1) M ∘ₗ
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M))
      (a ⊗ₜ[A] x) = a.1 • x := by
  -- Route correction: rewrite the whole applied composite before any extensionality, so Lean only
  -- sees the ambient scalar-action route on the pure tensor `a ⊗ₜ[A] x`.
  simp only [LinearMap.comp_apply]
  have hforget :
      (idealPowerSubtype I (n + 1) M ∘ₗ
          TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M))
        ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)) =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 1) A))
          ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)) := by
    exact congrArg
      (fun f ↦ f ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)))
      (idealPowerTensorToSubmodule_forget I (n + 1) M)
  have hforget_apply :
      (idealPowerSubtype I (n + 1) M)
          ((TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M))
            ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x))) =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 1) A))
          ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)) := by
    simpa [LinearMap.comp_apply] using hforget
  have hstep :
      idealPowerTensorStepLinear I n M (a ⊗ₜ[A] x) =
        ((Submodule.inclusion (idealPowerSubmodule_mono I (Nat.le_succ (n + 1)))).rTensor M)
          (a ⊗ₜ[A] x) := by
    simpa using congrArg (fun f ↦ f (a ⊗ₜ[A] x))
      (idealPowerTensorStepLinear_eq_rTensor_inclusion I n M)
  have hrTensor :
      TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 1) A))
          (((Submodule.inclusion (idealPowerSubmodule_mono I (Nat.le_succ (n + 1)))).rTensor M)
            (a ⊗ₜ[A] x)) =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 2) A))
          (a ⊗ₜ[A] x) := by
    exact congrArg (fun f ↦ f (a ⊗ₜ[A] x))
      (tensor_lsmul_comp_rTensor_inclusion
        (A := A)
        (X := M)
        (hLK := idealPowerSubmodule_mono I (Nat.le_succ (n + 1))))
  calc
    (idealPowerSubtype I (n + 1) M)
        ((TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M))
          ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)))
      =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 1) A))
          ((idealPowerTensorStepLinear I n M) (a ⊗ₜ[A] x)) := hforget_apply
    _ =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 1) A))
          (((Submodule.inclusion (idealPowerSubmodule_mono I (Nat.le_succ (n + 1)))).rTensor M)
            (a ⊗ₜ[A] x)) := by
              rw [hstep]
    _ =
        TensorProduct.lift ((LinearMap.lsmul A M).comp (idealPowerSubtype I (n + 2) A))
          (a ⊗ₜ[A] x) := hrTensor
    _ = a.1 • x := by
      rw [TensorProduct.lift.tmul]
      rfl

/-- Helper for Lemma 15.102.6: the tensor-step route evaluates a pure tensor by the ambient scalar
action of its ideal-power stage element. -/
private theorem idealPowerTensorToSubmodule_step_comm_forget_eval_left
    (I : Ideal A) (n : ℕ) (M : ModuleCat A)
    (a : idealPowerRingStage I (n + 2)) (x : M) :
    (idealPowerSubtype I (n + 1) M ∘ₗ
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M))
      (a ⊗ₜ[A] x) = a.1 • x := by
  -- Proof comment: this is exactly the applied-form rewrite packaged in the previous helper.
  simpa using idealPowerTensorToSubmodule_forget_apply_after_step I n M a x

/-- Helper for Lemma 15.102.6: the submodule-step route evaluates a pure tensor by the same
ambient scalar action of its stage element. -/
private theorem idealPowerTensorToSubmodule_step_comm_forget_eval_right
    (I : Ideal A) (n : ℕ) (M : ModuleCat A)
    (a : idealPowerRingStage I (n + 2)) (x : M) :
    (idealPowerSubtype I (n + 1) M ∘ₗ
        (idealPowerSubmoduleStepLinear I n M ∘ₗ
          TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M)))
      (a ⊗ₜ[A] x) = a.1 • x := by
  -- Proof comment: evaluate the stage-`n + 2` tensor-to-submodule map first, then use that
  -- forgetting after the successor inclusion preserves the same ambient element.
  simp only [LinearMap.comp_apply, TensorProduct.lift.tmul]
  rfl

/-- Helper for Lemma 15.102.6: after forgetting the subtype codomain, the successor square for
the tensor-to-submodule comparison becomes an ambient module identity. -/
private theorem idealPowerTensorToSubmodule_step_comm_forget
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    idealPowerSubtype I (n + 1) M ∘ₗ
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M) =
      idealPowerSubtype I (n + 1) M ∘ₗ
        (idealPowerSubmoduleStepLinear I n M ∘ₗ
          TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M)) := by
  -- Proof comment: both forgotten composites agree on every pure tensor by the two evaluation
  -- lemmas above, so `TensorProduct.ext'` closes the linear-map equality.
  apply TensorProduct.ext'
  intro a x
  calc
    (idealPowerSubtype I (n + 1) M ∘ₗ
        (TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M))
      (a ⊗ₜ[A] x) = a.1 • x := by
        exact idealPowerTensorToSubmodule_step_comm_forget_eval_left I n M a x
    _ = (idealPowerSubtype I (n + 1) M ∘ₗ
          (idealPowerSubmoduleStepLinear I n M ∘ₗ
            TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M)))
        (a ⊗ₜ[A] x) := by
          symm
          exact idealPowerTensorToSubmodule_step_comm_forget_eval_right I n M a x

private abbrev idealPowerTensorComplexStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M (n + 1) ⟶ idealPowerTensorComplex I M n :=
  (idealPowerTensorComplexStepNatTrans I n).app M

-- The cochain complex `I^(n+1) M^\bullet`, obtained by applying the canonical ideal-power
-- submodule functor degreewise to `M^\bullet`.
private abbrev idealPowerComplexFunctor (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (idealPowerSubmoduleFunctor I (n + 1)).mapHomologicalComplex (up ℤ)

private abbrev idealPowerComplex (I : Ideal A) (M : CpxA) (n : ℕ) : CpxA :=
  (idealPowerComplexFunctor I n).obj M

private abbrev idealPowerComplexStepNatTrans (I : Ideal A) (n : ℕ) :
    idealPowerComplexFunctor I (n + 1) ⟶ idealPowerComplexFunctor I n :=
  NatTrans.mapHomologicalComplex
    (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))) (up ℤ)

private abbrev idealPowerComplexStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerComplex I M (n + 1) ⟶ idealPowerComplex I M n :=
  (idealPowerComplexStepNatTrans I n).app M

private abbrev idealPowerComplexDerivedStage (I : Ideal A) (M : CpxA) (n : ℕ) : DMod :=
  Q.obj (idealPowerComplex I M n)

private abbrev idealPowerComplexDerivedStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerComplexDerivedStage I M (n + 1) ⟶ idealPowerComplexDerivedStage I M n :=
  Q.map (idealPowerComplexStep I M n)

/-- The inverse system `(Q(I^(n+1) M^\bullet))_n` in `D(A)`. -/
abbrev idealPowerComplexDerivedInverseSystem (I : Ideal A) (M : CpxA) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerComplexDerivedStep I M)

-- The internal stagewise comparison map
-- `I^(n+1)A ⊗_A M^\bullet ⟶ I^(n+1) M^\bullet`.
private abbrev idealPowerTensorComplexToIdealPowerComplex (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M n ⟶ idealPowerComplex I M n :=
  (NatTrans.mapHomologicalComplex (idealPowerTensorToSubmoduleNatTrans I (n + 1)) (up ℤ)).app M

private theorem idealPowerTensorToSubmodule_step_comm
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
        idealPowerTensorStepLinear I n M =
      idealPowerSubmoduleStepLinear I n M ∘ₗ
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M) := by
  -- Proof comment: compare the two subtype-valued maps by forgetting to the ambient module, where
  -- the previous lemma already proved the successor square.
  apply TensorProduct.ext'
  intro a x
  apply Subtype.ext
  change
    (idealPowerSubtype I (n + 1) M)
        ((TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M)
          (a ⊗ₜ[A] x)) =
      (idealPowerSubtype I (n + 1) M)
        ((idealPowerSubmoduleStepLinear I n M ∘ₗ
          TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M))
          (a ⊗ₜ[A] x))
  calc
    (idealPowerSubtype I (n + 1) M)
        ((TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 1) M) ∘ₗ
          idealPowerTensorStepLinear I n M)
          (a ⊗ₜ[A] x))
      = a.1 • x := by
          simpa [LinearMap.comp_apply] using
            idealPowerTensorToSubmodule_step_comm_forget_eval_left I n M a x
    _ =
      (idealPowerSubtype I (n + 1) M)
        ((idealPowerSubmoduleStepLinear I n M ∘ₗ
          TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M))
          (a ⊗ₜ[A] x)) := by
            symm
            simpa [LinearMap.comp_apply] using
              idealPowerTensorToSubmodule_step_comm_forget_eval_right I n M a x

private theorem idealPowerTensorToSubmodule_step_comm_hom
    (I : Ideal A) (n : ℕ) (M : ModuleCat A) :
    (idealPowerTensorStepNatTrans I n).app M ≫
      idealPowerTensorToSubmodule I (n + 1) M =
    idealPowerTensorToSubmodule I (n + 2) M ≫
      (idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app M := by
  apply ModuleCat.hom_ext
  exact idealPowerTensorToSubmodule_step_comm I n M

private theorem idealPowerTensorToSubmodule_step_natTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerTensorStepNatTrans I n ≫
      idealPowerTensorToSubmoduleNatTrans I (n + 1) =
    idealPowerTensorToSubmoduleNatTrans I (n + 2) ≫
      idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1)) := by
  apply NatTrans.ext
  funext M
  exact idealPowerTensorToSubmodule_step_comm_hom I n M

private theorem idealPowerTensorComplexToIdealPowerComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexStep I M n ≫ idealPowerTensorComplexToIdealPowerComplex I M n =
      idealPowerTensorComplexToIdealPowerComplex I M (n + 1) ≫ idealPowerComplexStep I M n := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (up ℤ)).app M)
      (idealPowerTensorToSubmodule_step_natTrans I n)
  simpa [idealPowerTensorComplexStep, idealPowerTensorComplexToIdealPowerComplex,
    idealPowerComplexStep] using h

private abbrev idealPowerTensorComplexDerivedStage (I : Ideal A) (M : CpxA) (n : ℕ) : DMod :=
  Q.obj (idealPowerTensorComplex I M n)

private abbrev idealPowerTensorComplexDerivedStep (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M (n + 1) ⟶
      idealPowerTensorComplexDerivedStage I M n :=
  Q.map (idealPowerTensorComplexStep I M n)

-- The bridge inverse system `(Q(I^(n+1)A ⊗_A M^\bullet))_n` in `D(A)`.
private abbrev idealPowerTensorComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerTensorComplexDerivedStep I M)

private theorem idealPowerTensorComplexToIdealPowerComplexDerived_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStep I M n ≫
        Q.map (idealPowerTensorComplexToIdealPowerComplex I M n) =
      Q.map (idealPowerTensorComplexToIdealPowerComplex I M (n + 1)) ≫
        idealPowerComplexDerivedStep I M n := by
  simpa [idealPowerTensorComplexDerivedStep] using
    congrArg Q.map
      (idealPowerTensorComplexToIdealPowerComplex_step_comm I M n)

private abbrev idealPowerTensorComplexToIdealPowerComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerTensorComplexDerivedInverseSystem I M ⟶
      idealPowerComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ Q.map (idealPowerTensorComplexToIdealPowerComplex I M n))
    (fun n ↦ by
      simpa using idealPowerTensorComplexToIdealPowerComplexDerived_step_comm I M n)

private abbrev idealPowerStageSingleComplex (I : Ideal A) (n : ℕ) : CpxA :=
  (singleCpx0).obj (idealPowerRingStage I (n + 1))

/-- Helper for Lemma 15.102.6: postcomposing a descended tensor-totalization map can be checked on
each `(p,q)` summand. -/
@[reassoc]
private theorem iTensorObj_mapBifunctorDesc_assoc
    {K L : CpxA} (n : ℤ) {B C : ModuleCat A}
    (f : ∀ p q
      (_h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (K.X p)).obj (L.X q) ⟶ B)
    (u : B ⟶ C) (p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        HomologicalComplex.mapBifunctorDesc
          (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
          (c := ComplexShape.up ℤ) (A := B) (j := n) f ≫ u =
      f p q h ≫ u := by
  -- Proof comment: this is the owner universal property `ι_mapBifunctorDesc`, postcomposed by `u`.
  simpa only [HomologicalComplex.ιTensorObj] using
    congrArg (fun t ↦ t ≫ u)
      (HomologicalComplex.ι_mapBifunctorDesc
        (K₁ := K) (K₂ := L) (F := curriedTensor (ModuleCat A))
        (c := ComplexShape.up ℤ) (A := B) (j := n) (f := f) p q h)

/-- Helper for Lemma 15.102.6: away from degree `0`, the right single complex contributes a zero
summand to the tensor totalization. -/
private theorem tensor_single0_off_diagonal_isZero
    (E : CpxA) (N : ModuleCat A) (p q : ℤ) (hq : q ≠ 0) :
    CategoryTheory.Limits.IsZero (((curriedTensor (ModuleCat A)).obj (E.X p)).obj
      (((singleCpx0).obj N).X q)) := by
  -- Proof comment: only the degree-zero term of the single complex survives.
  exact
    CategoryTheory.Functor.map_isZero ((curriedTensor (ModuleCat A)).obj (E.X p))
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) N q hq)

/-- Helper for Lemma 15.102.6: on the surviving degree-zero summand, tensoring with the right
single complex is exactly right tensoring by the underlying module. -/
private noncomputable def tensor_single0_diagonal_iso
    (E : CpxA) (N : ModuleCat A) (n : ℤ) :
    ((curriedTensor (ModuleCat A)).obj (E.X n)).obj
      (((singleCpx0).obj N).X 0) ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n := by
  -- Proof comment: after fixing degree `0`, only the canonical `singleObjXSelf` identification remains.
  simpa using
    CategoryTheory.Functor.mapIso ((curriedTensor (ModuleCat A)).obj (E.X n))
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N)

/-- Helper for Lemma 15.102.6: the forward comparison keeps only the diagonal summand of the
tensor totalization with a right single complex. -/
private noncomputable def tensor_single0_component_hom
    (E : CpxA) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E ((singleCpx0).obj N)).X n ⟶
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := E)
    (K₂ := (singleCpx0).obj N)
    (F := curriedTensor (ModuleCat A))
    (c := ComplexShape.up ℤ)
    (A := (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n)
    (j := n)
    (fun p q h ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0)

/-- Helper for Lemma 15.102.6: on the diagonal summand, the forward comparison is the canonical
degreewise tensor identification. -/
@[reassoc]
private theorem tensor_single0_component_hom_diag
    (E : CpxA) (N : ModuleCat A) (n : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n) :
    HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h ≫
      tensor_single0_component_hom E N n =
        (tensor_single0_diagonal_iso E N n).hom := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p q
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p)).obj (((singleCpx0).obj N).X q) ⟶ B :=
    fun p q h' ↦ by
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h'
        subst p
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Proof comment: evaluate the descended map on the unique surviving `(n,0)` summand.
  simpa [tensor_single0_component_hom, B, f] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := (singleCpx0).obj N)
      (n := n) (B := B) (C := B) f (𝟙 B) n 0 h)

/-- Helper for Lemma 15.102.6: off the diagonal summand, the forward comparison vanishes. -/
@[reassoc]
private theorem tensor_single0_component_hom_off_diagonal
    (E : CpxA) (N : ModuleCat A) (n p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n)
    (hq : q ≠ 0) :
    HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) p q n h ≫
      tensor_single0_component_hom E N n =
        0 := by
  let B :
      ModuleCat A :=
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n
  let f : ∀ p' q'
      (h' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p', q') = n),
      ((curriedTensor (ModuleCat A)).obj (E.X p')).obj (((singleCpx0).obj N).X q') ⟶ B :=
    fun p' q' h' ↦ by
      by_cases hq' : q' = 0
      · subst hq'
        have hp' : p' = n := by simpa using h'
        subst p'
        exact (tensor_single0_diagonal_iso E N n).hom
      · exact 0
  -- Proof comment: off the diagonal, the chosen branch in the descended map is definitionally zero.
  simpa [tensor_single0_component_hom, B, f, hq] using
    (iTensorObj_mapBifunctorDesc_assoc
      (K := E)
      (L := (singleCpx0).obj N)
      (n := n) (B := B) (C := B) f (𝟙 B) p q h)

/-- Helper for Lemma 15.102.6: the inverse degreewise comparison reinserts the diagonal summand
into the tensor totalization with a right single complex. -/
private noncomputable def tensor_single0_component_inv
    (E : CpxA) (N : ModuleCat A) (n : ℤ) :
    (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E).X n ⟶
      (HomologicalComplex.tensorObj E ((singleCpx0).obj N)).X n :=
  (tensor_single0_diagonal_iso E N n).inv ≫
    HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n
      (by simp)

/-- Helper for Lemma 15.102.6: in each total degree, tensoring with a right degree-zero single
complex collapses to the unique surviving diagonal summand. -/
private noncomputable def tensor_single0_component_iso
    (E : CpxA) (N : ModuleCat A) (n : ℤ) :
    (HomologicalComplex.tensorObj E ((singleCpx0).obj N)).X n ≅
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E).X n :=
  { hom := tensor_single0_component_hom E N n
    inv := tensor_single0_component_inv E N n
    hom_inv_id := by
      -- Proof comment: check the identity on the tensor totalization summandwise.
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q h
      by_cases hq : q = 0
      · subst hq
        have hp : p = n := by simpa using h
        subst p
        change
          ((HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h ≫
              𝟙 ((HomologicalComplex.tensorObj E ((singleCpx0).obj N)).X n)
        simpa [tensor_single0_component_inv, Category.assoc] using
          congrArg (fun k ↦ k ≫ tensor_single0_component_inv E N n)
            (tensor_single0_component_hom_diag E N n h)
      · change
          ((HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) p q n h ≫
              tensor_single0_component_hom E N n) ≫
            tensor_single0_component_inv E N n) =
            HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) p q n h ≫
              𝟙 ((HomologicalComplex.tensorObj E ((singleCpx0).obj N)).X n)
        rw [tensor_single0_component_hom_off_diagonal E N n p q h hq]
        simp only [CategoryTheory.Limits.zero_comp, Category.comp_id]
        symm
        exact (tensor_single0_off_diagonal_isZero E N p q hq).eq_of_src _ _
    inv_hom_id := by
      let h0 : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (n, 0) = n := by
        simp
      -- Proof comment: the inverse immediately lands in the diagonal summand and cancels there.
      change
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h0) ≫
          tensor_single0_component_hom E N n =
            𝟙 ((((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E).X n)
      calc
        ((tensor_single0_diagonal_iso E N n).inv ≫
            HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h0) ≫
          tensor_single0_component_hom E N n
            = (tensor_single0_diagonal_iso E N n).inv ≫
                (HomologicalComplex.ιTensorObj E ((singleCpx0).obj N) n 0 n h0 ≫
                  tensor_single0_component_hom E N n) := by
                    simp [Category.assoc]
        _ = (tensor_single0_diagonal_iso E N n).inv ≫
              (tensor_single0_diagonal_iso E N n).hom := by
                simpa using
                  congrArg (fun k ↦ (tensor_single0_diagonal_iso E N n).inv ≫ k)
                    (tensor_single0_component_hom_diag E N n h0)
        _ = 𝟙 _ := by simp }

/-- Helper for Lemma 15.102.6: the diagonal tensor comparison is natural in the differential of
the left cochain complex. -/
private theorem tensor_single0_diagonal_iso_hom_naturality
    (E : CpxA) (N : ModuleCat A) (i j : ℤ)
    (_hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).hom ≫
        (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j =
      (((curriedTensor (ModuleCat A)).map (E.d i j)).app (((singleCpx0).obj N).X 0)) ≫
        (tensor_single0_diagonal_iso E N j).hom := by
  -- Proof comment: this is the `singleObjXSelf` naturality square transported through `tensorRight`.
  simpa [tensor_single0_diagonal_iso, CategoryTheory.Functor.mapHomologicalComplex_obj_d,
    CochainComplex.singleFunctor] using
    (((curriedTensor (ModuleCat A)).map (E.d i j)).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) N).hom)

/-- Helper for Lemma 15.102.6: the inverse diagonal tensor comparison satisfies the same
naturality square rewritten for the inverse map. -/
private theorem tensor_single0_diagonal_iso_inv_naturality
    (E : CpxA) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    (tensor_single0_diagonal_iso E N i).inv ≫
        (((curriedTensor (ModuleCat A)).map (E.d i j)).app (((singleCpx0).obj N).X 0)) =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        (tensor_single0_diagonal_iso E N j).inv := by
  -- Proof comment: cancel the target diagonal isomorphism and reuse the forward naturality square.
  apply (cancel_mono (tensor_single0_diagonal_iso E N j).hom).1
  simpa [Category.assoc] using
    calc
      (tensor_single0_diagonal_iso E N i).inv ≫
          (((curriedTensor (ModuleCat A)).map (E.d i j)).app (((singleCpx0).obj N).X 0)) ≫
          (tensor_single0_diagonal_iso E N j).hom
        = (tensor_single0_diagonal_iso E N i).inv ≫
            ((tensor_single0_diagonal_iso E N i).hom ≫
              (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj E).d i j) := by
            rw [tensor_single0_diagonal_iso_hom_naturality E N i j hij]
      _ =
          (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E).d i j := by
            simp

/-- Helper for Lemma 15.102.6: the inverse degreewise tensor comparison already respects the
cochain differential. -/
private theorem tensor_single0_component_inv_comm
    (E : CpxA) (N : ModuleCat A) (i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    tensor_single0_component_inv E N i ≫
        (HomologicalComplex.tensorObj E ((singleCpx0).obj N)).d i j =
      (((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj E).d i j ≫
        tensor_single0_component_inv E N j := by
  have hj : j = i + 1 := by
    simpa [ComplexShape.up, eq_comm] using hij
  subst hj
  -- Proof comment: expand the total differential; the vertical part vanishes because the single
  -- complex has zero outgoing differential from degree `0`.
  simp only [tensor_single0_component_inv, Category.assoc,
    HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq
      (K₁ := E)
      (K₂ := (singleCpx0).obj N)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (h := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))
      (i₂ := 0)
      (j := i + 1)
      (h' := by simp)]
  rw [HomologicalComplex.mapBifunctor.d₂_eq
      (K₁ := E)
      (K₂ := (singleCpx0).obj N)
      (F := curriedTensor (ModuleCat A))
      (c := ComplexShape.up ℤ)
      (i₁ := i)
      (h := (show (ComplexShape.up ℤ).Rel 0 (0 + 1) by simp))
      (j := i + 1)
      (h' := by simp)]
  have hsingle : (((singleCpx0).obj N).d 0 (0 + 1)) = 0 := rfl
  rw [hsingle, Functor.map_zero, CategoryTheory.Limits.zero_comp, smul_zero,
    CategoryTheory.Limits.comp_zero, add_zero]
  rw [show ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i, 0) = 1 by
      rfl, one_smul]
  rw [← Category.assoc]
  rw [tensor_single0_diagonal_iso_inv_naturality
      (E := E)
      (N := N)
      (i := i)
      (j := i + 1)
      (hij := (show (ComplexShape.up ℤ).Rel i (i + 1) by simp))]
  simp [HomologicalComplex.ιTensorObj, Category.assoc]

/-- Helper for Lemma 15.102.6: tensoring a cochain complex with a right degree-zero single
complex is canonically the same as right tensoring by the underlying module. -/
private noncomputable def tensor_single0_complex_iso
    (E : CpxA) (N : ModuleCat A) :
    HomologicalComplex.tensorObj E ((singleCpx0).obj N) ≅
      ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ tensor_single0_component_iso E N n)
    (fun i j hij ↦ by
      -- Proof comment: rewrite the inverse chain-map square into the forward orientation expected
      -- by `isoOfComponents`.
      apply (cancel_mono (tensor_single0_component_iso E N j).inv).1
      apply (cancel_epi (tensor_single0_component_iso E N i).inv).1
      simpa [Category.assoc] using
        (tensor_single0_component_inv_comm E N i j hij).symm)

/-- Helper for Lemma 15.102.6: left tensoring a cochain complex by a module is canonically the
tensor object with the degree-zero single complex of that module. -/
private noncomputable def single0_tensorLeft_complex_iso
    (S : ModuleCat A) (M : CpxA) :
    (((tensorLeft S).mapHomologicalComplex (up ℤ)).obj M) ≅
      HomologicalComplex.tensorObj ((singleCpx0).obj S) M :=
  ((NatIso.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight S) (up ℤ)).app M) ≪≫
    (tensor_single0_complex_iso M S).symm ≪≫
      β_ M ((singleCpx0).obj S)

omit [IsNoetherianRing A] in
/-- Helper for Lemma 15.102.6: the explicit tensor stage is canonically the tensor of `M` with the
degree-zero complex `(I^[n+1] A)[0]`. -/
private noncomputable def idealPowerTensorComplex_iso_tensorObj_single_stage
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M n ≅
      HomologicalComplex.tensorObj (idealPowerStageSingleComplex I n) M :=
  -- Proof comment: first commute left tensoring past the braiding to right tensoring, then use
  -- the right-single tensor comparison and finally braid the tensor object back into source order.
  single0_tensorLeft_complex_iso (idealPowerRingStage I (n + 1)) M

private noncomputable abbrev idealPowerTensorComplexDerivedStageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M n ≅
      ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)).obj (op n)) :=
  (Q.mapIso (idealPowerTensorComplex_iso_tensorObj_single_stage I M n)) ≪≫
    (Functor.Monoidal.μIso Q
      (idealPowerStageSingleComplex I n) M).symm ≪≫
    (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl _) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct
        (idealPowerDerivedStage I n) (Q.obj M)

/-- Helper for Lemma 15.102.6: the left half of the stagewise comparison carries the explicit
tensor-complex model to the tensor-object model in `D(A)`. -/
private noncomputable abbrev idealPowerTensorComplex_to_tensor_stageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M n ≅
      idealPowerDerivedStage I n ⊗ Q.obj M :=
  (Q.mapIso (idealPowerTensorComplex_iso_tensorObj_single_stage I M n)) ≪≫
    (Functor.Monoidal.μIso Q
      (idealPowerStageSingleComplex I n) M).symm

/-- Helper for Lemma 15.102.6: the right half of the stagewise comparison transports the tensor
object model to the canonical derived tensor product stage. -/
private noncomputable abbrev idealPowerDerivedStage_to_derived_tensorIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerDerivedStage I n ⊗ Q.obj M ≅
      ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)).obj (op n)) :=
  (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl _) ≪≫
    derivedCategory_tensorObj_iso_derivedTensorProduct
      (idealPowerDerivedStage I n) (Q.obj M)

/-- Helper for Lemma 15.102.6: the comparison from ambient tensoring to derived tensoring is
natural in the left variable, written in the orientation used by the stagewise comparison. -/
@[reassoc]
private theorem tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit
    (N : DMod) {K L : DMod} (f : K ⟶ L) :
    (derivedCategory_tensorObj_iso_derivedTensorProduct K N).hom ≫
        (derivedTensorProduct N).map f =
      (f ▷ N) ≫ (derivedCategory_tensorObj_iso_derivedTensorProduct L N).hom := by
  -- Proof comment: this is the componentwise naturality of the canonical tensor/derived-tensor
  -- comparison for the fixed right factor `N`.
  simpa using ((tensoringRightIsoDerivedTensorProduct N).hom.naturality f).symm

/-- Helper for Lemma 15.102.6: after the `Q`-monoidal comparison, the explicit tensor-complex
transition becomes the tensor-object morphism induced by the ideal-power stage inclusion. -/
private theorem idealPowerTensorComplex_to_tensor_stage_hom_naturality
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStep I M n ≫
        (idealPowerTensorComplex_to_tensor_stageIso I M n).hom =
      (idealPowerTensorComplex_to_tensor_stageIso I M (n + 1)).hom ≫
        (idealPowerDerivedStep I n ▷ Q.obj M) := by
  -- TODO: transport the step map through `single0_tensorLeft_complex_iso` first, then apply the
  -- monoidal naturality square for `Functor.Monoidal.μIso Q` exactly as in Lemma 15.101.3.
  sorry

/-- Helper for Lemma 15.102.6: the single-complex bridge and the derived-tensor comparison carry
the tensor-object morphism on the ideal-power stage to the canonical derived tensor transition. -/
private theorem idealPowerDerivedStage_to_derived_tensor_hom_naturality
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    (idealPowerDerivedStep I n ▷ Q.obj M) ≫
        (idealPowerDerivedStage_to_derived_tensorIso I M n).hom =
      (idealPowerDerivedStage_to_derived_tensorIso I M (n + 1)).hom ≫
        ((derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n)) := by
  -- Proof comment: first rewrite the `singleFunctorIsoCompQ` component by naturality of the
  -- degree-zero comparison, then move the remaining map through the ambient/derived tensor bridge.
  have hsingle :
      (idealPowerDerivedStep I n ▷ Q.obj M) ≫
          ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl (Q.obj M)).hom) =
        ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          (idealPowerDerivedStep I n ▷ Q.obj M) := by
    -- Proof comment: tensor the naturality square for `singleFunctorIsoCompQ` with the fixed right
    -- factor `Q.obj M`.
    simpa [idealPowerDerivedStep, Category.assoc] using
      congrArg (fun k ↦ k ▷ Q.obj M)
        ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).hom.naturality
          ((idealPowerSubmoduleInclusionNatTrans I (Nat.le_succ (n + 1))).app ringAsModule))
  have htensor :
      (idealPowerDerivedStep I n ▷ Q.obj M) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct
            (idealPowerDerivedStage I n) (Q.obj M)).hom =
        (derivedCategory_tensorObj_iso_derivedTensorProduct
          (idealPowerDerivedStage I (n + 1)) (Q.obj M)).hom ≫
          (derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n) := by
    -- Proof comment: this is the fixed-right-factor naturality of the ambient/derived tensor
    -- comparison.
    simpa [tensoringRightIsoDerivedTensorProduct_hom_app] using
      (tensoringRightIsoDerivedTensorProduct_hom_naturality_explicit
        (N := Q.obj M)
        (f := idealPowerDerivedStep I n)).symm
  calc
    (idealPowerDerivedStep I n ▷ Q.obj M) ≫
        (idealPowerDerivedStage_to_derived_tensorIso I M n).hom
      =
        (idealPowerDerivedStep I n ▷ Q.obj M) ≫
          ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl (Q.obj M)).hom ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct
              (idealPowerDerivedStage I n) (Q.obj M)).hom) := by
              rfl
    _ =
        ((idealPowerDerivedStep I n ▷ Q.obj M ≫
            (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
                (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct
            (idealPowerDerivedStage I n) (Q.obj M)).hom) := by
              simp [Category.assoc]
    _ =
        (((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          (idealPowerDerivedStep I n ▷ Q.obj M)) ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct
              (idealPowerDerivedStage I n) (Q.obj M)).hom := by
                exact congrArg
                  (fun k ↦ k ≫
                    (derivedCategory_tensorObj_iso_derivedTensorProduct
                      (idealPowerDerivedStage I n) (Q.obj M)).hom)
                  hsingle
    _ =
        ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          (idealPowerDerivedStep I n ▷ Q.obj M ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct
              (idealPowerDerivedStage I n) (Q.obj M)).hom) := by
                simp [Category.assoc]
    _ =
        ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          ((idealPowerDerivedStep I n ▷ Q.obj M) ≫
            (derivedCategory_tensorObj_iso_derivedTensorProduct
              (idealPowerDerivedStage I n) (Q.obj M)).hom) := by
                simp [Category.assoc]
    _ =
        ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
              (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct
            (idealPowerDerivedStage I (n + 1)) (Q.obj M)).hom ≫
          (derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n) := by
            simpa [Category.assoc] using congrArg
              (fun k ↦
                ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
                    (idealPowerRingStage I (n + 2))) ⊗ᵢ Iso.refl (Q.obj M)).hom) ≫ k)
              htensor
    _ =
        (idealPowerDerivedStage_to_derived_tensorIso I M (n + 1)).hom ≫
          (derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n) := by
            simpa [idealPowerDerivedStage_to_derived_tensorIso, Category.assoc]

/-- Helper for Lemma 15.102.6: the full stagewise tensor-model comparison is natural with respect
to the successor maps of the explicit tensor-complex tower and the derived tensor tower. -/
private theorem idealPowerTensorComplexDerivedStageIso_hom_naturality
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStep I M n ≫
        (idealPowerTensorComplexDerivedStageIso I M n).hom =
      (idealPowerTensorComplexDerivedStageIso I M (n + 1)).hom ≫
        ((derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n)) := by
  -- TODO: factor the full stage comparison into the two half-isomorphisms above, prove the two
  -- hom-side squares, and then compose them by reassociating the middle tensor-object stage.
  sorry

private theorem idealPowerDerivedTensorToTensorComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    ((derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n)) ≫
        (idealPowerTensorComplexDerivedStageIso I M n).inv =
      (idealPowerTensorComplexDerivedStageIso I M (n + 1)).inv ≫
        idealPowerTensorComplexDerivedStep I M n := by
  -- TODO: once the hom-side naturality of `idealPowerTensorComplexDerivedStageIso` is proved,
  -- recover this inverse-side square by the same cancellation pattern used in Lemma 15.101.3.
  sorry

private abbrev idealPowerDerivedTensorToTensorComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerTensorComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ (idealPowerTensorComplexDerivedStageIso I M n).inv)
    (fun n ↦ by
      simpa using idealPowerDerivedTensorToTensorComplex_step_comm I M n)

/-- Helper for Lemma 15.102.6: the derived tensor tower is naturally isomorphic to the explicit
tensor-complex tower through the chosen stagewise tensor-model identifications. -/
private noncomputable def idealPowerDerivedTensorToTensorComplex_natIso
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ≅
      idealPowerTensorComplexDerivedInverseSystem I M :=
  NatIso.ofComponents
    (fun n ↦ (idealPowerTensorComplexDerivedStageIso I M n.unop).symm)
    (fun {_ _} f ↦ by
      -- The naturality square is exactly the packaged step compatibility of the inverse
      -- components.
      simpa using
        (idealPowerDerivedTensorToTensorComplexNatTrans I M).naturality f)

-- Proof sketch: choose generators of `I`, replace the ideal-power tower by the pro-isomorphic
-- powered-Koszul tower from Lemma `15.102.5`, then tensor that pro-isomorphism with `Q.obj M`
-- using the canonical owner `derivedTensorProduct`. For the concrete comparison to
-- `(I^(n+1) M^\bullet)_n`, use the explicit tensor-on-complex bridge above and then apply Lemma
-- `13.42.5` after passing to cohomology. For each cohomological degree, resolve `M^\bullet` by a
-- bounded-above finite free complex and use Lemma `15.102.1` to identify the induced homology
-- tower with the ideal-power filtration on `H^p(M^\bullet)`.
/-- The canonical comparison from the derived tensor tower
`((I^(n+1)A)[0] \otimes_A^{\mathbf L} Q(M^\bullet))_n` to the ideal-power tower
`(Q(I^(n+1) M^\bullet))_n`, assembled directly from the canonical tensor and ideal-power stage
maps. -/
abbrev idealPowerDerivedTensorToIdealPowerComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerComplexDerivedInverseSystem I M :=
  idealPowerDerivedTensorToTensorComplexNatTrans I M ≫
    idealPowerTensorComplexToIdealPowerComplexNatTrans I M

/-- Lemma 15.102.6: let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `M^\bullet`
be a bounded complex of finite `A`-modules. Then the canonical comparison from the derived tensor
tower `((I^(n+1)A)[0] \otimes_A^{\mathbf L} Q(M^\bullet))_n`, equivalently
`idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (DerivedCategory.Q.obj M)`, to the
ideal-power tower `(Q(I^(n+1) M^\bullet))_n` is an isomorphism of sequential pro-objects. In this
item-file convention, stage `0` corresponds to the textbook power `I^1`. -/
theorem idealPowerDerivedTensorToIdealPowerComplex_isIso
    (I : Ideal A) (M : CpxA)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (ofNatTrans (idealPowerDerivedTensorToIdealPowerComplexNatTrans I M)).toProObjectHom :=
  by
  -- TODO: first replace the source tower by `idealPowerTensorComplexDerivedInverseSystem I M`
  -- using the stagewise tensor-model isomorphism above, then apply Lemma `13.42.5` to
  -- `idealPowerTensorComplexToIdealPowerComplexNatTrans I M` after reducing each cohomology tower
  -- to a bounded-above finite-free model and invoking Lemma `15.102.1`.
  sorry

end
