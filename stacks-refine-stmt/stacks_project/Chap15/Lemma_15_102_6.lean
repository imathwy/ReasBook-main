import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import stacks_project.Chap04.Example_4_22_6
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Lemma_15_59_14
import stacks_project.Chap15.Lemma_15_102_5
import stacks_project.Chap15.Lemma_15_102_Basic

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

private noncomputable instance : (DerivedCategory.Q : CpxA ⥤ DMod).Monoidal := by
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

private theorem idealPowerTensorToSubmodule_naturality_linear
    (I : Ideal A) (n : ℕ) {X Y : ModuleCat A} (f : X ⟶ Y) :
    TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n Y) ∘ₗ
        ModuleCat.Hom.hom ((tensorLeft (idealPowerRingStage I n)).map f) =
      idealPowerSubmoduleMap I f.hom n ∘ₗ
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I n X) := sorry

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
        TensorProduct.lift (idealPowerTensorToSubmoduleBilinear I (n + 2) M) := sorry

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

private theorem idealPowerTensorComplex_eq_tensorObj
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplex I M n =
      HomologicalComplex.tensorObj (idealPowerStageSingleComplex I n) M :=
  sorry

private noncomputable abbrev idealPowerTensorComplexDerivedStageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerTensorComplexDerivedStage I M n ≅
      ((idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)).obj (op n)) :=
  (Q.mapIso (eqToIso (idealPowerTensorComplex_eq_tensorObj I M n))) ≪≫
    (Functor.Monoidal.μIso Q
      (idealPowerStageSingleComplex I n) M).symm ≪≫
    (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
        (idealPowerRingStage I (n + 1))) ⊗ᵢ Iso.refl _) ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct
        (idealPowerDerivedStage I n) (Q.obj M)

private theorem idealPowerDerivedTensorToTensorComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    ((derivedTensorProduct (Q.obj M)).map (idealPowerDerivedStep I n)) ≫
        (idealPowerTensorComplexDerivedStageIso I M n).inv =
      (idealPowerTensorComplexDerivedStageIso I M (n + 1)).inv ≫
        idealPowerTensorComplexDerivedStep I M n := sorry

private abbrev idealPowerDerivedTensorToTensorComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    (idealPowerDerivedInverseSystem I ⋙ derivedTensorProduct (Q.obj M)) ⟶
      idealPowerTensorComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ (idealPowerTensorComplexDerivedStageIso I M n).inv)
    (fun n ↦ by
      simpa using idealPowerDerivedTensorToTensorComplex_step_comm I M n)

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
  sorry

end
