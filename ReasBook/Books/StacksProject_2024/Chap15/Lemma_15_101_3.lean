import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.Chap04.Example_4_22_6
import StacksProject_2024.Chap15.Definition_15_59_13
import StacksProject_2024.Chap15.Lemma_15_101_1
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Proposition_15_95_2
import StacksProject_2024.Chap15.Remark_15_96_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open CochainComplex
open Opposite
open SequentialProObjectMorphismRep

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "CpxA" => CochainComplex (ModuleCat A) ℤ
local notation "KMod" => HomotopyCategory (ModuleCat A) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "singleCpx0" => CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)
private abbrev Q : CpxA ⥤ DMod := DerivedCategory.Q

private noncomputable instance : (Q : CpxA ⥤ DMod).Monoidal := by
  change
    (((HomotopyCategory.quotient (ModuleCat A) (up ℤ)) ⋙ Qh)).Monoidal
  infer_instance
 
/- 
Domain-style sampling for Lemma 15.101.3:
- primary domain: sequential inverse systems in `D(A)` built from ideal-power quotients of a
  bounded cochain complex and compared through `SequentialProObjectMorphismRep`;
- sampled owner declarations:
  `idealPowerQuotientDerivedInverseSystem`,
  `idealPowerQuotientTensorDerivedInverseSystem`,
  `reduceModIdealA`,
  `SequentialProObjectMorphismRep.toProObjectHom`;
- best owner abstraction:
  `source-facing`: the quotient-complex tower
    `(M^• / I^(n+1) M^•)_n` in `D(A)` and the resulting pro-isomorphism statement;
  `core/canonical`: `idealPowerQuotientDerivedInverseSystem`,
    `idealPowerQuotientTensorDerivedInverseSystem`, `reduceModIdealA`,
    `DerivedCategory.Q.map`, `Functor.ofOpSequence`, and `SequentialProObjectMorphismRep`;
  `bridge/view`: the quotient-complex transition maps assembling the target tower below.

Primitive-vs-derived split:
- primitive data: the ideal `I`, the cochain complex `M`, and the quotient-complex transition maps
  induced by `AdicCompletion.transitionMap`;
- derived API: the chapter owner `idealPowerQuotientDerivedInverseSystem`, its tensor image in
  `D(A)`, the canonical quotient-complex owner `reduceModIdealA`, the inverse system below, and
  the induced pro-object isomorphism.
-/

/-- The quotient complex `M^\bullet / I^(n+1) M^\bullet`, expressed through the chapter owner
`CochainComplex.reduceModIdealA`. -/
private abbrev idealPowerQuotientComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    CpxA :=
  reduceModIdealA (I ^ (n + 1)) M

private abbrev idealPowerQuotientComplexStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientComplex I M (n + 1) ⟶ idealPowerQuotientComplex I M n :=
  { f := fun i ↦
      show ModuleCat.of A (idealPowerModuleQuotient I (M.X i) (n + 1)) ⟶
          ModuleCat.of A (idealPowerModuleQuotient I (M.X i) n) from
        ModuleCat.ofHom (AdicCompletion.transitionMap I (M.X i) (Nat.le_succ (n + 1)))
    comm' := fun i j hij ↦ by
      sorry }

private abbrev idealPowerQuotientComplexDerivedStage
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    DMod :=
  Q.obj (idealPowerQuotientComplex I M n)

/-- The inverse-system step on the derived quotient-complex tower. -/
private abbrev idealPowerQuotientComplexDerivedStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientComplexDerivedStage I M (n + 1) ⟶
      idealPowerQuotientComplexDerivedStage I M n :=
  Q.map (idealPowerQuotientComplexStep I M n)

/-- The inverse system `(M^\bullet / I^(n+1) M^\bullet)_n` in `D(A)`. -/
abbrev idealPowerQuotientComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) :
    ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientComplexDerivedStep I M)

private abbrev idealPowerQuotientTensorComplexFunctor
    (I : Ideal A) (n : ℕ) : CpxA ⥤ CpxA :=
  (tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 1)))).mapHomologicalComplex (up ℤ)

private abbrev idealPowerQuotientTensorComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    CpxA :=
  (idealPowerQuotientTensorComplexFunctor I n).obj M

private abbrev idealPowerQuotientTensorStepNatTrans
    (I : Ideal A) (n : ℕ) :
    tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 2))) ⟶
      tensorLeft (ModuleCat.of A (A ⧸ I ^ (n + 1))) :=
  (tensoringLeft (ModuleCat A)).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap))

private abbrev idealPowerQuotientTensorComplexStepNatTrans
    (I : Ideal A) (n : ℕ) :
    idealPowerQuotientTensorComplexFunctor I (n + 1) ⟶
      idealPowerQuotientTensorComplexFunctor I n :=
  NatTrans.mapHomologicalComplex (idealPowerQuotientTensorStepNatTrans I n) (up ℤ)

private abbrev idealPowerQuotientTensorComplexStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M (n + 1) ⟶
      idealPowerQuotientTensorComplex I M n :=
  (idealPowerQuotientTensorComplexStepNatTrans I n).app M

private abbrev idealPowerQuotientTensorComplexDerivedStage
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    DMod :=
  Q.obj (idealPowerQuotientTensorComplex I M n)

private abbrev idealPowerQuotientTensorComplexDerivedStep
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexDerivedStage I M (n + 1) ⟶
      idealPowerQuotientTensorComplexDerivedStage I M n :=
  Q.map (idealPowerQuotientTensorComplexStep I M n)

private abbrev idealPowerQuotientTensorComplexDerivedInverseSystem
    (I : Ideal A) (M : CpxA) :
    ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientTensorComplexDerivedStep I M)

private abbrev idealPowerQuotientTensorComplexToQuotientComplex
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M n ⟶ idealPowerQuotientComplex I M n :=
  { f := fun i ↦
      show ModuleCat.of A (TensorProduct A (A ⧸ I ^ (n + 1)) (M.X i)) ⟶
          ModuleCat.of A (idealPowerModuleQuotient I (M.X i) n) from
        ModuleCat.ofHom
          (TensorProduct.quotTensorEquivQuotSMul (M.X i) (I ^ (n + 1))).toLinearMap
    comm' := fun i j hij ↦ by
      sorry }

private theorem idealPowerQuotientTensorComplexToQuotientComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexStep I M n ≫
        idealPowerQuotientTensorComplexToQuotientComplex I M n =
      idealPowerQuotientTensorComplexToQuotientComplex I M (n + 1) ≫
        idealPowerQuotientComplexStep I M n := by
  sorry

private abbrev idealPowerQuotientTensorComplexToQuotientComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorComplexDerivedInverseSystem I M ⟶
      idealPowerQuotientComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ Q.map (idealPowerQuotientTensorComplexToQuotientComplex I M n))
    (fun n ↦ by
      simpa [idealPowerQuotientTensorComplexDerivedStep] using
        congrArg Q.map
          (idealPowerQuotientTensorComplexToQuotientComplex_step_comm I M n))

private theorem idealPowerQuotientTensorComplex_eq_tensorObj
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplex I M n =
      HomologicalComplex.tensorObj
        ((singleCpx0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) M := by
  sorry

private noncomputable abbrev idealPowerQuotientTensorComplexDerivedStageIso
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    idealPowerQuotientTensorComplexDerivedStage I M n ≅
      (idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M)).obj (op n) :=
  (Q.mapIso (eqToIso (idealPowerQuotientTensorComplex_eq_tensorObj I M n))) ≪≫
    (Functor.Monoidal.μIso Q
      ((singleCpx0).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) M).symm ≪≫
      (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
          (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⊗ᵢ Iso.refl _) ≪≫
        derivedCategory_tensorObj_iso_derivedTensorProduct
          (idealPowerQuotientDerivedStage I n) (Q.obj M)

private theorem idealPowerQuotientDerivedTensorToTensorComplex_step_comm
    (I : Ideal A) (M : CpxA) (n : ℕ) :
    ((derivedTensorProduct (Q.obj M)).map (idealPowerQuotientDerivedStep I n)) ≫
        (idealPowerQuotientTensorComplexDerivedStageIso I M n).inv =
      (idealPowerQuotientTensorComplexDerivedStageIso I M (n + 1)).inv ≫
        idealPowerQuotientTensorComplexDerivedStep I M n := by
  sorry

private abbrev idealPowerQuotientDerivedTensorToTensorComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M) ⟶
      idealPowerQuotientTensorComplexDerivedInverseSystem I M :=
  NatTrans.ofOpSequence
    (fun n ↦ (idealPowerQuotientTensorComplexDerivedStageIso I M n).inv)
    (fun n ↦ by
      simpa using idealPowerQuotientDerivedTensorToTensorComplex_step_comm I M n)

-- Proof sketch: choose generators of `I` and replace the quotient ring tower by the
-- pro-isomorphic powered Koszul tower from Lemma `15.95.1`. Since each powered Koszul complex is a
-- bounded finite free complex, the tensor tower and the quotient-complex tower are uniformly
-- bounded in cohomology. Apply Lemma `13.42.5`, reducing to cohomology, and use Lemma `15.101.1`
-- on a bounded-above finite free resolution of `M^\bullet` to identify both cohomology towers
-- with the same tower `H^i(M^\bullet) / I^(n+1) H^i(M^\bullet)`.
/-- The canonical comparison from the derived tensor tower
`((A / I^(n+1))[0] ⊗_A^{\mathbf L} Q(M^\bullet))_n` to the quotient-complex tower
`(Q(M^\bullet / I^(n+1) M^\bullet))_n`. -/
abbrev idealPowerQuotientTensorToQuotientComplexNatTrans
    (I : Ideal A) (M : CpxA) :
    idealPowerQuotientTensorDerivedInverseSystem I (Q.obj M) ⟶
      idealPowerQuotientComplexDerivedInverseSystem I M :=
  idealPowerQuotientDerivedTensorToTensorComplexNatTrans I M ≫
    idealPowerQuotientTensorComplexToQuotientComplexNatTrans I M

section

variable [IsNoetherianRing A]

/-- Lemma 15.101.3: let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `M^\bullet`
be a bounded complex of finite `A`-modules. Then the inverse system of maps
`M^\bullet \otimes_A^{\mathbf L} A / I^(n+1) ⟶ M^\bullet / I^(n+1) M^\bullet` defines an
isomorphism of pro-objects of `D(A)`. In this item-file convention, stage `0` corresponds to the
textbook quotient by `I`. -/
theorem idealPowerQuotientTensorToQuotientComplex_isIso
    (I : Ideal A) (M : CpxA)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (ofNatTrans (idealPowerQuotientTensorToQuotientComplexNatTrans I M)).toProObjectHom :=
  sorry

end

end
