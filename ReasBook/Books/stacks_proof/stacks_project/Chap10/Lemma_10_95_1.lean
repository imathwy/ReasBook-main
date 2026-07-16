import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_83_2
import stacks_proof.stacks_project.Chap10.Lemma_10_88_10
import stacks_proof.stacks_project.Chap10.Example_10_91_1
import stacks_proof.stacks_project.Chap10.Proposition_10_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open CategoryTheory
open CategoryTheory.Limits

universe u v w x y

namespace Module

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable [Module.FaithfullyFlat R S]

omit [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: distributing base change over a tensor product is compatible
with tensoring a base-changed map on the right. -/
private lemma distribBaseChange_rTensor_baseChange
    {P : Type x} {N : Type y} {Q : Type w}
    [AddCommMonoid P] [Module R P] [AddCommMonoid N] [Module R N]
    [AddCommMonoid Q] [Module R Q] (f : P →ₗ[R] N) :
    ((f.baseChange S).rTensor (S ⊗[R] Q)).comp
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S P Q).toLinearMap =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R S N Q).toLinearMap.comp
        ((f.rTensor Q).baseChange S) := by
  -- Both composites are maps out of `S ⊗[R] (P ⊗[R] Q)`, so pure tensors determine them.
  ext s pq
  simp

/-- Helper for Chap10 Lemma 10 95 1: universal injectivity descends from a faithfully flat
base change. -/
private lemma universallyInjective_of_baseChange_universallyInjective
    {P : Type x} {N : Type y}
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    (f : P →ₗ[R] N)
    (hfS : LinearMap.UniversallyInjective.{v, max v x, max v y, max v w} (f.baseChange S)) :
    LinearMap.UniversallyInjective.{u, x, y, w} f := by
  intro Q _ _
  have hS : Function.Injective ((f.baseChange S).rTensor (S ⊗[R] Q)) :=
    hfS (S ⊗[R] Q) inferInstance inferInstance
  have hbase : Function.Injective ((f.rTensor Q).baseChange S) := by
    intro a b hab
    let eP := TensorProduct.AlgebraTensorModule.distribBaseChange R S P Q
    let eN := TensorProduct.AlgebraTensorModule.distribBaseChange R S N Q
    apply eP.injective
    apply hS
    have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
      (N := N) (Q := Q) f
    have ha := LinearMap.congr_fun hcompat a
    have hb := LinearMap.congr_fun hcompat b
    calc
      ((f.baseChange S).rTensor (S ⊗[R] Q)) (eP a)
          = eN (((f.rTensor Q).baseChange S) a) := by
              simpa [eP, eN, LinearMap.comp_apply] using ha
      _ = eN (((f.rTensor Q).baseChange S) b) := by rw [hab]
      _ = ((f.baseChange S).rTensor (S ⊗[R] Q)) (eP b) := by
              simpa [eP, eN, LinearMap.comp_apply] using hb.symm
  have hlTensor : Function.Injective ((f.rTensor Q).lTensor S) := by
    simpa [LinearMap.baseChange_eq_ltensor] using hbase
  -- Faithful flatness reflects injectivity from the left tensor by `S`.
  exact (Module.FaithfullyFlat.lTensor_injective_iff_injective
    (R := R) (M := S) (f := f.rTensor Q)).mp hlTensor

/-- Helper for Chap10 Lemma 10 95 1: the intrinsic tensor-kernel factorization criterion
associated to a `Module.MittagLeffler` module. -/
private theorem mittagLeffler_kernelFactorization_condition
    {A : Type u} [CommRing A]
    {X : Type (max v w)} [AddCommGroup X] [Module A X]
    (hML : MittagLeffler A X) :
    ∀ (P : ModuleCat.{max v w} A) [Module.FinitePresentation A P] (f : P →ₗ[A] X),
      ∃ (Q : ModuleCat.{max v w} A) (_ : Module.FinitePresentation A Q) (g : P →ₗ[A] Q),
        ∀ N : ModuleCat.{max v w} A,
          LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) := by
  -- Choose the owner-level presentation contained in the Mittag-Leffler structure and unpack its
  -- finite-presentation and Hom-inverse-system conditions.
  let pres : MittagLefflerPresentation A X := Classical.choice hML.exists_presentation
  letI : Preorder pres.index := pres.indexPreorder
  letI : Nonempty pres.index := pres.indexNonempty
  letI : IsDirectedOrder pres.index := pres.indexDirected
  let c : colimit pres.diagram ≅ ModuleCat.of A X := Classical.choice pres.colimitIso
  have hfp : ∀ i, Module.FinitePresentation A (pres.diagram.obj i) :=
    pres.presentation_isMittagLeffler.1
  have hhom : ∀ N : ModuleCat.{max v w} A,
      (colimitPresentationHomInverseSystem pres.diagram N).IsMittagLeffler :=
    pres.presentation_isMittagLeffler.2
  -- Proposition `10.88.6` converts that presentation-level Hom condition to the intrinsic
  -- kernel-factorization condition.
  have htfae :=
    directed_colimit_presentation_mittag_leffler_tfae
      (R := A) (I := pres.index) (M := X) pres.diagram hfp c
  exact (htfae.out 3 0 rfl rfl).mp hhom

/-- Helper for Chap10 Lemma 10 95 1: equality of tensor kernels after faithfully flat base
change reflects to equality of the original tensor kernels. -/
private lemma tensorKernel_eq_of_baseChange_tensorKernel_eq
    {P N Q : Type (max u v w)}
    [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] N) (g : P →ₗ[R] Q)
    (hS : ∀ T : ModuleCat.{max u v w} R,
      LinearMap.ker ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) =
        LinearMap.ker ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T)))) :
    ∀ T : ModuleCat.{max u v w} R,
      LinearMap.ker (f.rTensor T) = LinearMap.ker (g.rTensor T) := by
  intro T
  apply le_antisymm
  · intro z hz
    -- Push a downstairs kernel element to the faithfully flat base change and compare the
    -- normalized upstairs kernels there.
    let eP := TensorProduct.AlgebraTensorModule.distribBaseChange R S P T
    let eN := TensorProduct.AlgebraTensorModule.distribBaseChange R S N T
    let eQ := TensorProduct.AlgebraTensorModule.distribBaseChange R S Q T
    let zS : S ⊗[R] (P ⊗[R] T) := 1 ⊗ₜ[R] z
    have hfS : eP zS ∈
        LinearMap.ker ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) := by
      have hz0 : (f.rTensor T) z = 0 := by
        simpa [LinearMap.mem_ker] using hz
      have hzbase : ((f.rTensor T).baseChange S) zS = 0 := by
        simp [zS, LinearMap.baseChange_tmul, hz0]
      have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
        (N := N) (Q := T) f
      have hzcompat := LinearMap.congr_fun hcompat zS
      have hfzero :
          ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) = 0 := by
        calc
          ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS)
              = eN (((f.rTensor T).baseChange S) zS) := by
                  simpa [eP, eN, LinearMap.comp_apply] using hzcompat
          _ = eN 0 := by rw [hzbase]
          _ = 0 := by simp [eN]
      simpa [LinearMap.mem_ker] using hfzero
    have hgS : eP zS ∈
        LinearMap.ker ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) := by
      simpa [hS T] using hfS
    have hgS0 :
        ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) = 0 := by
      simpa [LinearMap.mem_ker] using hgS
    have hbase0 : ((g.rTensor T).baseChange S) zS = 0 := by
      have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
        (N := Q) (Q := T) g
      have hzcompat := LinearMap.congr_fun hcompat zS
      apply eQ.injective
      calc
        eQ (((g.rTensor T).baseChange S) zS)
            = ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) := by
                simpa [eP, eQ, LinearMap.comp_apply] using hzcompat.symm
        _ = 0 := hgS0
        _ = eQ 0 := by simp [eQ]
    have hg0 : (g.rTensor T) z = 0 := by
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := S) (M := Q ⊗[R] T)
      simpa [zS, LinearMap.baseChange_tmul] using hbase0
    simpa [LinearMap.mem_ker] using hg0
  · intro z hz
    -- The reverse inclusion is the same reflection argument with the two maps interchanged.
    let eP := TensorProduct.AlgebraTensorModule.distribBaseChange R S P T
    let eN := TensorProduct.AlgebraTensorModule.distribBaseChange R S N T
    let eQ := TensorProduct.AlgebraTensorModule.distribBaseChange R S Q T
    let zS : S ⊗[R] (P ⊗[R] T) := 1 ⊗ₜ[R] z
    have hgS : eP zS ∈
        LinearMap.ker ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) := by
      have hz0 : (g.rTensor T) z = 0 := by
        simpa [LinearMap.mem_ker] using hz
      have hzbase : ((g.rTensor T).baseChange S) zS = 0 := by
        simp [zS, LinearMap.baseChange_tmul, hz0]
      have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
        (N := Q) (Q := T) g
      have hzcompat := LinearMap.congr_fun hcompat zS
      have hgzero :
          ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) = 0 := by
        calc
          ((g.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS)
              = eQ (((g.rTensor T).baseChange S) zS) := by
                  simpa [eP, eQ, LinearMap.comp_apply] using hzcompat
          _ = eQ 0 := by rw [hzbase]
          _ = 0 := by simp [eQ]
      simpa [LinearMap.mem_ker] using hgzero
    have hfS : eP zS ∈
        LinearMap.ker ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) := by
      simpa [hS T] using hgS
    have hfS0 :
        ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) = 0 := by
      simpa [LinearMap.mem_ker] using hfS
    have hbase0 : ((f.rTensor T).baseChange S) zS = 0 := by
      have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
        (N := N) (Q := T) f
      have hzcompat := LinearMap.congr_fun hcompat zS
      apply eN.injective
      calc
        eN (((f.rTensor T).baseChange S) zS)
            = ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS) := by
                simpa [eP, eN, LinearMap.comp_apply] using hzcompat.symm
        _ = 0 := hfS0
        _ = eN 0 := by simp [eN]
    have hf0 : (f.rTensor T) z = 0 := by
      apply Module.FaithfullyFlat.tensorProduct_mk_injective
        (A := R) (B := S) (M := N ⊗[R] T)
      simpa [zS, LinearMap.baseChange_tmul] using hbase0
    simpa [LinearMap.mem_ker] using hf0

/-- Helper for Chap10 Lemma 10 95 1: domination descends from a faithfully flat base change. -/
private lemma dominates_of_baseChange_dominates
    {P N Q : Type (max u v w)}
    [AddCommGroup P] [Module R P]
    [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] N) (g : P →ₗ[R] Q)
    (hS : (g.baseChange S).Dominates (f.baseChange S)) :
    g.Dominates f := by
  intro T _ _ z hz
  -- Push a downstairs tensor-kernel element to the faithfully flat base change.
  let eP := TensorProduct.AlgebraTensorModule.distribBaseChange R S P T
  let eN := TensorProduct.AlgebraTensorModule.distribBaseChange R S N T
  let eQ := TensorProduct.AlgebraTensorModule.distribBaseChange R S Q T
  let zS : S ⊗[R] (P ⊗[R] T) := 1 ⊗ₜ[R] z
  have hfS : eP zS ∈
      LinearMap.ker ((f.baseChange S).rTensor (S ⊗[R] T)) := by
    have hz0 : (f.rTensor T) z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    have hzbase : ((f.rTensor T).baseChange S) zS = 0 := by
      simp [zS, LinearMap.baseChange_tmul, hz0]
    have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
      (N := N) (Q := T) f
    have hzcompat := LinearMap.congr_fun hcompat zS
    have hfzero :
        ((f.baseChange S).rTensor (S ⊗[R] T)) (eP zS) = 0 := by
      calc
        ((f.baseChange S).rTensor (ModuleCat.of S (S ⊗[R] T))) (eP zS)
            = eN (((f.rTensor T).baseChange S) zS) := by
                simpa [eP, eN, LinearMap.comp_apply] using hzcompat
        _ = eN 0 := by rw [hzbase]
        _ = 0 := by simp [eN]
    simpa [LinearMap.mem_ker] using hfzero
  have hgS : eP zS ∈
      LinearMap.ker ((g.baseChange S).rTensor (S ⊗[R] T)) :=
    hS (S ⊗[R] T) hfS
  have hgS0 :
      ((g.baseChange S).rTensor (S ⊗[R] T)) (eP zS) = 0 := by
    simpa [LinearMap.mem_ker] using hgS
  have hbase0 : ((g.rTensor T).baseChange S) zS = 0 := by
    have hcompat := distribBaseChange_rTensor_baseChange (R := R) (S := S) (P := P)
      (N := Q) (Q := T) g
    have hzcompat := LinearMap.congr_fun hcompat zS
    apply eQ.injective
    calc
      eQ (((g.rTensor T).baseChange S) zS)
          = ((g.baseChange S).rTensor (S ⊗[R] T)) (eP zS) := by
              simpa [eP, eQ, LinearMap.comp_apply] using hzcompat.symm
      _ = 0 := hgS0
      _ = eQ 0 := by simp [eQ]
  have hg0 : (g.rTensor T) z = 0 := by
    apply Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := R) (B := S) (M := Q ⊗[R] T)
    simpa [zS, LinearMap.baseChange_tmul] using hbase0
  simpa [LinearMap.mem_ker] using hg0

omit [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: the restricted scalar copy of `S` carries the usual
`R`, `S` scalar tower. -/
private instance extendScalarsSelf_isScalarTower :
    IsScalarTower R S
      (↑((ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))) :=
  ⟨by
    intro r s x
    rw [ModuleCat.restrictScalars.smul_def]
    rw [Algebra.smul_def]
    rw [mul_smul]
    rfl⟩

omit [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: `ModuleCat.extendScalars` has the same carrier as the
ordinary tensor-product base change. -/
private noncomputable abbrev extendScalarsObjTensorEquiv
    (P : ModuleCat.{max u v w} R) :
    ((ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj P) ≃ₗ[S]
      (S ⊗[R] P) :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
    (LinearEquiv.refl R P)

omit [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: the tensor spelling of `ModuleCat.extendScalars` is
compatible with the base change of a morphism. -/
private lemma extendScalarsObjTensorEquiv_map_hom
    {P N : ModuleCat.{max u v w} R} (f : P ⟶ N) :
    (f.hom.baseChange S).comp (extendScalarsObjTensorEquiv (R := R) (S := S) P).toLinearMap =
      (extendScalarsObjTensorEquiv (R := R) (S := S) N).toLinearMap.comp
        (((ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).map f).hom) := by
  -- Both maps are `S`-linear maps out of the extended-scalar object, so pure tensors determine
  -- them.
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      rfl
  | tmul s p =>
      dsimp [extendScalarsObjTensorEquiv]
      rfl
  | add x y hx hy =>
      let leftMap :=
        (f.hom.baseChange S).comp
          (extendScalarsObjTensorEquiv (R := R) (S := S) P).toLinearMap
      let rightMap :=
        (extendScalarsObjTensorEquiv (R := R) (S := S) N).toLinearMap.comp
          (((ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).map f).hom)
      calc
        leftMap (x + y) = leftMap x + leftMap y := leftMap.map_add x y
        _ = rightMap x + rightMap y := congrArg₂ HAdd.hAdd hx hy
        _ = rightMap (x + y) := (rightMap.map_add x y).symm

omit [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: domination is invariant under conjugating source and target
maps by linear equivalences. -/
private lemma dominates_of_linearEquiv_conjugate
    {A B C A' B' C' : Type (max u v w)}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    [AddCommGroup C'] [Module R C']
    (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    {f : A →ₗ[R] B} {g : A →ₗ[R] C} {f' : A' →ₗ[R] B'} {g' : A' →ₗ[R] C'}
    (hf : f'.comp eA.toLinearMap = eB.toLinearMap.comp f)
    (hg : g'.comp eA.toLinearMap = eC.toLinearMap.comp g)
    (h : g'.Dominates f') :
    g.Dominates f := by
  intro T _ _ z hz
  let eAT := LinearEquiv.rTensor T eA
  let eBT := LinearEquiv.rTensor T eB
  let eCT := LinearEquiv.rTensor T eC
  have hfT := congrArg (fun l : A →ₗ[R] B' ↦ l.rTensor T) hf
  have hgT := congrArg (fun l : A →ₗ[R] C' ↦ l.rTensor T) hg
  have hz' : eAT z ∈ LinearMap.ker (f'.rTensor T) := by
    have hz0 : (f.rTensor T) z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    have hcalc : (f'.rTensor T) (eAT z) = eBT ((f.rTensor T) z) := by
      simpa [eAT, eBT, LinearMap.rTensor_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hfT z
    simpa [LinearMap.mem_ker, hcalc, hz0, eBT]
  have hg'0 : (g'.rTensor T) (eAT z) = 0 := by
    simpa [LinearMap.mem_ker] using h T hz'
  have hgcalc : (g'.rTensor T) (eAT z) = eCT ((g.rTensor T) z) := by
    simpa [eAT, eCT, LinearMap.rTensor_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun hgT z
  have hg0' : eCT ((g.rTensor T) z) = 0 := hgcalc.symm.trans hg'0
  have hg0 : (g.rTensor T) z = 0 :=
    eCT.injective (by simpa [eCT] using hg0')
  simpa [LinearMap.mem_ker] using hg0

omit [CommRing R] [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] in
/-- Helper for Chap10 Lemma 10 95 1: domination transports from conjugate maps after moving
through linear equivalences from the conjugate source and targets. -/
private lemma dominates_of_linearEquiv_conjugate_source
    {A₀ : Type x} [CommRing A₀]
    {A B C A' B' C' : Type y}
    [AddCommGroup A] [Module A₀ A] [AddCommGroup B] [Module A₀ B]
    [AddCommGroup C] [Module A₀ C]
    [AddCommGroup A'] [Module A₀ A'] [AddCommGroup B'] [Module A₀ B']
    [AddCommGroup C'] [Module A₀ C']
    (eA : A' ≃ₗ[A₀] A) (eB : B' ≃ₗ[A₀] B) (eC : C' ≃ₗ[A₀] C)
    {f : A →ₗ[A₀] B} {g : A →ₗ[A₀] C} {f' : A' →ₗ[A₀] B'} {g' : A' →ₗ[A₀] C'}
    (hf : f.comp eA.toLinearMap = eB.toLinearMap.comp f')
    (hg : g.comp eA.toLinearMap = eC.toLinearMap.comp g')
    (h : g'.Dominates f') :
    g.Dominates f := by
  intro T _ _ z hz
  let eAT := LinearEquiv.rTensor T eA
  let eBT := LinearEquiv.rTensor T eB
  let eCT := LinearEquiv.rTensor T eC
  have hfT := congrArg (fun l : A' →ₗ[A₀] B ↦ l.rTensor T) hf
  have hgT := congrArg (fun l : A' →ₗ[A₀] C ↦ l.rTensor T) hg
  have hz' : eAT.symm z ∈ LinearMap.ker (f'.rTensor T) := by
    have hz0 : (f.rTensor T) z = 0 := by
      simpa [LinearMap.mem_ker] using hz
    have hcalc₀ : (f.rTensor T) ((eA.toLinearMap.rTensor T) (eAT.symm z)) =
        eBT ((f'.rTensor T) (eAT.symm z)) := by
      simpa [eAT, eBT, LinearMap.rTensor_comp, LinearMap.comp_apply] using
        LinearMap.congr_fun hfT (eAT.symm z)
    have hsource : (eA.toLinearMap.rTensor T) (eAT.symm z) = z := by
      change eAT (eAT.symm z) = z
      exact eAT.apply_symm_apply z
    have hcalc : (f.rTensor T) z =
        eBT ((f'.rTensor T) (eAT.symm z)) := by
      simpa [hsource] using hcalc₀
    have : eBT ((f'.rTensor T) (eAT.symm z)) = 0 := by
      simpa [hz0] using hcalc.symm
    have : (f'.rTensor T) (eAT.symm z) = 0 :=
      eBT.injective (by simpa [eBT] using this)
    simpa [LinearMap.mem_ker] using this
  have hg'0 : (g'.rTensor T) (eAT.symm z) = 0 := by
    simpa [LinearMap.mem_ker] using h T hz'
  have hgcalc₀ : (g.rTensor T) ((eA.toLinearMap.rTensor T) (eAT.symm z)) =
      eCT ((g'.rTensor T) (eAT.symm z)) := by
    simpa [eAT, eCT, LinearMap.rTensor_comp, LinearMap.comp_apply] using
      LinearMap.congr_fun hgT (eAT.symm z)
  have hsource : (eA.toLinearMap.rTensor T) (eAT.symm z) = z := by
    change eAT (eAT.symm z) = z
    exact eAT.apply_symm_apply z
  have hgcalc : (g.rTensor T) z =
      eCT ((g'.rTensor T) (eAT.symm z)) := by
    simpa [hsource] using hgcalc₀
  have hg0 : (g.rTensor T) z = 0 := by
    simpa [hg'0] using hgcalc
  simpa [LinearMap.mem_ker] using hg0

/- Source/core/bridge triage:
* source-facing: descent of the Mittag-Leffler property along a faithfully flat base change;
* core/canonical owner: `Module.MittagLeffler`, sampled via the finite-presentation colimit
  criterion and domination/universal-injectivity bridge from Proposition `10.88.6`;
* adjacent bridge theorem checked and rejected as the main owner reuse:
  `Module.mittagLeffler_restrictScalars_of_mittagLeffler_of_flat` from Lemma `10.89.11`, whose
  extra hypotheses `[MittagLeffler R S] [Module.Flat S M]` change the semantics of the present
  faithfully flat descent statement;
* bridge/view: descend universal injectivity for pushout legs after comparing base change with
  tensor distribution, then use it to descend tail domination in a finite-presentation
  presentation of `M`.
-/
-- Route correction: the older arbitrary-presentation tail-domination route forces a transport
-- comparison between an arbitrary base-changed presentation and the Mittag-Leffler presentation
-- over `S`. The verified prefix below instead records the intrinsic kernel criterion and the
-- faithful-flat kernel-reflection bridge; what remains is the universe-stable scalar-extension
-- presentation comparison and final packaging.
/-- Chap10 Lemma 10 95 1: if the faithfully flat base change `S ⊗[R] M` is a Mittag-Leffler `S`-module,
then `M` is a Mittag-Leffler `R`-module. -/
@[stacks 05A5]
theorem mittagLeffler_of_mittagLeffler_tensorProduct_of_faithfullyFlat
    [MittagLeffler S (S ⊗[R] M)] :
    MittagLeffler R M := by
  classical
  let M' := ULift.{max u v w} M
  have hMLLiftTensor : MittagLeffler S (S ⊗[R] M') := by
    let e : (S ⊗[R] M') ≃ₗ[S] (S ⊗[R] M) :=
      LinearEquiv.baseChange R S M' M ULift.moduleEquiv
    exact Module.mittagLeffler_of_linearEquiv e
  have hMLLift : MittagLeffler R M' := by
    letI : MittagLeffler S (S ⊗[R] M') := hMLLiftTensor
    obtain ⟨J, _, _, pres, hfp⟩ :=
      (show CategoryTheory.ObjectProperty.ind.{max u v w}
          (fun N : ModuleCat.{max u v w} R ↦ Module.FinitePresentation R N)
          (ModuleCat.of.{max u v w} R M') from
        (module_is_isomorphic_to_colimit_of_directed_system_of_finitelyPresented.{u, max v w}
          (R := R) (M := ModuleCat.of.{max u v w} R M')))
    obtain ⟨K, _, _, _, FJ, _⟩ := CategoryTheory.IsFiltered.exists_directed J
    let P : ColimitPresentation K (ModuleCat.of.{max u v w} R M') := pres.reindex FJ
    let F : K ⥤ ModuleCat.{max u v w} R := P.diag
    let cR : colimit F ≅ ModuleCat.of.{max u v w} R M' :=
      (P.isColimit.coconePointUniqueUpToIso (colimit.isColimit F)).symm
    have hfpR : ∀ k, Module.FinitePresentation R (F.obj k) := by
      intro k
      simpa [P, F] using hfp (FJ.obj k)
    let G := ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)
    letI : G.IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{max u v w, u, v} (algebraMap R S)).isLeftAdjoint
    let FS : K ⥤ ModuleCat.{max u v w} S := F ⋙ G
    let X : ModuleCat.{max u v w} S := G.obj (ModuleCat.of.{max u v w} R M')
    letI : AddCommGroup (X : Type (max u v w)) := inferInstance
    letI : Module S (X : Type (max u v w)) := inferInstance
    let cS : colimit FS ≅ ModuleCat.of.{max u v w} S (X : Type (max u v w)) :=
      (preservesColimitIso G F).symm ≪≫ G.mapIso cR
    have hMLObj : MittagLeffler S (X : Type (max u v w)) := by
      let e : (X : Type (max u v w)) ≃ₗ[S] (S ⊗[R] M') :=
        extendScalarsObjTensorEquiv (R := R) (S := S)
          (ModuleCat.of.{max u v w} R M')
      exact Module.mittagLeffler_of_linearEquiv e
    have hfpS : ∀ k, Module.FinitePresentation S (FS.obj k) := by
      intro k
      let e : (FS.obj k) ≃ₗ[S] (S ⊗[R] F.obj k) := by
        dsimp [FS, G]
        exact extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj k)
      letI : Module.FinitePresentation R (F.obj k) := hfpR k
      exact Module.FinitePresentation.of_equiv e.symm
    have hdomS : ∀ i : K, ∃ (j : K) (hij : i ≤ j),
        ((FS.map (homOfLE hij)).hom).Dominates ((colimit.ι FS i ≫ cS.hom).hom) := by
      have hcrit :
          ∀ (P : ModuleCat.{max u v w} S) [Module.FinitePresentation S P]
            (f : P →ₗ[S] (X : Type (max u v w))),
            ∃ (Q : ModuleCat.{max u v w} S) (_ : Module.FinitePresentation S Q)
              (g : P →ₗ[S] Q),
              ∀ N : ModuleCat.{max u v w} S,
                LinearMap.ker (f.rTensor N) = LinearMap.ker (g.rTensor N) :=
        mittagLeffler_kernelFactorization_condition.{v, max u v w, 0}
          (A := S) (X := (X : Type (max u v w))) hMLObj
      have htfae := directed_colimit_presentation_mittag_leffler_tfae (R := S) (I := K)
        (M := (X : Type (max u v w))) FS hfpS cS
      exact (htfae.out 0 1).mp hcrit
    have hdomR : ∀ i : K, ∃ (j : K) (hij : i ≤ j),
        ((F.map (homOfLE hij)).hom).Dominates ((colimit.ι F i ≫ cR.hom).hom) := by
      intro i
      obtain ⟨j, hij, hSdom⟩ := hdomS i
      let transition : F.obj i ⟶ F.obj j := F.map (homOfLE hij)
      let colimitMap : F.obj i ⟶ ModuleCat.of.{max u v w} R M' := colimit.ι F i ≫ cR.hom
      have hcolimitMapS :
          colimit.ι FS i ≫ cS.hom = G.map colimitMap := by
        dsimp [cS, FS, colimitMap]
        rw [ι_preservesColimitIso_inv_assoc]
        rw [← G.map_comp]
      have hSdom' :
          ((G.map transition).hom).Dominates ((G.map colimitMap).hom) := by
        simpa [transition, hcolimitMapS] using hSdom
      have hbaseS :
          (transition.hom.baseChange S).Dominates (colimitMap.hom.baseChange S) := by
        have hcolimitConj :
            (colimitMap.hom.baseChange S).comp
                (extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj i)).toLinearMap =
              (extendScalarsObjTensorEquiv (R := R) (S := S)
                  (ModuleCat.of.{max u v w} R M')).toLinearMap.comp
                ((G.map colimitMap).hom) :=
          extendScalarsObjTensorEquiv_map_hom (R := R) (S := S) colimitMap
        have htransitionConj :
            (transition.hom.baseChange S).comp
                (extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj i)).toLinearMap =
              (extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj j)).toLinearMap.comp
                ((G.map transition).hom) :=
          extendScalarsObjTensorEquiv_map_hom (R := R) (S := S) transition
        exact dominates_of_linearEquiv_conjugate_source
          (A₀ := S)
          (eA := extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj i))
          (eB := extendScalarsObjTensorEquiv (R := R) (S := S)
            (ModuleCat.of.{max u v w} R M'))
          (eC := extendScalarsObjTensorEquiv (R := R) (S := S) (F.obj j))
          (f := colimitMap.hom.baseChange S) (g := transition.hom.baseChange S)
          (f' := (G.map colimitMap).hom) (g' := (G.map transition).hom)
          hcolimitConj
          htransitionConj
          hSdom'
      refine ⟨j, hij, ?_⟩
      exact dominates_of_baseChange_dominates
        (R := R) (S := S) (f := colimitMap.hom) (g := transition.hom) hbaseS
    have hallR : ∀ N : ModuleCat.{max u v w} R,
        (colimitPresentationHomInverseSystem F N).IsMittagLeffler := by
      exact ((directed_colimit_presentation_mittag_leffler_tfae F hfpR cR).out 1 3).mp hdomR
    exact ⟨⟨{
      index := K
      indexPreorder := inferInstance
      indexNonempty := inferInstance
      indexDirected := inferInstance
      diagram := F
      presentation_isMittagLeffler := ⟨hfpR, hallR⟩
      colimitIso := ⟨cR⟩
    }⟩⟩
  exact Module.mittagLeffler_of_linearEquiv (ULift.moduleEquiv.symm : M ≃ₗ[R] M')

end

end Module
