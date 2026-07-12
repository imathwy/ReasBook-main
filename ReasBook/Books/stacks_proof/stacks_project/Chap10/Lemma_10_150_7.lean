import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_150_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S'] [Algebra S S']
variable [IsScalarTower R S S']

/- Domain-style sampling:
- primary domain: Kähler differentials, diagonal ideals in tensor products, and formally étale
  base change for quotient thickenings;
- sampled owner declarations:
  `KaehlerDifferential.ideal`,
  `KaehlerDifferential.mapBaseChange`,
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`,
  `Algebra.TensorProduct.map`;
- best owner abstraction:
  the canonical owner for part (2) is the linear equivalence
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`; its underlying linear map is
  `KaehlerDifferential.mapBaseChange R S S'`, so bare bijectivity belongs only to derived API.
  For part (1), the diagonal ideal owner is `KaehlerDifferential.ideal R S'`, and the
  quotient-thickening map is only a bridge/view built from `Algebra.TensorProduct.map` and
  `Ideal.quotientMap`;
- primitive data vs. derived API:
  primitive data are the tower `R → S → S'` and the canonical diagonal ideal
  `KaehlerDifferential.ideal R S'`, together with the owner equivalence
  `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`;
  the underlying map `KaehlerDifferential.mapBaseChange R S S'`, the pulled-back diagonal ideal in
  `S' ⊗[R] S`, and the induced quotient map are derived bridge-level constructions and should not
  remain as separate public owner declarations;
- source/core/bridge triage:
  `source-facing`: the bijectivity statements on nilpotent thickenings and on
    `KaehlerDifferential.mapBaseChange`;
  `core/canonical`: `KaehlerDifferential.ideal R S'`,
    `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`;
  `bridge/view`: the underlying map `KaehlerDifferential.mapBaseChange R S S'`, the
    tensor-product comparison `S' ⊗[R] S → S' ⊗[R] S'`, its pulled-back diagonal ideal, and the
    induced quotient map. -/

-- Proof sketch: identify the source
-- `S' ⊗[S] ((S ⊗[R] S) / J^(k + 1))` with the quotient of `S' ⊗[R] S` by the pulled-back
-- diagonal ideal, then apply Lemma `10.150.6` to the canonical tensor-product map
-- `S' ⊗[R] S → S' ⊗[R] S'` and the diagonal ideal `KaehlerDifferential.ideal R S'`.
/-- Helper for Chap10 Lemma 10 150 7: the cancel-base-change equivalence sends the
base-changed algebra structure map to the tensor-comparison map. -/
private lemma tensorComparison_cancelBaseChangeAlg_commutes (x : S' ⊗[R] S) :
    let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
      Algebra.TensorProduct.lTensor (S := S') S' (IsScalarTower.toAlgHom R S S')
    letI : Algebra S (S' ⊗[R] S) :=
      Algebra.TensorProduct.rightAlgebra (R := R) (A := S') (B := S)
    let rightModule : Module S (S' ⊗[R] S) := Algebra.toModule
    let rightSMul : SMul S (S' ⊗[R] S) := rightModule.toDistribMulAction.toSMul
    letI : Module S (S' ⊗[R] S) := rightModule
    letI : SMul S (S' ⊗[R] S) := rightSMul
    letI : Algebra (S' ⊗[R] S) (S' ⊗[R] S') := tensorComparison.toAlgebra
    (Algebra.IsPushout.cancelBaseChangeAlg R S' S (S' ⊗[R] S) S')
        ((algebraMap (S' ⊗[R] S) ((S' ⊗[R] S) ⊗[S] S')) x) =
      (algebraMap (S' ⊗[R] S) (S' ⊗[R] S')) x := by
  dsimp only
  let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
    Algebra.TensorProduct.lTensor (S := S') S' (IsScalarTower.toAlgHom R S S')
  letI : Algebra S (S' ⊗[R] S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := S') (B := S)
  let rightModule : Module S (S' ⊗[R] S) := Algebra.toModule
  let rightSMul : SMul S (S' ⊗[R] S) := rightModule.toDistribMulAction.toSMul
  letI : Module S (S' ⊗[R] S) := rightModule
  letI : SMul S (S' ⊗[R] S) := rightSMul
  letI : Algebra (S' ⊗[R] S) (S' ⊗[R] S') := tensorComparison.toAlgebra
  -- It is enough to check the equality on pure tensors in `S' ⊗[R] S`.
  induction x with
  | zero => simp
  | add x y hx hy =>
      simpa [map_add] using congrArg₂ HAdd.hAdd (by simpa using hx) (by simpa using hy)
  | tmul a s =>
      change (Algebra.IsPushout.cancelBaseChangeAlg R S' S (S' ⊗[R] S) S')
          ((a ⊗ₜ[R] s : S' ⊗[R] S) ⊗ₜ[S] (1 : S')) =
        tensorComparison (a ⊗ₜ[R] s)
      -- Pull the target back through the equivalence and use the tensor relation over `S`.
      apply (Algebra.IsPushout.cancelBaseChangeAlg R S' S (S' ⊗[R] S) S').symm.injective
      rw [AlgEquiv.symm_apply_apply]
      have htc : tensorComparison (a ⊗ₜ[R] s) = a ⊗ₜ[R] algebraMap S S' s := by
        simp [tensorComparison, Algebra.TensorProduct.map_tmul]
      rw [htc]
      rw [Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul]
      have hfactor : (a ⊗ₜ[R] s : S' ⊗[R] S) =
          @SMul.smul S (S' ⊗[R] S) rightSMul s (a ⊗ₜ[R] (1 : S)) := by
        change (a ⊗ₜ[R] s : S' ⊗[R] S) =
          (algebraMap S (S' ⊗[R] S) s) * (a ⊗ₜ[R] (1 : S))
        rw [Algebra.TensorProduct.right_algebraMap_apply]
        simp [Algebra.TensorProduct.tmul_mul_tmul]
      rw [hfactor]
      calc
        @SMul.smul S (S' ⊗[R] S) rightSMul s (a ⊗ₜ[R] (1 : S)) ⊗ₜ[S]
            (1 : S') =
          (a ⊗ₜ[R] (1 : S) : S' ⊗[R] S) ⊗ₜ[S] (s • (1 : S')) := by
            exact Quotient.sound' <| AddConGen.Rel.of _ _ <|
              TensorProduct.Eqv.of_smul s (a ⊗ₜ[R] (1 : S)) (1 : S')
        _ = (algebraMap S' (S' ⊗[R] S)) a ⊗ₜ[S] (algebraMap S S') s := by
          simp [Algebra.smul_def]

/-- Helper for Chap10 Lemma 10 150 7: the canonical tensor-comparison map is the base change of the
formally étale map `S → S'`, so it is itself formally étale. -/
lemma tensorComparison_formallyEtale [Algebra.FormallyEtale S S'] :
    (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
      S' ⊗[R] S →+* S' ⊗[R] S').FormallyEtale := by
  let tensorComparison : S' ⊗[R] S →ₐ[S'] S' ⊗[R] S' :=
    Algebra.TensorProduct.lTensor (S := S') S' (IsScalarTower.toAlgHom R S S')
  letI : Algebra S (S' ⊗[R] S) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := S') (B := S)
  let rightModule : Module S (S' ⊗[R] S) := Algebra.toModule
  let rightSMul : SMul S (S' ⊗[R] S) := rightModule.toDistribMulAction.toSMul
  letI : Module S (S' ⊗[R] S) := rightModule
  letI : SMul S (S' ⊗[R] S) := rightSMul
  letI : Algebra (S' ⊗[R] S) (S' ⊗[R] S') := tensorComparison.toAlgebra
  -- The standard base-change instance gives formal étaleness of
  -- `(S' ⊗[R] S) ⊗[S] S'` over `S' ⊗[R] S`.
  let e : (S' ⊗[R] S) ⊗[S] S' ≃ₐ[S' ⊗[R] S] S' ⊗[R] S' :=
    { __ := Algebra.IsPushout.cancelBaseChangeAlg R S' S (S' ⊗[R] S) S',
      commutes' := tensorComparison_cancelBaseChangeAlg_commutes }
  have htarget : Algebra.FormallyEtale (S' ⊗[R] S) (S' ⊗[R] S') := by
    exact Algebra.FormallyEtale.of_equiv e
  -- Finally identify `tensorComparison` with the ring homomorphism in the statement.
  simpa [RingHom.FormallyEtale, tensorComparison, Algebra.TensorProduct.lTensor] using htarget

/-- Chap10 Lemma 10 150 7: if `S → S'` is formally étale, then the canonical quotient map
`(S' ⊗[R] S) / (Icomap)^(k + 1) → (S' ⊗[R] S') / (Jdiag)^(k + 1)`, where
`tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S'` is the canonical tensor comparison,
`Jdiag = KaehlerDifferential.ideal R S'`, and `Icomap = Ideal.comap tensorComparison Jdiag`,
is bijective for every `k`. This is the canonical tensor/quotient form of the textbook comparison
`S' ⊗[S] ((S ⊗[R] S) / J^(k + 1)) → (S' ⊗[R] S') / (J')^(k + 1)`. -/
@[stacks 0H93]
theorem formallyEtale_tensorProduct_quotientMap_pow_bijective
    [Algebra.FormallyEtale S S'] (k : ℕ) :
    let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
      (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
        S' ⊗[R] S →+* S' ⊗[R] S')
    let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
    let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
    Function.Bijective
      ((Ideal.quotientMap (Jdiag ^ (k + 1)) tensorComparison
          (Jdiag.le_comap_pow tensorComparison (k + 1))) :
        (S' ⊗[R] S) ⧸ (Icomap ^ (k + 1)) →+* (S' ⊗[R] S') ⧸ (Jdiag ^ (k + 1))) := by
  let tensorComparison : S' ⊗[R] S →+* S' ⊗[R] S' :=
    (Algebra.TensorProduct.map (AlgHom.id S S') (IsScalarTower.toAlgHom R S S') :
      S' ⊗[R] S →+* S' ⊗[R] S')
  let Jdiag : Ideal (S' ⊗[R] S') := KaehlerDifferential.ideal R S'
  let Icomap : Ideal (S' ⊗[R] S) := Ideal.comap tensorComparison Jdiag
  -- The tensor-comparison map is the standard base change of `S → S'`, hence formally étale.
  have hform : tensorComparison.FormallyEtale := by
    simpa [tensorComparison] using
      tensorComparison_formallyEtale (R := R) (S := S) (S' := S')
  -- To apply Lemma `10.150.6`, first show surjectivity modulo the diagonal ideal.
  have hsurj : Function.Surjective ((Ideal.Quotient.mk Jdiag).comp tensorComparison) := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine ⟨(Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[R] S)
        ((Algebra.TensorProduct.lmul' R) y), ?_⟩
    change
      Ideal.Quotient.mk Jdiag
          (tensorComparison (((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S))) =
        Ideal.Quotient.mk Jdiag y
    rw [Ideal.Quotient.eq]
    have hcomparison :
        tensorComparison (((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S)) =
          ((Algebra.TensorProduct.lmul' R) y) ⊗ₜ[R] (1 : S') := by
      simp [tensorComparison]
    rw [hcomparison]
    rw [RingHom.mem_ker]
    simp
  -- The quotient-thickening comparison is now exactly Lemma `10.150.6`.
  simpa [tensorComparison, Jdiag, Icomap] using
    RingHom.formallyEtale_quotientMap_pow_bijective
      (f := tensorComparison) (J := Jdiag) hform hsurj (k + 1)

/- Lemma 10.150.7 (2): for a formally étale map `S → S'`, the canonical map
`S' ⊗[S] Ω[S⁄R] → Ω[S'⁄R]` is exactly the owner equivalence
`KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S'`. -/
recall KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale

/-- Companion to Chap10 Lemma 10 150 7 (2): the underlying linear map
`KaehlerDifferential.mapBaseChange R S S'` is bijective. -/
theorem formallyEtale_kaehlerDifferential_mapBaseChange_bijective
    [Algebra.FormallyEtale S S'] :
    Function.Bijective (KaehlerDifferential.mapBaseChange R S S') := by
  simpa using (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S S').bijective

end
