import Mathlib
import StacksProject_2024.Chap10.Lemma_10_25_2
import StacksProject_2024.Chap10.Lemma_10_42_3
import StacksProject_2024.Chap10.Lemma_10_42_4
import StacksProject_2024.Chap10.Lemma_10_43_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct

universe u v w

section

variable {k : Type u} {R : Type v} {S : Type w}
variable [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Chap10 Lemma 10 43 5: every minimal prime carries its canonical primality
instance. -/
local instance minimalPrime_isPrime {A : Type*} [CommRing A] (p : minimalPrimes A) : p.1.IsPrime :=
  Ideal.minimalPrimes_isPrime p.2

/-- Helper for Chap10 Lemma 10 43 5: reducedness descends to `k`-subalgebras. -/
private lemma isReduced_subalgebra_of_isReduced
    {κ A : Type*} [Field κ] [CommRing A] [Algebra κ A] [IsReduced A] (T : Subalgebra κ A) :
    IsReduced T := by
  -- Reducedness reflects across the injective inclusion into the ambient ring.
  exact isReduced_of_injective T.val Subtype.val_injective

/-- Helper for Chap10 Lemma 10 43 5: tensoring an injective algebra map on the right over a field
stays injective. -/
private lemma tensorProduct_map_injective_of_injective_rightAlgHom
    {κ A B C : Type*}
    [Field κ] [CommRing A] [CommRing B] [CommRing C]
    [Algebra κ A] [Algebra κ B] [Algebra κ C]
    (f : B →ₐ[κ] C) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id κ A) f) := by
  -- Over a field, tensoring preserves injectivity on both sides.
  simpa using
    TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : A →ₗ[κ] A)
      f.toLinearMap
      (fun _ _ h ↦ h)
      hf

/-- Helper for Chap10 Lemma 10 43 5: reducedness descends along an injective map on the left
tensor factor. -/
private lemma isReduced_tensorProduct_of_injective_leftAlgHom
    {κ E L A : Type*}
    [Field κ] [CommRing E] [CommRing L] [CommRing A]
    [Algebra κ E] [Algebra κ L] [Algebra κ A]
    (i : E →ₐ[κ] L) (hi : Function.Injective i)
    (hred : IsReduced (L ⊗[κ] A)) :
    IsReduced (E ⊗[κ] A) := by
  let φ : E ⊗[κ] A →+* L ⊗[κ] A :=
    Algebra.TensorProduct.map i (AlgHom.id κ A)
  have hφ : Function.Injective φ := by
    -- Tensoring the injective left map with the identity on the right stays injective.
    simpa [φ] using
      TensorProduct.map_injective_of_flat_flat
        i.toLinearMap
        (LinearMap.id : A →ₗ[κ] A)
        hi
        (fun _ _ h ↦ h)
  letI : IsReduced (L ⊗[κ] A) := hred
  exact isReduced_of_injective φ hφ

/-- Helper for Chap10 Lemma 10 43 5: reducedness is invariant under commuting tensor factors. -/
private lemma isReduced_tensorProduct_comm_iff
    {κ A B : Type*}
    [Field κ] [CommRing A] [CommRing B] [Algebra κ A] [Algebra κ B] :
    IsReduced (A ⊗[κ] B) ↔ IsReduced (B ⊗[κ] A) := by
  constructor
  · intro hAB
    let e : A ⊗[κ] B ≃ₐ[κ] B ⊗[κ] A := Algebra.TensorProduct.comm κ A B
    letI : IsReduced (A ⊗[κ] B) := hAB
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  · intro hBA
    let e : B ⊗[κ] A ≃ₐ[κ] A ⊗[κ] B := Algebra.TensorProduct.comm κ B A
    letI : IsReduced (B ⊗[κ] A) := hBA
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Helper for Chap10 Lemma 10 43 5: it is enough to prove reducedness on the finitely generated
tensor stages supplied by Lemma `10.43.4`. -/
private lemma isReduced_tensorProduct_of_forall_fgSubalgebraPair
    [IsReduced R] [IsGeometricallyReduced k S]
    (hfg : ∀ T : @FGSubalgebraPair k R S _ _ _ _ _, IsReduced (T.left ⊗[k] T.right)) :
    IsReduced (R ⊗[k] S) := by
  -- Any nonreduced witness in the ambient tensor product already appears on one finite stage.
  by_contra hnot
  obtain ⟨T, hTnot⟩ := exists_fg_subalgebras_not_isReduced_tensorProduct
    (k := k) (R := R) (S := S) hnot
  exact hTnot (hfg T)

/-- Helper for Chap10 Lemma 10 43 5: the polynomial base-change stage is reduced. -/
private theorem isReduced_tensor_mvPolynomial
    {κ A ι : Type*} [Field κ] [CommRing A] [Algebra κ A] [IsReduced A] :
    IsReduced (A ⊗[κ] MvPolynomial ι κ) := by
  let ePoly : A ⊗[κ] MvPolynomial ι κ ≃+* MvPolynomial ι A :=
    (MvPolynomial.algebraTensorAlgEquiv (σ := ι) κ A).toRingEquiv
  -- Proof comment: `MvPolynomial.algebraTensorAlgEquiv` rewrites the tensor stage to the
  -- polynomial ring over `A`, whose reducedness is an instance.
  letI : IsReduced (MvPolynomial ι A) := inferInstance
  exact isReduced_of_injective ePoly.toRingHom ePoly.injective

/-- Helper for Chap10 Lemma 10 43 5: the left tensor map induced by a tower
`R → Q → S` sends `Q ⊗[R] T` to `S ⊗[R] T`. -/
private abbrev tensorLeftMap
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    Q ⊗[R] T →ₐ[R] S ⊗[R] T :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T)

/-- Helper for Chap10 Lemma 10 43 5: the left tensor map fixes the right tensor
inclusion. -/
private lemma tensorLeftMap_includeRight_comp
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toSMul
    (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp
        (Algebra.TensorProduct.includeRight : T →ₐ[R] Q ⊗[R] T).toRingHom =
      (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom := by
  let baseMap : Q ⊗[R] T →ₐ[R] S ⊗[R] T :=
    tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)
  -- Proof comment: after installing the algebra structure from `baseMap`, the claim is the
  -- pure-tensor computation on `1 ⊗ₜ t`.
  rw [RingHom.algebraMap_toAlgebra baseMap.toRingHom]
  ext t
  simpa [baseMap, tensorLeftMap, Algebra.TensorProduct.includeRight_apply] using
    (Algebra.TensorProduct.map_tmul
      (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T) (1 : Q) t)

/-- Helper for Chap10 Lemma 10 43 5: the left tensor map makes
`Q → Q ⊗[R] T → S ⊗[R] T` agree with the canonical left tensor algebra map. -/
private lemma tensorLeftMap_q_tower
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommSemiring S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] :
    letI : Module Q S := Algebra.toModule
    letI : SMul Q (S ⊗[R] T) := TensorProduct.leftHasSMul
    letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toSMul
    IsScalarTower Q (Q ⊗[R] T) (S ⊗[R] T) := by
  letI : Module Q S := Algebra.toModule
  let baseMap : Q ⊗[R] T →ₐ[R] S ⊗[R] T :=
    tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)
  letI : SMul Q (S ⊗[R] T) := TensorProduct.leftHasSMul
  letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) := baseMap.toAlgebra
  letI : SMul (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toSMul
  -- Proof comment: scalar-tower compatibility reduces to the pure-tensor image of `q ⊗ₜ 1`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro q
  rw [RingHom.algebraMap_toAlgebra baseMap.toRingHom]
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.TensorProduct.algebraMap_apply]
  rw [Algebra.algebraMap_self_apply]
  exact (Algebra.TensorProduct.map_tmul
    (IsScalarTower.toAlgHom R Q S) (AlgHom.id R T) q (1 : T)).symm

/-- Helper for Chap10 Lemma 10 43 5: tensoring a localization on the left remains a
localization after base change along the right tensor factor. -/
private lemma tensorLeftMap_isLocalization
    {R Q S T : Type*} [CommSemiring R] [CommSemiring Q] [CommRing S]
    [CommSemiring T] [Algebra R Q] [Algebra R S] [Algebra Q S]
    [IsScalarTower R Q S] [Algebra R T] (M : Submonoid Q) [IsLocalization M S] :
    letI : Module Q S := Algebra.toModule
    letI : SMul Q (S ⊗[R] T) := TensorProduct.leftHasSMul
    letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
      (tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
    letI : SMul (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toSMul
    letI : Module (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toModule
    IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[R] T) M) (S ⊗[R] T) := by
  letI : Module Q S := Algebra.toModule
  letI : SMul Q (S ⊗[R] T) := TensorProduct.leftHasSMul
  letI : Algebra (Q ⊗[R] T) (S ⊗[R] T) :=
    (tensorLeftMap (R := R) (Q := Q) (S := S) (T := T)).toAlgebra
  letI : SMul (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toSMul
  letI : Module (Q ⊗[R] T) (S ⊗[R] T) := Algebra.toModule
  have hTower : IsScalarTower Q (Q ⊗[R] T) (S ⊗[R] T) :=
    tensorLeftMap_q_tower (R := R) (Q := Q) (S := S) (T := T)
  letI : IsScalarTower Q (Q ⊗[R] T) (S ⊗[R] T) := hTower
  have hRight :
      (algebraMap (Q ⊗[R] T) (S ⊗[R] T)).comp
          (Algebra.TensorProduct.includeRight : T →ₐ[R] Q ⊗[R] T).toRingHom =
        (Algebra.TensorProduct.includeRight : T →ₐ[R] S ⊗[R] T).toRingHom :=
    tensorLeftMap_includeRight_comp (R := R) (Q := Q) (S := S) (T := T)
  -- Proof comment: mathlib's tensor-product localization theorem applies once the right
  -- inclusion and scalar-tower compatibilities are fixed explicitly.
  exact
    @IsLocalization.tensorProduct_tensorProduct R T _ _ _ Q _ _ M S
      _ _ _ _ _ _ hTower hRight

/-- Helper for Chap10 Lemma 10 43 5: tensoring a rational-function field with a reduced
`κ`-algebra remains reduced. -/
private theorem isReduced_tensor_fractionRing_of_mvPolynomial
    {κ A ι : Type*} [Field κ] [CommRing A] [Algebra κ A] [IsReduced A] :
    IsReduced (FractionRing (MvPolynomial ι κ) ⊗[κ] A) := by
  let Q := MvPolynomial ι κ
  let F := FractionRing Q
  -- Proof comment: view the target as the localization of `Q ⊗[κ] A` at the image of
  -- the nonzero-divisors of `Q`.
  letI : Module Q F := Algebra.toModule
  letI : SMul Q (F ⊗[κ] A) := TensorProduct.leftHasSMul
  letI : Algebra (Q ⊗[κ] A) (F ⊗[κ] A) :=
    (tensorLeftMap (R := κ) (Q := Q) (S := F) (T := A)).toAlgebra
  letI : SMul (Q ⊗[κ] A) (F ⊗[κ] A) := Algebra.toSMul
  letI : Module (Q ⊗[κ] A) (F ⊗[κ] A) := Algebra.toModule
  letI : IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[κ] A) (nonZeroDivisors Q))
      (F ⊗[κ] A) :=
    tensorLeftMap_isLocalization (R := κ) (Q := Q) (S := F) (T := A)
      (nonZeroDivisors Q)
  have hSource : IsReduced (Q ⊗[κ] A) := by
    -- Proof comment: commute the polynomial tensor stage already identified with
    -- `MvPolynomial ι A`.
    simpa [Q] using
      (isReduced_tensorProduct_comm_iff (κ := κ) (A := A) (B := MvPolynomial ι κ)).1
        (isReduced_tensor_mvPolynomial (κ := κ) (A := A) (ι := ι))
  letI : IsReduced (Q ⊗[κ] A) := hSource
  -- Proof comment: reducedness is preserved by localization.
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (Q ⊗[κ] A) (nonZeroDivisors Q)) (F ⊗[κ] A) hSource

/-- Helper for Chap10 Lemma 10 43 5: after identifying a transcendence-basis stage with a
rational-function field, tensoring with a reduced algebra stays reduced. -/
private theorem isReduced_tensor_adjoin_of_isTranscendenceBasis
    {κ A L ι : Type*}
    [Field κ] [CommRing A] [Algebra κ A] [IsReduced A]
    [Field L] [Algebra κ L]
    (x : ι → L) (hx : IsTranscendenceBasis κ x) :
    IsReduced (IntermediateField.adjoin κ (Set.range x) ⊗[κ] A) := by
  let eAdjoin :
      IntermediateField.adjoin κ (Set.range x) ⊗[κ] A ≃+*
        FractionRing (MvPolynomial ι κ) ⊗[κ] A :=
    (Algebra.TensorProduct.congr
      hx.1.aevalEquivField.symm
      (AlgEquiv.refl : A ≃ₐ[κ] A)).toRingEquiv
  letI : IsReduced (FractionRing (MvPolynomial ι κ) ⊗[κ] A) :=
    isReduced_tensor_fractionRing_of_mvPolynomial (κ := κ) (A := A) (ι := ι)
  exact isReduced_of_injective eAdjoin.toRingHom eAdjoin.injective

/-- Helper for Chap10 Lemma 10 43 5: a separable polynomial cuts out a reduced adjoin-root
quotient over a field. -/
private theorem isReduced_adjoinRoot_of_separable
    {F : Type*} [Field F] (P : Polynomial F) (hP : P.Separable) :
    IsReduced (AdjoinRoot P) := by
  -- A separable polynomial is squarefree, hence generates a radical ideal.
  change IsReduced (Polynomial F ⧸ Ideal.span ({P} : Set (Polynomial F)))
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact hP.squarefree.isRadical

/-- Helper for Chap10 Lemma 10 43 5: a one-generator algebraic extension is identified with its
`AdjoinRoot` model. -/
private noncomputable def simple_generator_adjoinRoot_algEquiv
    {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hyInt : IsIntegral E y)
    (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤) :
    AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
  let eTop : IntermediateField.adjoin E ({y} : Set L) ≃ₐ[E] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  (IntermediateField.adjoinRootEquivAdjoin E hyInt).trans eTop

/-- Helper for Chap10 Lemma 10 43 5: under the polynomial tensor equivalence, the right tensor
inclusion of a polynomial becomes coefficientwise base change. -/
private theorem polyEquivTensor_symm_includeRight
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    (polyEquivTensor' E A).symm
      ((Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E) p) =
        Polynomial.map (algebraMap E A) p := by
  rw [Algebra.TensorProduct.includeRight_apply]
  simpa using
    (polyEquivTensor_symm_apply_tmul_eq_smul (R := E) (A := A) (a := (1 : A)) (p := p))

/-- Helper for Chap10 Lemma 10 43 5: the tensor-side principal ideal generated by one polynomial
becomes the principal ideal of its coefficientwise image. -/
private theorem tensor_adjoinRoot_ideal_map_eq_span
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)) =
      Ideal.map ((polyEquivTensor' E A).symm : A ⊗[E] Polynomial E →ₐ[A] Polynomial A).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
          (Ideal.span ({p} : Set (Polynomial E)))) := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (polyEquivTensor_symm_includeRight (E := E) (A := A) p).symm

/-- Helper for Chap10 Lemma 10 43 5: base changing an adjoin-root algebra produces the
adjoin-root algebra of the mapped polynomial. -/
private noncomputable def tensor_adjoinRoot_ringEquiv
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    A ⊗[E] AdjoinRoot p ≃+* AdjoinRoot (Polynomial.map (algebraMap E A) p) :=
  let eQuot :
      A ⊗[E] AdjoinRoot p ≃ₐ[A]
        (A ⊗[E] Polynomial E) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
            (Ideal.span ({p} : Set (Polynomial E))) :=
    Algebra.TensorProduct.tensorQuotientEquiv (R := E) A (Polynomial E) A
      (Ideal.span ({p} : Set (Polynomial E)))
  let ePoly :
      ((A ⊗[E] Polynomial E) ⧸
          Ideal.map
            (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
            (Ideal.span ({p} : Set (Polynomial E)))) ≃ₐ[A]
        Polynomial A ⧸ Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)) :=
    Ideal.quotientEquivAlg
      (I := Ideal.map
        (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
        (Ideal.span ({p} : Set (Polynomial E))))
      (J := Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)))
      ((polyEquivTensor' E A).symm)
      (tensor_adjoinRoot_ideal_map_eq_span (E := E) (A := A) p)
  (eQuot.trans ePoly).toRingEquiv

/-- Helper for Chap10 Lemma 10 43 5: after localizing a reduced finite-type algebra at a minimal
prime, the separable adjoin-root tensor factor is still reduced. -/
private theorem minimalPrimeLocalization_tensorAdjoinRoot_reduced
    {E : Type*} [Field E]
    {B : Type*} [CommRing B] [Algebra E B] [IsReduced B] [Algebra.FiniteType E B]
    (q : minimalPrimes B) (p : Polynomial E) (hp : p.Separable) :
    IsReduced (AdjoinRoot p ⊗[E] Localization.AtPrime q.1) := by
  let _ : Field (Localization.AtPrime q.1) :=
    (isField_localizationAtPrime_of_minimalPrime (R := B) q).toField
  let eTensor :
      AdjoinRoot p ⊗[E] Localization.AtPrime q.1 ≃+*
        AdjoinRoot (Polynomial.map (algebraMap E (Localization.AtPrime q.1)) p) :=
    ((Algebra.TensorProduct.comm E (AdjoinRoot p) (Localization.AtPrime q.1)).toRingEquiv).trans
      (tensor_adjoinRoot_ringEquiv (E := E) (A := Localization.AtPrime q.1) p)
  have hpMap :
      (Polynomial.map (algebraMap E (Localization.AtPrime q.1)) p).Separable := by
    -- Proof comment: separability survives the coefficient extension from `E` to the field
    -- factor `Localization.AtPrime q.1`.
    simpa using
      (Polynomial.Separable.map
        (f := algebraMap E (Localization.AtPrime q.1)) hp)
  letI :
      IsReduced (AdjoinRoot (Polynomial.map (algebraMap E (Localization.AtPrime q.1)) p)) :=
    isReduced_adjoinRoot_of_separable
      (P := Polynomial.map (algebraMap E (Localization.AtPrime q.1)) p) hpMap
  -- Proof comment: transport reducedness back along the canonical adjoin-root tensor
  -- identification over the minimal-prime field factor.
  exact isReduced_of_injective eTensor.toRingHom eTensor.injective

/-- Helper for Chap10 Lemma 10 43 5: the product target built from the minimal-prime field
factors of one finitely generated base stage. -/
private abbrev adjoinRootStageTensorTarget
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (B : Subalgebra E A) (p : Polynomial E) : Type _ :=
  ∀ q : minimalPrimes B, AdjoinRoot p ⊗[E] Localization.AtPrime q.1

/-- Helper for Chap10 Lemma 10 43 5: tensoring the minimal-prime embedding of one finitely
generated base stage with `AdjoinRoot p` gives the comparison map into the product of field
factors. -/
private noncomputable abbrev adjoinRootStageCompare
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (B : Subalgebra E A) (p : Polynomial E)
    [Fintype (minimalPrimes B)] [DecidableEq (minimalPrimes B)] :
    AdjoinRoot p ⊗[E] B →ₐ[E] adjoinRootStageTensorTarget (E := E) B p :=
  (Algebra.TensorProduct.piRight E E (AdjoinRoot p)
    (fun q : minimalPrimes B ↦ Localization.AtPrime q.1)).toAlgHom.comp
    (Algebra.TensorProduct.map
      (AlgHom.id E (AdjoinRoot p))
      (IsScalarTower.toAlgHom E B (∀ q : minimalPrimes B, Localization.AtPrime q.1)))

/-- Helper for Chap10 Lemma 10 43 5: the minimal-prime comparison map for one finitely generated
base stage is injective. -/
private theorem adjoinRootStageCompare_injective
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A] [IsReduced A]
    (B : Subalgebra E A) (p : Polynomial E)
    [Fintype (minimalPrimes B)] [DecidableEq (minimalPrimes B)] :
    Function.Injective (adjoinRootStageCompare (E := E) B p) := by
  classical
  let _ : IsReduced B := isReduced_subalgebra_of_isReduced (κ := E) (A := A) B
  have hEmbed :
      Function.Injective
        (IsScalarTower.toAlgHom E B (∀ q : minimalPrimes B, Localization.AtPrime q.1)) := by
    -- Proof comment: the base stage embeds into the product of its minimal-prime field factors.
    simpa using (algebraMap_embedding_into_product_of_fields (R := B)).1
  have hTensor :
      Function.Injective
        (Algebra.TensorProduct.map
          (AlgHom.id E (AdjoinRoot p))
          (IsScalarTower.toAlgHom E B (∀ q : minimalPrimes B, Localization.AtPrime q.1))) :=
    tensorProduct_map_injective_of_injective_rightAlgHom
      (κ := E)
      (A := AdjoinRoot p)
      (B := B)
      (C := ∀ q : minimalPrimes B, Localization.AtPrime q.1)
      (IsScalarTower.toAlgHom E B (∀ q : minimalPrimes B, Localization.AtPrime q.1))
      hEmbed
  -- Proof comment: the product decomposition is an equivalence, so it preserves injectivity.
  exact
    (Algebra.TensorProduct.piRight E E (AdjoinRoot p)
      (fun q : minimalPrimes B ↦ Localization.AtPrime q.1)).injective.comp hTensor

/-- Helper for Chap10 Lemma 10 43 5: tensoring a separable adjoin-root algebra with a reduced
finitely generated base stage stays reduced. -/
private theorem isReduced_fgSubalgebra_tensor_adjoinRoot_of_separable
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A] [IsReduced A]
    (B : Subalgebra E A) (hB : B.FG)
    (p : Polynomial E) (hp : p.Separable) :
    IsReduced (AdjoinRoot p ⊗[E] B) := by
  classical
  let _ : IsReduced B := isReduced_subalgebra_of_isReduced (κ := E) (A := A) B
  let _ : Algebra.FiniteType E B := (Subalgebra.fg_iff_finiteType B).mp hB
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing E B
  let _ : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  let _ : DecidableEq (minimalPrimes B) := Classical.decEq _
  let compare := adjoinRootStageCompare (E := E) B p
  have hCompare : Function.Injective compare :=
    adjoinRootStageCompare_injective (E := E) (A := A) B p
  let _ :
      ∀ q : minimalPrimes B, IsReduced (AdjoinRoot p ⊗[E] Localization.AtPrime q.1) :=
    fun q ↦
      minimalPrimeLocalization_tensorAdjoinRoot_reduced
        (E := E) (B := B) q p hp
  let _ :
      Pow (adjoinRootStageTensorTarget (E := E) B p) ℕ :=
    ⟨fun x n q ↦ x q ^ n⟩
  let _ :
      IsReduced (adjoinRootStageTensorTarget (E := E) B p) :=
    { eq_zero := fun x hx ↦
        let ⟨n, hn⟩ := hx
        funext fun q ↦ IsReduced.eq_zero (x q) ⟨n, congrFun hn q⟩ }
  -- Proof comment: once every field-valued factor is reduced, reducedness descends back along
  -- the injective comparison map from the finite tensor stage.
  exact isReduced_of_injective compare.toRingHom hCompare

/-- Helper for Chap10 Lemma 10 43 5: tensoring a separable adjoin-root algebra with a reduced
base ring stays reduced. -/
private theorem isReduced_tensor_adjoinRoot_of_separable
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A] [IsReduced A]
    (p : Polynomial E) (hp : p.Separable) :
    IsReduced (AdjoinRoot p ⊗[E] A) := by
  -- Proof comment: reduce to finitely generated subalgebras of the reduced base ring and embed
  -- each finite stage into the product of its minimal-prime field localizations.
  exact
    IsReduced.tensorProduct_of_flat_of_forall_fg
      (fun B hB ↦
        isReduced_fgSubalgebra_tensor_adjoinRoot_of_separable
          (A := A) B hB p hp)

/-- Helper for Chap10 Lemma 10 43 5: a one-generator separable extension stays reduced after
tensoring with a reduced algebra. -/
private theorem isReduced_tensor_simple_separable_extension_of_reduced
    {E : Type*} [Field E]
    {A0 : Type*} [CommRing A0] [Algebra E A0] [IsReduced A0]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤)
    (hySep : IsSeparable E y) :
    IsReduced (L ⊗[E] A0) := by
  let hyInt : IsIntegral E y := hySep.isIntegral
  let eSimple : AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
    simple_generator_adjoinRoot_algEquiv (E := E) hyInt hgen
  have hReducedSimple :
      IsReduced (AdjoinRoot (minpoly E y) ⊗[E] A0) :=
    isReduced_tensor_adjoinRoot_of_separable
      (E := E) (A := A0) (p := minpoly E y) hySep
  let eTensor :
      AdjoinRoot (minpoly E y) ⊗[E] A0 ≃+*
        L ⊗[E] A0 :=
    (Algebra.TensorProduct.congr eSimple (AlgEquiv.refl : A0 ≃ₐ[E] A0)).toRingEquiv
  letI : IsReduced (AdjoinRoot (minpoly E y) ⊗[E] A0) := hReducedSimple
  exact isReduced_of_injective eTensor.symm.toRingHom eTensor.symm.injective

/-- Helper for Chap10 Lemma 10 43 5: a Stacks primitive-generator witness already shows that
adjoining the generator over the transcendence-basis field gives the whole extension. -/
private theorem adjoin_singleton_eq_top_of_oneSeparableGenerator
    {κ : Type*} [Field κ]
    {L : Type*} [Field L] [Algebra κ L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg κ L)) → L)
    {y : L} (hy : IsOneSeparableGeneratorOver x y) :
    IntermediateField.adjoin (IntermediateField.adjoin κ (Set.range x)) ({y} : Set L) = ⊤ := by
  let F : IntermediateField κ L := IntermediateField.adjoin κ (Set.range x)
  have hAdjoinRestrict :
      (IntermediateField.adjoin F ({y} : Set L)).restrictScalars κ = ⊤ := by
    -- Proof comment: Lemma `10.42.3` rewrites the primitive-element adjoin step over `F` as the
    -- original `κ`-adjoin of the transcendence basis together with `y`.
    calc
      (IntermediateField.adjoin F ({y} : Set L)).restrictScalars κ =
          IntermediateField.adjoin κ (Set.range x ∪ {y}) := by
            simpa [F] using
              restrictScalars_adjoin_singleton_eq_adjoin_union
                (k := κ) (K := L) (S := Set.range x) y
      _ = ⊤ := hy.1
  apply top_unique
  intro z hzTop
  have hzRestrict :
      z ∈ ((IntermediateField.adjoin F ({y} : Set L)).restrictScalars κ :
        IntermediateField κ L) := by
    simpa [hAdjoinRestrict] using hzTop
  simpa [F] using hzRestrict

/-- Helper for Chap10 Lemma 10 43 5: the primitive-generator tensor tower cancels back to the
original tensor product. -/
private noncomputable abbrev primitiveGeneratorTensor_ringEquiv
    {κ F A L : Type*}
    [Field κ] [Field F] [CommRing A] [Field L]
    [Algebra κ F] [Algebra κ A] [Algebra κ L] [Algebra F L] [IsScalarTower κ F L] :
    L ⊗[F] (F ⊗[κ] A) ≃+* L ⊗[κ] A :=
  (Algebra.TensorProduct.cancelBaseChange κ F L L A).toRingEquiv

/-- Helper for Chap10 Lemma 10 43 5: a separably generated essentially finite type field
extension with one chosen primitive generator stays reduced after tensoring with a reduced
algebra. -/
private theorem isReducedTensorProductOfOneSeparableGenerator
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsReduced A]
    {L : Type*} [Field L] [Algebra κ L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg κ L)) → L) (hx : IsTranscendenceBasis κ x)
    {y : L} (hy : IsOneSeparableGeneratorOver x y) :
    IsReduced (L ⊗[κ] A) := by
  let F : IntermediateField κ L := IntermediateField.adjoin κ (Set.range x)
  -- Route correction: keep every intermediate object literally over the field `F = κ(x)`, then
  -- cancel the iterated tensor product only once at the end.
  letI : Module ↥F (↥F ⊗[κ] A) := TensorProduct.leftModule
  letI : Algebra ↥F (↥F ⊗[κ] A) := Algebra.TensorProduct.leftAlgebra
  letI : CommRing (↥F ⊗[κ] A) := TensorProduct.instCommRing (R := κ) (A := ↥F) (B := A)
  letI : CommSemiring (L ⊗[↥F] (↥F ⊗[κ] A)) :=
    TensorProduct.instCommSemiring (R := ↥F) (A := L) (B := ↥F ⊗[κ] A)
  letI : Ring (L ⊗[↥F] (↥F ⊗[κ] A)) :=
    TensorProduct.instRing (R := ↥F) (A := L) (B := ↥F ⊗[κ] A)
  letI : CommRing (L ⊗[↥F] (↥F ⊗[κ] A)) :=
    TensorProduct.instCommRing (R := ↥F) (A := L) (B := ↥F ⊗[κ] A)
  let T := L ⊗[↥F] (↥F ⊗[κ] A)
  have hBaseReduced : IsReduced (↥F ⊗[κ] A) :=
    isReduced_tensor_adjoin_of_isTranscendenceBasis (κ := κ) (A := A) (L := L) x hx
  have hGenerator : IntermediateField.adjoin ↥F ({y} : Set L) = ⊤ := by
    simpa using adjoin_singleton_eq_top_of_oneSeparableGenerator (κ := κ) x hy
  have hSimpleStage : IsReduced T := by
    letI : IsReduced (↥F ⊗[κ] A) := hBaseReduced
    -- Proof comment: over the transcendence-basis field `F`, the extension is generated by one
    -- separable element, so the simple-extension tensor theorem applies directly.
    exact
      isReduced_tensor_simple_separable_extension_of_reduced
        (E := ↥F)
        (A0 := ↥F ⊗[κ] A)
        (L := L)
        (y := y)
        hGenerator
        hy.2
  let eCancel : T ≃+* L ⊗[κ] A :=
    primitiveGeneratorTensor_ringEquiv (κ := κ) (F := ↥F) (A := A) (L := L)
  let ψ : L ⊗[κ] A →+* T := eCancel.symm.toRingHom
  -- Proof comment: the final tensor tower is the standard `cancelBaseChange` equivalence.
  constructor
  intro z hz
  -- Proof comment: nilpotence transports along the inverse ring homomorphism `ψ`.
  have hzSource : IsNilpotent (ψ z) := hz.map ψ
  have hψinj : Function.Injective ψ := by
    intro a b hab
    exact eCancel.symm.injective hab
  have hzero : ψ z = 0 := hSimpleStage.eq_zero (ψ z) hzSource
  have hzero' : ψ z = ψ 0 := by
    calc
      ψ z = 0 := hzero
      _ = ψ 0 := by rw [RingHom.map_zero]
  exact hψinj hzero'

/-- Helper for Chap10 Lemma 10 43 5: a separably generated essentially finite type field
extension stays reduced after tensoring with a reduced algebra. -/
private theorem isReducedTensorProductOfSeparablyGeneratedField
    {κ : Type*} [Field κ]
    {A : Type*} [CommRing A] [Algebra κ A] [IsReduced A]
    {L : Type*} [Field L] [Algebra κ L] [Algebra.EssFiniteType κ L]
    [IsSeparablyGenerated κ L] :
    IsReduced (L ⊗[κ] A) := by
  obtain ⟨x, hx, y, hy⟩ :=
    exists_transcendence_basis_and_one_separable_generator (k := κ) (K := L)
  exact
    isReducedTensorProductOfOneSeparableGenerator
      (κ := κ) (A := A) (L := L) x hx hy

/-- Helper for Chap10 Lemma 10 43 5: if a field extension is essentially of finite type over `k`,
then tensoring it with a geometrically reduced `k`-algebra is reduced. -/
private lemma essFiniteTypeField_tensor_right_reduced
    {K : Type v} [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    [IsGeometricallyReduced k S] :
    IsReduced (S ⊗[k] K) := by
  obtain ⟨k', hk'Field, hk'Alg, K', hK'Field, hkK', hKK', hk'K', hkKK', hkk'K', hLift⟩ :
      ∃ (k' : Type (max u w)) (_ : Field k') (_ : Algebra k k')
        (K' : Type (max v (max u w))) (_ : Field K') (_ : Algebra k K') (_ : Algebra K K')
        (_ : Algebra k' K') (_ : IsScalarTower k K K') (_ : IsScalarTower k k' K'),
          IsPurelyInseparableLiftWithSeparablyGenerated k K k' K' :=
    exists_purelyInseparable_lift_with_separablyGenerated (k := k) (K := K)
  letI : Field k' := hk'Field
  letI : Algebra k k' := hk'Alg
  letI : Field K' := hK'Field
  letI : Algebra k K' := hkK'
  letI : Algebra K K' := hKK'
  letI : Algebra k' K' := hk'K'
  letI : IsScalarTower k K K' := hkKK'
  letI : IsScalarTower k k' K' := hkk'K'
  letI : FiniteDimensional K K' := hLift.finiteDimensional_top
  letI : IsPurelyInseparable K K' := hLift.purelyInseparable_top
  letI : FiniteDimensional k k' := hLift.finiteDimensional_base
  letI : IsPurelyInseparable k k' := hLift.purelyInseparable_base
  letI : IsSeparablyGenerated k' K' := hLift.separablyGenerated_top
  letI : Algebra.IsAlgebraic k k' := IsPurelyInseparable.isAlgebraic k k'
  letI : Algebra.EssFiniteType K K' := inferInstance
  letI : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  letI : Algebra.EssFiniteType k' K' := Algebra.EssFiniteType.of_comp k k' K'
  have hBaseReduced : IsReduced (k' ⊗[k] S) := by
    -- Proof comment: geometric reducedness over `k` already gives reducedness after any
    -- algebraic base change, in particular for the purely inseparable lift `k' / k`.
    infer_instance
  have hLiftedReduced : IsReduced (K' ⊗[k'] (k' ⊗[k] S)) := by
    -- Proof comment: the lifted top extension is separably generated over `k'`, so the previous
    -- field theorem applies over the reduced base `k' ⊗[k] S`.
    exact
      isReducedTensorProductOfSeparablyGeneratedField
        (κ := k') (A := k' ⊗[k] S) (L := K')
  let eCancel :
      K' ⊗[k'] (k' ⊗[k] S) ≃+* K' ⊗[k] S :=
    (Algebra.TensorProduct.cancelBaseChange k k' K' K' S).toRingEquiv
  have hK'TensorReduced : IsReduced (K' ⊗[k] S) := by
    letI : IsReduced (K' ⊗[k'] (k' ⊗[k] S)) := hLiftedReduced
    -- Proof comment: cancel the iterated base change to identify the lifted tensor product with
    -- the simpler tensor `K' ⊗[k] S`.
    exact isReduced_of_injective eCancel.symm.toRingHom eCancel.symm.injective
  have hKTensorReduced : IsReduced (K ⊗[k] S) := by
    -- Proof comment: reducedness descends along the injective map `K →ₐ[k] K'`.
    exact
      isReduced_tensorProduct_of_injective_leftAlgHom
        (κ := k)
        (E := K)
        (L := K')
        (A := S)
        (IsScalarTower.toAlgHom k K K')
        (IsScalarTower.toAlgHom k K K').injective
        hK'TensorReduced
  -- Proof comment: commute the tensor factors back to the target orientation used in this file.
  exact (isReduced_tensorProduct_comm_iff (κ := k) (A := K) (B := S)).1 hKTensorReduced

/-- Helper for Chap10 Lemma 10 43 5: tensoring the geometrically reduced right stage with a
minimal-prime field factor of a finitely generated left stage stays reduced. -/
private lemma minimalPrime_localization_tensor_right_reduced
    [IsReduced R] [Algebra.FiniteType k R] [IsGeometricallyReduced k S]
    (p : minimalPrimes R) :
    IsReduced (S ⊗[k] Localization.AtPrime p.1) := by
  let _ : Field (Localization.AtPrime p.1) :=
    (isField_localizationAtPrime_of_minimalPrime (R := R) p).toField
  let _ : Algebra.EssFiniteType R (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.of_isLocalization
      (R := R)
      (S := Localization.AtPrime p.1)
      p.1.primeCompl
  let _ : Algebra.EssFiniteType k (Localization.AtPrime p.1) :=
    Algebra.EssFiniteType.comp k R (Localization.AtPrime p.1)
  exact essFiniteTypeField_tensor_right_reduced (k := k) (S := S)

/-- Helper for Chap10 Lemma 10 43 5: the minimal-prime field tensor factor attached to one finite
stage. -/
private abbrev fgStageFieldFactor
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    (p : minimalPrimes T.left) : Type _ :=
  T.right ⊗[k] Localization.AtPrime p.1

/-- Helper for Chap10 Lemma 10 43 5: the product of the minimal-prime field tensor factors
attached to one finite stage. -/
private abbrev fgStageTensorTarget
    (T : @FGSubalgebraPair k R S _ _ _ _ _) : Type _ :=
  ∀ p : minimalPrimes T.left, fgStageFieldFactor (k := k) (R := R) (S := S) T p

/-- Helper for Chap10 Lemma 10 43 5: after commuting the tensor factors, tensoring the
minimal-prime embedding of the left stage gives a comparison map into the product of field
factors. -/
private noncomputable abbrev fgStageTensorCompare
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
  (((Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).toAlgHom).comp
      (Algebra.TensorProduct.map (AlgHom.id k T.right)
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)))).comp
    (Algebra.TensorProduct.comm k T.left T.right).toAlgHom

/-- Helper for Chap10 Lemma 10 43 5: the finite-stage comparison map into the product of field
factors is injective. -/
private lemma fg_stage_tensor_to_minimalPrime_fields_injective
    (T : @FGSubalgebraPair k R S _ _ _ _ _)
    [IsReduced T.left] [Fintype (minimalPrimes T.left)] [DecidableEq (minimalPrimes T.left)] :
    Function.Injective (fgStageTensorCompare (k := k) (R := R) (S := S) T) := by
  have hleft :
      Function.Injective
        (IsScalarTower.toAlgHom
          k
          T.left
          (∀ p : minimalPrimes T.left, Localization.AtPrime p.1)) :=
    (algebraMap_embedding_into_product_of_fields (R := T.left)).1
  have htensor :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id k T.right)
          (IsScalarTower.toAlgHom
            k
            T.left
            (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))) :=
    tensorProduct_map_injective_of_injective_rightAlgHom
      (κ := k)
      (A := T.right)
      (B := T.left)
      (C := ∀ p : minimalPrimes T.left, Localization.AtPrime p.1)
      (IsScalarTower.toAlgHom
        k
        T.left
        (∀ p : minimalPrimes T.left, Localization.AtPrime p.1))
      hleft
  exact
    (Algebra.TensorProduct.piRight k k T.right
      (fun p : minimalPrimes T.left ↦ Localization.AtPrime p.1)).injective.comp
      (htensor.comp (Algebra.TensorProduct.comm k T.left T.right).injective)

/-- Helper for Chap10 Lemma 10 43 5: one finitely generated tensor stage is reduced by embedding
it into the product of its minimal-prime field factors. -/
private lemma fgSubalgebraPair_isReduced_tensorProduct
    [IsReduced R] [IsGeometricallyReduced k S]
    (T : @FGSubalgebraPair k R S _ _ _ _ _) :
    IsReduced (T.left ⊗[k] T.right) := by
  classical
  let _ : IsReduced T.left :=
    isReduced_subalgebra_of_isReduced (κ := k) (A := R) T.left
  let _ : IsGeometricallyReduced k T.right :=
    IsGeometricallyReduced.of_injective T.right.val Subtype.val_injective
  let _ : Algebra.FiniteType k T.left :=
    (Subalgebra.fg_iff_finiteType T.left).mp T.left_fg
  let _ : IsNoetherianRing T.left := Algebra.FiniteType.isNoetherianRing k T.left
  let _ : Fintype (minimalPrimes T.left) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := T.left)).fintype
  let compare :
      T.left ⊗[k] T.right →ₐ[k] fgStageTensorTarget (k := k) (R := R) (S := S) T :=
    fgStageTensorCompare (k := k) (R := R) (S := S) T
  have hcompare : Function.Injective compare :=
    fg_stage_tensor_to_minimalPrime_fields_injective (k := k) (R := R) (S := S) T
  let _ :
      ∀ p : minimalPrimes T.left, IsReduced (fgStageFieldFactor (k := k) (R := R) (S := S) T p) :=
    fun p ↦
      minimalPrime_localization_tensor_right_reduced
        (k := k) (R := T.left) (S := T.right) p
  let _ : Pow (fgStageTensorTarget (k := k) (R := R) (S := S) T) ℕ :=
    ⟨fun x n p ↦ x p ^ n⟩
  let _ : IsReduced (fgStageTensorTarget (k := k) (R := R) (S := S) T) :=
    { eq_zero := fun x hx ↦
        let ⟨n, hn⟩ := hx
        funext fun p ↦ IsReduced.eq_zero (x p) ⟨n, congrFun hn p⟩ }
  exact isReduced_of_injective compare.toMonoidWithZeroHom hcompare

-- Proof sketch: first descend nonreducedness to a finitely generated tensor stage using
-- Lemma `10.43.4`, then prove that finite stage reduced by embedding it into a product of field
-- factors and invoking the field-extension case on each factor.
/-- Chap10 Lemma 10 43 5 (Tag 034N): if `S` is geometrically reduced over the field `k` and
`R` is a reduced `k`-algebra, then `R ⊗[k] S` is reduced. -/
@[stacks 034N, instance]
theorem isReduced_tensorProduct_of_geometricallyReduced
    [IsReduced R] [IsGeometricallyReduced k S] :
    IsReduced (R ⊗[k] S) := by
  refine isReduced_tensorProduct_of_forall_fgSubalgebraPair
    (k := k) (R := R) (S := S) ?_
  intro T
  exact fgSubalgebraPair_isReduced_tensorProduct (k := k) (R := R) (S := S) T

end
