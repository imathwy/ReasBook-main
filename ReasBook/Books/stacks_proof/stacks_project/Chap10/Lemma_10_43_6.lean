import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Lemma_10_42_3
import stacks_proof.stacks_project.Chap10.Lemma_10_43_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra

universe u v w

/-
Domain triage:
- `source-facing`: the main lemma is reducedness of `K ⊗[k] S` for a reduced `k`-algebra `S` and a
  Stacks-separable field extension `K / k`.
- `core/canonical`: the owner abstraction for the field-extension side is
  `Algebra.IsGeometricallyReduced k K`.
- `bridge/view`: the geometric-reducedness consequence is derived from the source-facing tensor
  product lemma by commuting `AlgebraicClosure k ⊗[k] K`.

Primitive data are the reduced algebra `S` and the separable extension `K / k`; geometric
reducedness of `K` is derived API, not primitive data.
-/

section

variable {k : Type u} {K : Type v} {S : Type w}
variable [Field k] [Field K] [CommRing S] [Algebra k K] [Algebra k S]

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Chap10 Lemma 10 43 6: a polynomial algebra base-changed to a field extension is
again a domain. -/
lemma mvPolynomial_tensor_field_isDomain
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    IsDomain (MvPolynomial ι k ⊗[k] κ) := by
  let ePoly : MvPolynomial ι k ⊗[k] κ ≃+* MvPolynomial ι κ :=
    (Algebra.TensorProduct.comm k (MvPolynomial ι k) κ).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k κ).toRingEquiv
  -- The standard tensor-polynomial equivalence identifies the base change with a polynomial ring.
  exact ePoly.isDomain_iff.mpr inferInstance

/-- Helper for Chap10 Lemma 10 43 6: non-zero-divisors of `MvPolynomial ι k` remain
non-zero-divisors after tensoring with a field extension. -/
lemma mvPolynomial_nonZeroDivisors_le_tensor
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    Algebra.algebraMapSubmonoid (MvPolynomial ι k ⊗[k] κ)
      (nonZeroDivisors (MvPolynomial ι k)) ≤ nonZeroDivisors (MvPolynomial ι k ⊗[k] κ) := by
  letI : IsDomain (MvPolynomial ι k ⊗[k] κ) :=
    mvPolynomial_tensor_field_isDomain (k := k) (ι := ι) (κ := κ)
  have hIncl : Function.Injective
      (Algebra.TensorProduct.includeLeft : MvPolynomial ι k →ₐ[k] MvPolynomial ι k ⊗[k] κ) := by
    -- Tensor inclusion is injective because the field map `k → κ` is injective.
    exact Algebra.TensorProduct.includeLeft_injective (S := k) (A := MvPolynomial ι k)
      (B := κ) (algebraMap k κ).injective
  -- Injective maps into a domain carry regular elements to regular elements.
  simpa [Algebra.algebraMapSubmonoid] using
    (map_le_nonZeroDivisors_of_injective
      (Algebra.TensorProduct.includeLeft : MvPolynomial ι k →ₐ[k] MvPolynomial ι k ⊗[k] κ)
      hIncl le_rfl)

/-- Helper for Chap10 Lemma 10 43 6: localizing a domain after tensoring with a fraction field
over the original domain remains a domain when the inverted elements remain regular. -/
lemma fractionRing_tensorOver_isDomain_of_le_nonZeroDivisors
    {A B : Type*} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B] [IsDomain B]
    (hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors A) ≤ nonZeroDivisors B) :
    IsDomain (FractionRing A ⊗[A] B) := by
  letI : Algebra B (FractionRing A ⊗[A] B) := Algebra.TensorProduct.rightAlgebra
  have hLoc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (FractionRing A ⊗[A] B) := by
    -- The tensor product over `A` is the base change of the fraction-ring localization.
    exact IsLocalization.tensorRight (R := A) (S := B) (A := FractionRing A)
      (nonZeroDivisors A)
  letI : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      (FractionRing A ⊗[A] B) := hLoc
  -- A localization of a domain at regular elements is again a domain.
  exact IsLocalization.isDomain_of_le_nonZeroDivisors (FractionRing A ⊗[A] B) hM

/-- Helper for Chap10 Lemma 10 43 6: localizing the tensor polynomial ring by the original
polynomial non-zero-divisors gives a domain. -/
lemma fractionRing_tensorOver_mvPolynomial_tensor_field_isDomain
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    IsDomain (FractionRing (MvPolynomial ι k) ⊗[MvPolynomial ι k]
      (MvPolynomial ι k ⊗[k] κ)) := by
  letI : IsDomain (MvPolynomial ι k ⊗[k] κ) :=
    mvPolynomial_tensor_field_isDomain (k := k) (ι := ι) (κ := κ)
  -- Apply the general localization-domain criterion to the polynomial tensor base.
  exact fractionRing_tensorOver_isDomain_of_le_nonZeroDivisors
    (A := MvPolynomial ι k) (B := MvPolynomial ι k ⊗[k] κ)
    (mvPolynomial_nonZeroDivisors_le_tensor (k := k) (ι := ι) (κ := κ))

/-- Helper for Chap10 Lemma 10 43 6: `cancelBaseChange` identifies the fraction-ring localization
normal form with the ordinary tensor over `k`. -/
noncomputable abbrev fractionRingMvPolynomialCancelBaseChange
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    FractionRing (MvPolynomial ι k) ⊗[MvPolynomial ι k] (MvPolynomial ι k ⊗[k] κ) ≃+*
      FractionRing (MvPolynomial ι k) ⊗[k] κ :=
  letI : Algebra (MvPolynomial ι k) (FractionRing (MvPolynomial ι k) ⊗[k] κ) :=
    Algebra.TensorProduct.leftAlgebra
  (Algebra.TensorProduct.cancelBaseChange k (MvPolynomial ι k) (MvPolynomial ι k)
    (FractionRing (MvPolynomial ι k)) κ).toRingEquiv

/-- Helper for Lemma 10.43.6: after base change to a field `κ / k`, the fraction-field stage of
the transcendence-basis argument is still a domain. -/
lemma isDomain_tensor_fractionRing_of_mvPolynomial
    {ι : Type*} {κ : Type*} [Field κ] [Algebra k κ] :
    IsDomain (FractionRing (MvPolynomial ι k) ⊗[k] κ) := by
  -- Work in the localization normal form and then cancel the intermediate base change.
  exact (fractionRingMvPolynomialCancelBaseChange (k := k) (ι := ι) (κ := κ)).isDomain_iff.mp
    (fractionRing_tensorOver_mvPolynomial_tensor_field_isDomain (k := k) (ι := ι) (κ := κ))

/-- Helper for Lemma 10.43.6: after identifying the transcendence-basis stage with a rational
function field, tensoring with any left field still yields a domain. -/
lemma isDomain_tensor_adjoin_of_isTranscendenceBasis
    {κ : Type*} [Field κ] [Algebra k κ]
    {L : Type*} [Field L] [Algebra k L]
    {ι : Type*} (x : ι → L) (hx : IsTranscendenceBasis k x) :
    IsDomain (κ ⊗[k] IntermediateField.adjoin k (Set.range x)) := by
  let P : Type _ := MvPolynomial ι k
  let eAdjoin :
      κ ⊗[k] IntermediateField.adjoin k (Set.range x) ≃+* (κ ⊗[k] FractionRing P) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : κ ≃ₐ[k] κ) hx.1.aevalEquivField.symm).toRingEquiv
  let ePoly :
      P ⊗[k] κ ≃+* MvPolynomial ι κ :=
    (Algebra.TensorProduct.comm k P κ).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) k κ).toRingEquiv
  have hPolyDomain : IsDomain (P ⊗[k] κ) := by
    -- After commuting the factors, the polynomial base change is exactly `MvPolynomial ι κ`.
    exact ePoly.isDomain_iff.mpr inferInstance
  have hFracDomain : IsDomain (FractionRing P ⊗[k] κ) := by
    -- This is the fraction-field domain step isolated from the localization transport.
    simpa [P] using
      isDomain_tensor_fractionRing_of_mvPolynomial (k := k) (ι := ι) (κ := κ)
  let eTensor :
      (κ ⊗[k] FractionRing P) ≃+* (FractionRing P ⊗[k] κ) :=
    (Algebra.TensorProduct.comm k κ (FractionRing P)).toRingEquiv
  -- Transport the fraction-field domain result back to the transcendence-basis stage.
  exact (eAdjoin.trans eTensor).isDomain_iff.mpr hFracDomain

/-- Helper for Lemma 10.43.6: a separable polynomial cuts out a reduced adjoin-root quotient. -/
lemma isReduced_adjoinRoot_of_separable
    {F : Type*} [Field F] (P : Polynomial F) (hP : P.Separable) :
    IsReduced (AdjoinRoot P) := by
  -- Route correction: package the squarefree-to-radical quotient step as a standalone field lemma
  -- instead of reproving it inside the final one-generator tensor argument.
  change IsReduced (Polynomial F ⧸ Ideal.span ({P} : Set (Polynomial F)))
  rw [← Ideal.isRadical_iff_quotient_reduced, ← isRadical_iff_span_singleton]
  exact hP.squarefree.isRadical

/-- Helper for Lemma 10.43.6: tensoring the injective map from a domain to its fraction field with
the identity on a finite-dimensional right field factor remains injective. -/
lemma tensorProduct_map_injective_to_fractionRing_of_finiteDimensional_right
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra E A]
    {L : Type*} [Field L] [Algebra E L] [FiniteDimensional E L] :
    Function.Injective
      (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom E A (FractionRing A))
        (AlgHom.id E L)) := by
  -- Over the base field `E`, both target modules are flat, so tensoring preserves injectivity.
  simpa using TensorProduct.map_injective_of_flat_flat
    (IsScalarTower.toAlgHom E A (FractionRing A)).toLinearMap
    (LinearMap.id : L →ₗ[E] L)
    (IsFractionRing.injective A (FractionRing A))
    (fun _ _ h ↦ h)

/-- Helper for Lemma 10.43.6: an algebraic simple generator identifies the whole field with the
corresponding `AdjoinRoot` model. -/
noncomputable def simple_generator_adjoinRoot_algEquiv
    {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hy_int : IsIntegral E y)
    (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤) :
    AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
  let eTop : IntermediateField.adjoin E ({y} : Set L) ≃ₐ[E] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  (IntermediateField.adjoinRootEquivAdjoin E hy_int).trans eTop

/-- Helper for Lemma 10.43.6: a field generated by one integral element is finite-dimensional over
the base field. -/
lemma finiteDimensional_of_singleton_adjoin_eq_top
    {E : Type*} [Field E]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hy_int : IsIntegral E y)
    (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤) :
    FiniteDimensional E L := by
  -- First control the one-generator intermediate field by integrality of `y`.
  letI : FiniteDimensional E (IntermediateField.adjoin E ({y} : Set L)) :=
    IntermediateField.adjoin.finiteDimensional hy_int
  let eTop : IntermediateField.adjoin E ({y} : Set L) ≃ₐ[E] L :=
    (IntermediateField.equivOfEq hgen).trans IntermediateField.topEquiv
  -- Then transport finite dimensionality across the identification with the top field.
  exact FiniteDimensional.of_injective
    eTop.symm.toLinearMap eTop.symm.injective

/-- Helper for Lemma 10.43.6: under the polynomial-tensor equivalence, the right tensor inclusion
of a polynomial is exactly coefficientwise base change. -/
lemma polyEquivTensor_symm_includeRight
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    (polyEquivTensor' E A).symm
      ((Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E) p) =
        Polynomial.map (algebraMap E A) p := by
  -- Rewrite the tensor-side polynomial relation as the mapped polynomial over `A`.
  rw [Algebra.TensorProduct.includeRight_apply]
  simpa using
    (polyEquivTensor_symm_apply_tmul_eq_smul (R := E) (A := A) (a := (1 : A)) (p := p))

/-- Helper for Lemma 10.43.6: after transporting along `polyEquivTensor`, the tensor-side ideal of
the relation `p` becomes the principal ideal of the mapped polynomial. -/
lemma tensor_adjoinRoot_ideal_map_eq_span
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    Ideal.span ({Polynomial.map (algebraMap E A) p} : Set (Polynomial A)) =
      Ideal.map ((polyEquivTensor' E A).symm : A ⊗[E] Polynomial E →ₐ[A] Polynomial A).toRingHom
        (Ideal.map
          (Algebra.TensorProduct.includeRight : Polynomial E →ₐ[E] A ⊗[E] Polynomial E)
          (Ideal.span ({p} : Set (Polynomial E)))) := by
  -- The quotient relation is still generated by one polynomial after passing through the tensor.
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (polyEquivTensor_symm_includeRight (E := E) (A := A) p).symm

/-- Helper for Lemma 10.43.6: base changing `AdjoinRoot p` along an `E`-algebra `A` produces the
adjoin-root algebra of the coefficientwise image of `p`. -/
noncomputable abbrev tensor_adjoinRoot_algEquiv
    {E : Type*} [Field E]
    {A : Type*} [CommRing A] [Algebra E A]
    (p : Polynomial E) :
    A ⊗[E] AdjoinRoot p ≃ₐ[A] AdjoinRoot (Polynomial.map (algebraMap E A) p) :=
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
  eQuot.trans ePoly

/-- Helper for Lemma 10.43.6: after passing to the fraction field on the left, a separable
one-relation extension stays reduced. -/
lemma isReduced_fractionRing_tensor_adjoinRoot_of_separable
    {E : Type*} [Field E]
    {A0 : Type*} [CommRing A0] [IsDomain A0] [Algebra E A0]
    (p : Polynomial E) (hp : p.Separable) :
    IsReduced (FractionRing A0 ⊗[E] AdjoinRoot p) := by
  have hpMap : (Polynomial.map (algebraMap E (FractionRing A0)) p).Separable := by
    -- Separability survives extension of coefficients to the fraction field.
    simpa using Polynomial.Separable.map (f := algebraMap E (FractionRing A0)) hp
  let e : FractionRing A0 ⊗[E] AdjoinRoot p ≃ₐ[FractionRing A0]
      AdjoinRoot (Polynomial.map (algebraMap E (FractionRing A0)) p) :=
    tensor_adjoinRoot_algEquiv (E := E) (A := FractionRing A0) p
  letI : IsReduced (AdjoinRoot (Polynomial.map (algebraMap E (FractionRing A0)) p)) :=
    isReduced_adjoinRoot_of_separable
      (P := Polynomial.map (algebraMap E (FractionRing A0)) p) hpMap
  -- Transport reducedness back across the adjoin-root base-change equivalence.
  exact isReduced_of_injective e.toRingHom e.injective

/-- Helper for Lemma 10.43.6: if `L / E` is generated by one separable element and `A0` is a
domain, then `A0 ⊗[E] L` is reduced. -/
lemma isReduced_tensor_simple_separable_extension_of_domain
    {E : Type*} [Field E]
    {A0 : Type*} [CommRing A0] [IsDomain A0] [Algebra E A0]
    {L : Type*} [Field L] [Algebra E L]
    {y : L} (hgen : IntermediateField.adjoin E ({y} : Set L) = ⊤)
    (hy_sep : IsSeparable E y) :
    IsReduced (A0 ⊗[E] L) := by
  let hy_int : IsIntegral E y := hy_sep.isIntegral
  letI : FiniteDimensional E L :=
    finiteDimensional_of_singleton_adjoin_eq_top (E := E) hy_int hgen
  let eSimple : AdjoinRoot (minpoly E y) ≃ₐ[E] L :=
    simple_generator_adjoinRoot_algEquiv (E := E) hy_int hgen
  have hReducedFracSimple :
      IsReduced (FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y)) := by
    -- The fraction-field stage is the `F[T]/(P)` paragraph from the source proof.
    exact
      isReduced_fractionRing_tensor_adjoinRoot_of_separable
        (E := E) (A0 := A0) (p := minpoly E y) hy_sep
  letI : IsReduced (FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y)) := hReducedFracSimple
  let eFrac :
      FractionRing A0 ⊗[E] AdjoinRoot (minpoly E y) ≃ₐ[FractionRing A0]
        FractionRing A0 ⊗[E] L :=
    Algebra.TensorProduct.congr
      (AlgEquiv.refl : FractionRing A0 ≃ₐ[FractionRing A0] FractionRing A0) eSimple
  have hReducedFrac :
      IsReduced (FractionRing A0 ⊗[E] L) := by
    -- Replace the simple extension by its `AdjoinRoot` model over the fraction field.
    exact isReduced_of_injective eFrac.symm.toRingHom eFrac.symm.injective
  let φ :
      A0 ⊗[E] L →+* FractionRing A0 ⊗[E] L :=
    Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom E A0 (FractionRing A0))
      (AlgHom.id E L)
  have hφ : Function.Injective φ := by
    -- Finite dimensionality of the right factor lets reducedness descend along tensoring.
    exact
      tensorProduct_map_injective_to_fractionRing_of_finiteDimensional_right
        (E := E) (A := A0) (L := L)
  letI : IsReduced (FractionRing A0 ⊗[E] L) := hReducedFrac
  -- Descend reducedness from the fraction-field tensor back to the original domain tensor.
  exact isReduced_of_injective φ hφ

/-- Helper for Lemma 10.43.6: once the field extension `K / k` is geometrically reduced, the
commutativity constraint on tensor products turns `Lemma_10_43_5` into reducedness of
`K ⊗[k] S`. -/
lemma isReduced_tensorProduct_of_geometricallyReduced_field
    [IsReduced S] [IsGeometricallyReduced k K] :
    IsReduced (K ⊗[k] S) := by
  let e : S ⊗[k] K ≃ₐ[k] K ⊗[k] S := Algebra.TensorProduct.comm k S K
  have hSK : IsReduced (S ⊗[k] K) := by
    -- Apply the geometric-reducedness tensor theorem with the reduced algebra on the left.
    exact isReduced_tensorProduct_of_geometricallyReduced (k := k) (R := S) (S := K)
  -- Transport reducedness across the tensor-product commutativity equivalence.
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Helper for Chap10 Lemma 10 43 6: a Stacks one-separable-generator witness generates the
extension over the transcendence-basis field by the singleton generator. -/
lemma adjoinSingleton_eq_top_of_oneSeparableGenerator
    {L : Type*} [Field L] [Algebra k L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L)
    {y : L} (hy : IsOneSeparableGeneratorOver x y) :
    IntermediateField.adjoin (IntermediateField.adjoin k (Set.range x)) ({y} : Set L) = ⊤ := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hAdjoinRestrict :
      (IntermediateField.adjoin F ({y} : Set L)).restrictScalars k = ⊤ := by
    -- Rewrite adjoining over `F` after restricting scalars back to the original `k`-field.
    calc
      (IntermediateField.adjoin F ({y} : Set L)).restrictScalars k =
          IntermediateField.adjoin k (Set.range x ∪ {y}) := by
            simpa [F] using
              restrictScalars_adjoin_singleton_eq_adjoin_union
                (k := k) (K := L) (S := Set.range x) y
      _ = ⊤ := hy.1
  apply top_unique
  intro z hzTop
  have hzRestrict :
      z ∈ ((IntermediateField.adjoin F ({y} : Set L)).restrictScalars k :
        IntermediateField k L) := by
    simpa [hAdjoinRestrict] using hzTop
  -- Membership in the restricted field is the same carrier membership over `F`.
  simpa [F] using hzRestrict

/-- Helper for Chap10 Lemma 10 43 6: the simple-generator tensor stage cancels to the algebraic
closure tensor product. -/
noncomputable abbrev simpleGeneratorTensorCancelBaseChange
    {F Ω L : Type*} [Field F] [Field Ω] [Field L]
    [Algebra k F] [Algebra k Ω] [Algebra k L] [Algebra F L] [IsScalarTower k F L] :
    ((F ⊗[k] Ω) ⊗[F] L) ≃+* Ω ⊗[k] L :=
  letI : Algebra F (F ⊗[k] Ω) := Algebra.TensorProduct.leftAlgebra
  (Algebra.TensorProduct.comm F (F ⊗[k] Ω) L).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange k F L L Ω).toRingEquiv.trans <|
      (Algebra.TensorProduct.comm k L Ω).toRingEquiv

/-- Helper for Chap10 Lemma 10 43 6: a transcendence basis plus one separable generator gives a
domain after tensoring its generated field with the algebraic closure. -/
lemma isDomain_adjoin_tensor_algebraicClosure_of_isTranscendenceBasis
    {L : Type*} [Field L] [Algebra k L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L) (hx : IsTranscendenceBasis k x) :
    IsDomain (IntermediateField.adjoin k (Set.range x) ⊗[k] AlgebraicClosure k) := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hDomainOmegaF : IsDomain (AlgebraicClosure k ⊗[k] F) := by
    -- The transcendence-basis stage is a rational-function field, so its tensor is a domain.
    exact isDomain_tensor_adjoin_of_isTranscendenceBasis
      (k := k) (κ := AlgebraicClosure k) (L := L) x hx
  let e : AlgebraicClosure k ⊗[k] F ≃+* F ⊗[k] AlgebraicClosure k :=
    (Algebra.TensorProduct.comm k (AlgebraicClosure k) F).toRingEquiv
  -- Commute tensor factors so the simple-extension lemma can use the `F`-algebra structure.
  exact e.isDomain_iff.mp hDomainOmegaF

/-- Helper for Chap10 Lemma 10 43 6: the one-generator separable extension gives a reduced
simple tensor stage over the transcendence-basis field. -/
lemma isReduced_simpleGeneratorTensorStage_of_oneSeparableGenerator
    {L : Type*} [Field L] [Algebra k L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L) (hx : IsTranscendenceBasis k x)
    {y : L} (hy : IsOneSeparableGeneratorOver x y) :
    IsReduced (((IntermediateField.adjoin k (Set.range x)) ⊗[k] AlgebraicClosure k) ⊗[
      IntermediateField.adjoin k (Set.range x)] L) := by
  let F : IntermediateField k L := IntermediateField.adjoin k (Set.range x)
  have hDomainFomega : IsDomain (F ⊗[k] AlgebraicClosure k) :=
    isDomain_adjoin_tensor_algebraicClosure_of_isTranscendenceBasis (k := k) x hx
  have hGenerator : IntermediateField.adjoin F ({y} : Set L) = ⊤ := by
    -- The primitive-generator witness over `k` becomes singleton generation over `F`.
    exact adjoinSingleton_eq_top_of_oneSeparableGenerator (k := k) x hy
  -- Pin the tensor-product ring structures explicitly; otherwise instance search expands the same
  -- tower repeatedly in this declaration.
  letI : Module F (F ⊗[k] AlgebraicClosure k) := TensorProduct.leftModule
  letI : Algebra F (F ⊗[k] AlgebraicClosure k) := Algebra.TensorProduct.leftAlgebra
  letI : CommRing (F ⊗[k] AlgebraicClosure k) :=
    TensorProduct.instCommRing (R := k) (A := F) (B := AlgebraicClosure k)
  letI : CommSemiring ((F ⊗[k] AlgebraicClosure k) ⊗[F] L) :=
    TensorProduct.instCommSemiring (R := F) (A := F ⊗[k] AlgebraicClosure k) (B := L)
  letI : Ring ((F ⊗[k] AlgebraicClosure k) ⊗[F] L) :=
    TensorProduct.instRing (R := F) (A := F ⊗[k] AlgebraicClosure k) (B := L)
  letI : CommRing ((F ⊗[k] AlgebraicClosure k) ⊗[F] L) :=
    TensorProduct.instCommRing (R := F) (A := F ⊗[k] AlgebraicClosure k) (B := L)
  letI : IsDomain (F ⊗[k] AlgebraicClosure k) := hDomainFomega
  -- The extension over `F` is simple separable, so tensoring the domain base with `L` is reduced.
  exact isReduced_tensor_simple_separable_extension_of_domain
    (E := F) (A0 := F ⊗[k] AlgebraicClosure k) (L := L) hGenerator hy.2

/-- Helper for Chap10 Lemma 10 43 6: reducedness transports from the simple-generator tensor
stage to the algebraic-closure tensor product. -/
lemma isReduced_of_simpleGeneratorTensorStage
    {F Ω L : Type*} [Field F] [Field Ω] [Field L]
    [Algebra k F] [Algebra k Ω] [Algebra k L] [Algebra F L] [IsScalarTower k F L]
    (h : IsReduced ((F ⊗[k] Ω) ⊗[F] L)) :
    IsReduced (Ω ⊗[k] L) := by
  -- Reintroduce the same pinned instances outside the previous proof block for the final
  -- comparison equivalence.
  letI : Module F (F ⊗[k] Ω) := TensorProduct.leftModule
  letI : Algebra F (F ⊗[k] Ω) := Algebra.TensorProduct.leftAlgebra
  letI : CommRing (F ⊗[k] Ω) := TensorProduct.instCommRing (R := k) (A := F) (B := Ω)
  letI : CommSemiring ((F ⊗[k] Ω) ⊗[F] L) :=
    TensorProduct.instCommSemiring (R := F) (A := F ⊗[k] Ω) (B := L)
  letI : Ring ((F ⊗[k] Ω) ⊗[F] L) :=
    TensorProduct.instRing (R := F) (A := F ⊗[k] Ω) (B := L)
  letI : CommRing ((F ⊗[k] Ω) ⊗[F] L) :=
    TensorProduct.instCommRing (R := F) (A := F ⊗[k] Ω) (B := L)
  let eFinal :=
    simpleGeneratorTensorCancelBaseChange (k := k) (F := F) (Ω := Ω) (L := L)
  -- Transport reducedness through tensor commutativity and base-change cancellation.
  constructor
  intro z hz
  have hzSource : IsNilpotent (eFinal.symm z) := hz.map eFinal.symm.toRingHom
  have hzero : eFinal.symm z = 0 := h.eq_zero (eFinal.symm z) hzSource
  apply eFinal.symm.injective
  simpa using hzero

/-- Helper for Chap10 Lemma 10 43 6: a transcendence basis plus one separable generator gives a
reduced algebraic-closure tensor product. -/
lemma isReduced_algebraicClosure_tensor_of_oneSeparableGenerator
    {L : Type*} [Field L] [Algebra k L]
    (x : Fin (Cardinal.toNat (Algebra.trdeg k L)) → L) (hx : IsTranscendenceBasis k x)
    {y : L} (hy : IsOneSeparableGeneratorOver x y) :
    IsReduced (AlgebraicClosure k ⊗[k] L) := by
  have hStage :=
    isReduced_simpleGeneratorTensorStage_of_oneSeparableGenerator (k := k) x hx hy
  -- The simple tensor stage cancels to the desired algebraic-closure tensor product.
  exact isReduced_of_simpleGeneratorTensorStage
    (k := k) (F := IntermediateField.adjoin k (Set.range x)) (Ω := AlgebraicClosure k)
    (L := L) hStage

/-- Helper for Lemma 10.43.6: an essentially finite type separably generated field extension is
geometrically reduced over the base field. -/
lemma isGeometricallyReduced_of_essFiniteType_isSeparablyGenerated
    {L : Type*} [Field L] [Algebra k L]
    [Algebra.EssFiniteType k L] [IsSeparablyGenerated k L] :
    IsGeometricallyReduced k L := by
  refine ⟨?_⟩
  obtain ⟨x, hx, y, hy⟩ :=
    exists_transcendence_basis_and_one_separable_generator (k := k) (K := L)
  -- The chosen transcendence basis and one separable generator give the required reduced tensor.
  exact isReduced_algebraicClosure_tensor_of_oneSeparableGenerator (k := k) x hx hy

/-- Helper for Lemma 10.43.6: every finitely generated intermediate field of a Stacks-separable
extension is geometrically reduced over the base field. -/
lemma fg_intermediateField_isGeometricallyReduced_of_isSeparableOver
    (L : IntermediateField k K) (hL : L.FG) [IsSeparableOver k K] :
    IsGeometricallyReduced k L := by
  letI : Algebra.EssFiniteType k L := (IntermediateField.essFiniteType_iff).2 hL
  have hSepOver : IsSeparableOver k L :=
    (inferInstance : IsSeparableOver k K).of_intermediateField L
  have hTopSepGen : IsSeparablyGenerated k (⊤ : IntermediateField k L) := by
    exact hSepOver.isSeparablyGenerated_of_fg ⊤ (IntermediateField.fg_top k L)
  have hSepGen : IsSeparablyGenerated k L := by
    simpa using hTopSepGen.of_algEquiv IntermediateField.topEquiv
  letI : IsSeparablyGenerated k L := hSepGen
  -- The remaining finite-stage input is exactly the planned source-faithful theorem above.
  exact isGeometricallyReduced_of_essFiniteType_isSeparablyGenerated (k := k) (L := L)

/-- Chap10 Lemma 10 43 6 (Tag 030U): if `S` is a reduced `k`-algebra and `K / k` is separable in the
sense of Definition 10.42.1(2), then the base change `K ⊗[k] S` is reduced. By
`Lemma_10_44_3`, this also applies to separably generated extensions. -/
@[stacks 030U]
theorem Lemma_10_43_6
    [IsReduced S]
    [IsSeparableOver k K] :
    IsReduced (K ⊗[k] S) := by
  -- Route correction: the tensor-commutation step is now separated from the actual blocker,
  -- namely the source-faithful proof that a Stacks-separable field extension is geometrically
  -- reduced.
  have hgeom : IsGeometricallyReduced k K := by
    -- First reduce geometric reducedness to finitely generated `k`-subalgebras of `K`.
    refine IsGeometricallyReduced.of_forall_fg ?_
    intro B hB
    rcases Subalgebra.fg_def.mp hB with ⟨t, htfin, htB⟩
    let L : IntermediateField k K := IntermediateField.adjoin k t
    have hL : L.FG := IntermediateField.fg_adjoin_of_finite htfin
    have hB_le : B ≤ L.toSubalgebra := by
      rw [← htB]
      exact IntermediateField.algebra_adjoin_le_adjoin k t
    let φ : B →ₐ[k] L :=
      { toFun := fun x ↦ ⟨x.1, hB_le x.2⟩
        map_zero' := rfl
        map_one' := rfl
        map_add' := fun _ _ ↦ rfl
        map_mul' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    have hφ : Function.Injective φ := by
      intro x y hxy
      have hvals : ((φ x : L) : K) = ((φ y : L) : K) := by
        exact congrArg (fun z : L ↦ (z : K)) hxy
      exact Subtype.ext hvals
    letI : IsGeometricallyReduced k L :=
      fg_intermediateField_isGeometricallyReduced_of_isSeparableOver
        (k := k) (K := K) L hL
    -- Then descend geometric reducedness from the finite generated intermediate field to `B`.
    exact IsGeometricallyReduced.of_injective φ hφ
  -- Once geometric reducedness is available, Lemma `10.43.5` gives the target reducedness.
  exact @isReduced_tensorProduct_of_geometricallyReduced_field
    k K S _ _ _ _ _ inferInstance hgeom

end

section

variable {k : Type u} {K : Type v}
variable [Field k] [Field K] [Algebra k K]

/-- A field extension that is separable in the sense of Definition `10.42.1 (2)` is geometrically
reduced over the base field. -/
theorem isGeometricallyReduced_of_isSeparableOver
    [IsSeparableOver k K] :
    IsGeometricallyReduced k K := by
  refine ⟨?_⟩
  let e : AlgebraicClosure k ⊗[k] K ≃ₐ[k] K ⊗[k] AlgebraicClosure k :=
    Algebra.TensorProduct.comm k (AlgebraicClosure k) K
  letI : IsReduced (K ⊗[k] AlgebraicClosure k) := Lemma_10_43_6
  exact isReduced_of_injective e.toRingHom e.injective

@[instance low] instance [IsSeparableOver k K] : IsGeometricallyReduced k K :=
  isGeometricallyReduced_of_isSeparableOver

end
