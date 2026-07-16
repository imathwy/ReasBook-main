import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_54_1
import stacks_proof.stacks_project.Chap10.Definition_10_47_4
import stacks_proof.stacks_project.Chap10.Lemma_10_47_10.Index

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CommRingCat
open scoped RatFunc TensorProduct
open Algebra.TensorProduct

namespace Algebra

universe u

section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

attribute [local instance] Polynomial.algebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Helper for Lemma 10.47.10: the source iterated base change
`((K(X) ⊗[k[X]] k(X)) ⊗[k(X)] Ω)` is the usual tensor `K(X) ⊗[k[X]] Ω` via the standard
`comm + congr + cancelBaseChange + comm` transport. -/
private noncomputable def ratFunc_iterated_baseChange_ringEquiv
    {Ω : Type u} [Field Ω] [Algebra k⟮X⟯ Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower (Polynomial k) k⟮X⟯ Ω] :
    (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) ⊗[k⟮X⟯] Ω ≃+*
      K⟮X⟯ ⊗[Polynomial k] Ω :=
  -- Proof comment: specialize the chapter-local base-change associativity equivalence to
  -- `k[X] → k(X)`, after first switching the default-left algebra spelling to the right spelling
  -- consumed by the generic base-change helper.
  let algLeft : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) := inferInstance
  let algRight : Algebra k⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra
  (tensor_ringEquiv_of_algebra_eq (R := k⟮X⟯)
    (A := K⟮X⟯ ⊗[Polynomial k] k⟮X⟯) (B := Ω) algLeft algRight
    (ratFunc_tensor_self_algebra_eq (k := k) (K := K))).trans
    (tensor_base_change_assoc_ringEquiv (R := Polynomial k) (R' := k⟮X⟯)
      (K' := K⟮X⟯) (B := Ω))

/-- Helper for Chap10 Lemma 10 47 10: the default-left `k(X)`-algebra collapse of
`K⟮X⟯ ⊗[k[X]] k⟮X⟯` is `k(X)`-linear. -/
private noncomputable def ratFunc_tensor_self_default_algEquiv :
    K⟮X⟯ ⊗[Polynomial k] k⟮X⟯ ≃ₐ[k⟮X⟯] K⟮X⟯ :=
  -- Proof comment: use the ring-level localization collapse together with its default-left
  -- compatibility with the `k(X)`-structure map.
  AlgEquiv.ofRingEquiv (f := ratFunc_tensor_ratFuncBase_ringEquiv (k := k) (K := K))
    (ratFunc_tensor_ratFuncBase_ringEquiv_commutes_left (k := k) (K := K))

/-- Helper for Lemma 10.47.10: after the source localization `k[X] → k(X)`, tensoring over the
larger base `k(X)` is just iterated base change. -/
private noncomputable def ratFunc_tensor_polynomialBase_to_ratFuncBase_ringEquiv
    {Ω : Type u} [Field Ω] [Algebra k⟮X⟯ Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower (Polynomial k) k⟮X⟯ Ω] :
    K⟮X⟯ ⊗[Polynomial k] Ω ≃+* K⟮X⟯ ⊗[k⟮X⟯] Ω :=
  -- Proof comment: first rewrite `K(X) ⊗[k[X]] Ω` as the iterated base change through `k(X)`;
  -- then collapse the first tensor factor `K(X) ⊗[k[X]] k(X)` back to `K(X)`.
  let eIter := (ratFunc_iterated_baseChange_ringEquiv (k := k) (K := K) (Ω := Ω)).symm
  eIter.trans
    (Algebra.TensorProduct.congr
      (ratFunc_tensor_self_default_algEquiv (k := k) (K := K))
      (AlgEquiv.refl : Ω ≃ₐ[k⟮X⟯] Ω)).toRingEquiv

/-- Helper for Lemma 10.47.10: any `k(X)`-algebra carries the induced `k[X]`-algebra structure
obtained by precomposing with `k[X] → k(X)`. -/
private noncomputable abbrev polynomial_base_of_ratFuncAlgebra
    {Ω : Type u} [CommRing Ω] [Algebra k⟮X⟯ Ω] :
    Algebra (Polynomial k) Ω :=
  ((algebraMap k⟮X⟯ Ω).comp (algebraMap (Polynomial k) k⟮X⟯)).toAlgebra

/-- Helper for Lemma 10.47.10: the induced `k[X]`-algebra on a `k(X)`-algebra forms the expected
scalar tower over `k[X]`. -/
private theorem polynomial_base_of_ratFuncAlgebra_isScalarTower
    {Ω : Type u} [CommRing Ω] [Algebra k⟮X⟯ Ω] :
    letI : Algebra (Polynomial k) Ω := polynomial_base_of_ratFuncAlgebra (k := k) (Ω := Ω)
    IsScalarTower (Polynomial k) k⟮X⟯ Ω := by
  letI : Algebra (Polynomial k) Ω := polynomial_base_of_ratFuncAlgebra (k := k) (Ω := Ω)
  -- Proof comment: the induced `k[X]`-algebra was defined by precomposing the existing
  -- `k(X) → Ω` map, so the tower identity is exactly the defining equality of algebra maps.
  exact IsScalarTower.of_algebraMap_eq' <| by
    simp [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.47.10: the induced `k[X]`-algebra on a `k(X)`-algebra is compatible with
the original `k`-algebra on the polynomial ring. -/
private theorem polynomial_base_of_ratFuncAlgebra_baseFieldTower
    {Ω : Type u} [CommRing Ω] [Algebra k⟮X⟯ Ω] :
    letI : Algebra k Ω :=
      ((algebraMap k⟮X⟯ Ω).comp (algebraMap k k⟮X⟯)).toAlgebra
    letI : Algebra (Polynomial k) Ω := polynomial_base_of_ratFuncAlgebra (k := k) (Ω := Ω)
    IsScalarTower k (Polynomial k) Ω := by
  letI : Algebra k Ω := ((algebraMap k⟮X⟯ Ω).comp (algebraMap k k⟮X⟯)).toAlgebra
  letI : Algebra (Polynomial k) Ω := polynomial_base_of_ratFuncAlgebra (k := k) (Ω := Ω)
  -- Proof comment: both `k → Ω` structure maps are the same composite
  -- `k → k[X] → k(X) → Ω`, so the base-field tower is again definitional.
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change algebraMap k⟮X⟯ Ω ((algebraMap k k⟮X⟯) x) =
    algebraMap k⟮X⟯ Ω ((algebraMap (Polynomial k) k⟮X⟯) ((algebraMap k (Polynomial k)) x))
  rw [show (algebraMap k k⟮X⟯) x = RatFunc.C x by rfl]
  rw [show (algebraMap k (Polynomial k)) x = Polynomial.C x by rfl]
  rw [RatFunc.algebraMap_C]

/-- Helper for Lemma 10.47.10: the canonical base-field map into `k(X)` sends `x` to the constant
rational function `C x`. -/
private theorem ratFunc_baseField_algebraMap_eq_C (x : k) :
    algebraMap k k⟮X⟯ x = RatFunc.C x := by
  rfl

/-- Helper for Lemma 10.47.10: a field extension `k' / k` induces the canonical `k[X]`-algebra
structure on `k'(X)` by sending coefficients through `k → k'`. -/
private noncomputable abbrev ratFunc_extension_polynomialAlgebra
    {k' : Type u} [Field k'] [Algebra k k'] :
    Algebra (Polynomial k) k'⟮X⟯ :=
  ((algebraMap (Polynomial k') k'⟮X⟯).comp
    (Polynomial.mapRingHom (algebraMap k k'))).toAlgebra

/-- Helper for Lemma 10.47.10: a field extension `k' / k` induces the canonical `k(X)`-algebra
structure on `k'(X)` by applying the coefficient map on numerators and denominators. -/
private noncomputable abbrev ratFunc_extension_ratFuncAlgebra
    {k' : Type u} [Field k'] [Algebra k k'] :
    Algebra k⟮X⟯ k'⟮X⟯ :=
  let coeffMap : Polynomial k →+* k'⟮X⟯ :=
    (algebraMap (Polynomial k') k'⟮X⟯).comp (Polynomial.mapRingHom (algebraMap k k'))
  let hcoeff :
      nonZeroDivisors (Polynomial k) ≤ (nonZeroDivisors k'⟮X⟯).comap coeffMap :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective coeffMap <|
      (RatFunc.algebraMap_injective (K := k')).comp <|
        Polynomial.map_injective (algebraMap k k') <| RingHom.injective (algebraMap k k')
  (RatFunc.liftRingHom coeffMap hcoeff).toAlgebra

/-- Helper for Lemma 10.47.10: the induced `k(X)`-algebra structure on `k'(X)` is the explicit
localization lift of the coefficient map `k[X] → k'(X)`. -/
private theorem ratFunc_extension_algebraMap_eq_liftRingHom
    {k' : Type u} [Field k'] [Algebra k k'] :
    let coeffMap : Polynomial k →+* k'⟮X⟯ :=
      (algebraMap (Polynomial k') k'⟮X⟯).comp (Polynomial.mapRingHom (algebraMap k k'))
    let hcoeff :
        nonZeroDivisors (Polynomial k) ≤
          (nonZeroDivisors k'⟮X⟯).comap coeffMap :=
      nonZeroDivisors_le_comap_nonZeroDivisors_of_injective coeffMap <|
        (RatFunc.algebraMap_injective (K := k')).comp <|
          Polynomial.map_injective (algebraMap k k') <|
            RingHom.injective (algebraMap k k')
    letI : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
    algebraMap k⟮X⟯ k'⟮X⟯ = RatFunc.liftRingHom coeffMap hcoeff := by
  let coeffMap : Polynomial k →+* k'⟮X⟯ :=
    (algebraMap (Polynomial k') k'⟮X⟯).comp (Polynomial.mapRingHom (algebraMap k k'))
  let hcoeff :
      nonZeroDivisors (Polynomial k) ≤ (nonZeroDivisors k'⟮X⟯).comap coeffMap :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective coeffMap <|
      (RatFunc.algebraMap_injective (K := k')).comp <|
        Polynomial.map_injective (algebraMap k k') <| RingHom.injective (algebraMap k k')
  letI : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
  -- Proof comment: the algebra structure was defined from exactly this `liftRingHom`, so its
  -- bundled structure map is definitionally that lift.
  rfl

/-- Helper for Lemma 10.47.10: the canonical map `k(X) → k'(X)` extends the coefficient map
`k[X] → k'(X)`. -/
private theorem ratFunc_extension_ratFuncAlgebra_comp_eq
    {k' : Type u} [Field k'] [Algebra k k'] :
    letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
    letI : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
    (algebraMap k⟮X⟯ k'⟮X⟯).comp (algebraMap (Polynomial k) k⟮X⟯) =
      algebraMap (Polynomial k) k'⟮X⟯ := by
  let coeffMap : Polynomial k →+* k'⟮X⟯ :=
    (algebraMap (Polynomial k') k'⟮X⟯).comp (Polynomial.mapRingHom (algebraMap k k'))
  let hcoeff :
      nonZeroDivisors (Polynomial k) ≤ (nonZeroDivisors k'⟮X⟯).comap coeffMap :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective coeffMap <|
      (RatFunc.algebraMap_injective (K := k')).comp <|
        Polynomial.map_injective (algebraMap k k') <| RingHom.injective (algebraMap k k')
  letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
  letI : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
  -- Proof comment: after rewriting the `k(X)`-structure map as the explicit localization lift,
  -- the claim is exactly `RatFunc.liftRingHom_comp_algebraMap`.
  rw [ratFunc_extension_algebraMap_eq_liftRingHom (k := k) (k' := k')]
  simpa [coeffMap, ratFunc_extension_polynomialAlgebra, RingHom.algebraMap_toAlgebra] using
    (RatFunc.liftRingHom_comp_algebraMap coeffMap hcoeff)

/-- Helper for Lemma 10.47.10: the canonical coefficient map `k[X] → k'(X)` extends the base
field map `k → k'(X)` through constants. -/
private theorem ratFunc_extension_polynomialAlgebra_baseField_comp_eq
    {k' : Type u} [Field k'] [Algebra k k'] :
    letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
    (algebraMap (Polynomial k) k'⟮X⟯).comp (algebraMap k (Polynomial k)) =
      algebraMap k k'⟮X⟯ := by
  letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
  -- Proof comment: both composites send `x : k` to the same constant rational function in
  -- `k'(X)` after first applying the coefficient map `k → k'`.
  ext x
  change algebraMap (Polynomial k') k'⟮X⟯
      ((Polynomial.mapRingHom (algebraMap k k')) ((algebraMap k (Polynomial k)) x)) =
    algebraMap k k'⟮X⟯ x
  rw [show (algebraMap k (Polynomial k)) x = Polynomial.C x by rfl]
  change algebraMap (Polynomial k') k'⟮X⟯ (((Polynomial.C x).map (algebraMap k k'))) =
    algebraMap k k'⟮X⟯ x
  rw [Polynomial.map_C, RatFunc.algebraMap_C]
  rfl

/-- Helper for Lemma 10.47.10: the explicit `k[X]`-algebra structure on `k'(X)` is compatible
with the ambient `k`-algebra structure coming from the coefficient field extension `k → k'`. -/
private theorem ratFunc_extension_polynomial_baseField_isScalarTower
    {k' : Type u} [Field k'] [Algebra k k'] :
    letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
    IsScalarTower k (Polynomial k) k'⟮X⟯ := by
  letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
  -- Proof comment: this scalar tower is the standard coefficient-extension tower on rational
  -- function fields, so instance search closes it once the intended `k[X]`-algebra is fixed.
  infer_instance

/-- Helper for Lemma 10.47.10: the explicit `k[X]`-algebra structure on `k'(X)` is the ambient
one chosen by literal tensor notation. -/
private theorem ratFunc_extension_polynomialAlgebra_eq_default
    {k' : Type u} [Field k'] [Algebra k k'] :
    ratFunc_extension_polynomialAlgebra (k := k) (k' := k') =
      (inferInstance : Algebra (Polynomial k) k'⟮X⟯) := by
  apply Algebra.algebra_ext
  intro q
  -- Proof comment: both algebra structures are determined by the same coefficient map
  -- `k[X] → k'(X)`.
  simpa [ratFunc_extension_polynomialAlgebra, RingHom.algebraMap_toAlgebra] using
    (IsScalarTower.algebraMap_apply (Polynomial k) (Polynomial k') k'⟮X⟯ q).symm

/-- Helper for Lemma 10.47.10: after transporting the explicit polynomial coefficient map to the
ambient one, `k'(X)` carries the expected default scalar tower over `k[X]`. -/
private theorem ratFunc_extension_polynomial_default_isScalarTower
    {k' : Type u} [Field k'] [Algebra k k'] :
    IsScalarTower k (Polynomial k) k'⟮X⟯ := by
  -- Proof comment: both composites `k → k[X] → k'(X)` send `x` to the same constant rational
  -- function, so the default coefficient algebra already forms the expected base-field tower.
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  symm
  change algebraMap (Polynomial k') k'⟮X⟯
      (((algebraMap k (Polynomial k)) x).map (algebraMap k k')) =
    algebraMap k k'⟮X⟯ x
  rw [show (algebraMap k (Polynomial k)) x = Polynomial.C x by rfl]
  rw [Polynomial.map_C, RatFunc.algebraMap_C]
  rfl

/-- Helper for Lemma 10.47.10: after transporting the explicit localization lift to the ambient
one, `k'(X)` carries the expected default scalar tower over `k[X] → k(X)`. -/
private theorem ratFunc_extension_defaultLift_ringHom_eq
    {k' : Type u} [Field k'] [Algebra k k'] :
    let defaultRat : Algebra k⟮X⟯ k'⟮X⟯ := RatFunc.liftAlgebra k k'⟮X⟯
    @algebraMap k⟮X⟯ k'⟮X⟯ _ _ (ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')) =
      @algebraMap k⟮X⟯ k'⟮X⟯ _ _ defaultRat := by
  let defaultRat : Algebra k⟮X⟯ k'⟮X⟯ := RatFunc.liftAlgebra k k'⟮X⟯
  let explicitRat : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
  have hExplicitComp :
      (@algebraMap k⟮X⟯ k'⟮X⟯ _ _ explicitRat).comp (algebraMap (Polynomial k) k⟮X⟯) =
        algebraMap (Polynomial k) k'⟮X⟯ := by
    letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
    letI : Algebra k⟮X⟯ k'⟮X⟯ := explicitRat
    -- Proof comment: the explicit algebra was defined as the localization lift of the coefficient
    -- map, so its restriction to `k[X]` is exactly that coefficient map.
    exact ratFunc_extension_ratFuncAlgebra_comp_eq (k := k) (k' := k')
  have hDefaultComp :
      (@algebraMap k⟮X⟯ k'⟮X⟯ _ _ defaultRat).comp (algebraMap (Polynomial k) k⟮X⟯) =
        algebraMap (Polynomial k) k'⟮X⟯ := by
    -- Proof comment: the ambient `RatFunc` lift is the owner fraction-field algebra, so its
    -- restriction to `k[X]` is the standard polynomial coefficient map.
    refine RingHom.ext fun q ↦ ?_
    change @algebraMap k⟮X⟯ k'⟮X⟯ _ _ defaultRat ((algebraMap (Polynomial k) k⟮X⟯) q) =
      algebraMap (Polynomial k) k'⟮X⟯ q
    change (IsFractionRing.lift (FaithfulSMul.algebraMap_injective (Polynomial k) k'⟮X⟯))
        ((algebraMap (Polynomial k) k⟮X⟯) q) = algebraMap (Polynomial k) k'⟮X⟯ q
    simpa using
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective (Polynomial k) k'⟮X⟯) q)
  -- Proof comment: localization extensionality reduces equality of maps out of `k(X)` to equality
  -- on the polynomial subring `k[X]`.
  apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
  calc
    (@algebraMap k⟮X⟯ k'⟮X⟯ _ _ explicitRat).comp (algebraMap (Polynomial k) k⟮X⟯) =
      algebraMap (Polynomial k) k'⟮X⟯ := hExplicitComp
    _ =
      (@algebraMap k⟮X⟯ k'⟮X⟯ _ _ defaultRat).comp (algebraMap (Polynomial k) k⟮X⟯) :=
        hDefaultComp.symm

/-- Helper for Lemma 10.47.10: after transporting the explicit localization lift to the ambient
one, `k'(X)` carries the expected default scalar tower over `k[X] → k(X)`. -/
private theorem ratFunc_extension_ratFuncAlgebra_eq_defaultLift
    {k' : Type u} [Field k'] [Algebra k k'] :
    ratFunc_extension_ratFuncAlgebra (k := k) (k' := k') =
      (inferInstance : Algebra k⟮X⟯ k'⟮X⟯) := by
  -- Proof comment: `Algebra` structures are determined by their structure maps, so the previously
  -- proved ring-hom equality upgrades directly to equality of bundled algebras.
  apply Algebra.algebra_ext
  intro x
  exact RingHom.congr_fun
    (ratFunc_extension_defaultLift_ringHom_eq (k := k) (k' := k')) x

/-- Helper for Lemma 10.47.10: after transporting the explicit localization lift to the ambient
one, `k'(X)` carries the expected default scalar tower over `k[X] → k(X)`. -/
private theorem ratFunc_extension_ratFunc_default_isScalarTower
    {k' : Type u} [Field k'] [Algebra k k'] :
    IsScalarTower (Polynomial k) k⟮X⟯ k'⟮X⟯ := by
  -- Proof comment: the literal `RatFunc` actions are induced from the fraction-ring actions, so
  -- the scalar-tower associativity identity can be checked after applying `toFractionRing`.
  refine ⟨fun x y z => ?_⟩
  apply RatFunc.toFractionRing_injective
  simp [RatFunc.toFractionRing_smul, smul_assoc]

/-- Helper for Lemma 10.47.10: the explicit `k(X)`-algebra structure on `k'(X)` forms the
expected scalar tower over the explicit `k[X]`-algebra structure. -/
private theorem ratFunc_extension_ratFuncAlgebra_isScalarTower
    {k' : Type u} [Field k'] [Algebra k k'] :
    letI : Algebra (Polynomial k) k'⟮X⟯ := ratFunc_extension_polynomialAlgebra (k := k) (k' := k')
    letI : Algebra k⟮X⟯ k'⟮X⟯ := ratFunc_extension_ratFuncAlgebra (k := k) (k' := k')
    IsScalarTower (Polynomial k) k⟮X⟯ k'⟮X⟯ := by
  -- Proof comment: even with the explicit algebra packages fixed, the theorem target only asks
  -- for the literal `RatFunc` scalar actions, so the same fraction-ring associativity check
  -- proves the required tower directly.
  refine ⟨fun x y z => ?_⟩
  apply RatFunc.toFractionRing_injective
  simp [RatFunc.toFractionRing_smul, smul_assoc]
/-- Helper for Lemma 10.47.10: for any compatible `k`- and `k[X]`-algebra structure on `Ω`,
the polynomial pushout square cancels the `k[X]`-base change. -/
private noncomputable def polynomial_baseChange_ringEquiv_over_ratFuncBase
    {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower k (Polynomial k) Ω] :
    Polynomial K ⊗[Polynomial k] Ω ≃+* K ⊗[k] Ω := by
  -- Proof comment: `Polynomial K` is the pushout of `k → K` and `k → k[X]`, so
  -- `cancelBaseChangeAlg` rewrites the polynomial tensor directly as the field tensor.
  exact (Algebra.IsPushout.cancelBaseChangeAlg k K (Polynomial k) (Polynomial K) Ω).toRingEquiv

/-- Helper for Lemma 10.47.10: the polynomial-stage base change over `k[X]` has irreducible prime
spectrum exactly when the corresponding field-stage base change over `k` does. -/
private theorem irreducibleSpace_primeSpectrum_polynomial_baseChange_iff
    {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra (Polynomial k) Ω]
    [IsScalarTower k (Polynomial k) Ω] :
    IrreducibleSpace (PrimeSpectrum (Polynomial K ⊗[Polynomial k] Ω)) ↔
      IrreducibleSpace (PrimeSpectrum (K ⊗[k] Ω)) := by
  -- Proof comment: this is just transport across the canonical polynomial pushout equivalence.
  let e :=
    polynomial_baseChange_ringEquiv_over_ratFuncBase (k := k) (K := K) (Ω := Ω)
  let eSpec : PrimeSpectrum (Polynomial K ⊗[Polynomial k] Ω) ≃ₜ PrimeSpectrum (K ⊗[k] Ω) :=
    PrimeSpectrum.homeomorphOfRingEquiv e
  exact eSpec.irreducibleSpace_iff

/-- Helper for Lemma 10.47.10: the omitted constants map from `K ⊗[k] k'` into the rational
function-field tensor product is the standard comparison chain through the polynomial stage. -/
private noncomputable def constants_to_ratFuncTensor
    {k' : Type u} [Field k'] [Algebra k k'] :
    K ⊗[k] k' →+* K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯ := by
  letI : IsScalarTower k k' k'⟮X⟯ :=
    by
      -- Proof comment: both scalar actions on `k'(X)` are by constant rational functions, so the
      -- tower law is checked after applying `toFractionRing`.
      refine ⟨fun x y z => ?_⟩
      apply RatFunc.toFractionRing_injective
      simp [RatFunc.toFractionRing_smul, smul_assoc]
  letI : IsScalarTower k (Polynomial k) k'⟮X⟯ :=
    ratFunc_extension_polynomial_default_isScalarTower (k := k) (k' := k')
  letI : IsScalarTower (Polynomial k) k⟮X⟯ k'⟮X⟯ :=
    ratFunc_extension_ratFunc_default_isScalarTower (k := k) (k' := k')
  letI : Algebra k'⟮X⟯ (Polynomial K ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := k'⟮X⟯)
  letI : Algebra k'⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := k'⟮X⟯)
  let step₁ :
      K ⊗[k] k' →+* K ⊗[k] k'⟮X⟯ :=
    (Algebra.TensorProduct.map (AlgHom.id k K)
      (IsScalarTower.toAlgHom k k' k'⟮X⟯)).toRingHom
  let step₂ :
      K ⊗[k] k'⟮X⟯ →+* Polynomial K ⊗[Polynomial k] k'⟮X⟯ :=
    ((polynomial_baseChange_ringEquiv_over_ratFuncBase
      (k := k) (K := K) (Ω := k'⟮X⟯)).symm).toRingHom
  let step₃ :
      Polynomial K ⊗[Polynomial k] k'⟮X⟯ →+* K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯ :=
    (tensor_right_map (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := k'⟮X⟯)).toRingHom
  let step₄ :
      K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯ →+* K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯ :=
    (ratFunc_tensor_polynomialBase_to_ratFuncBase_ringEquiv
      (k := k) (K := K) (Ω := k'⟮X⟯)).toRingHom
  -- Proof comment: this is exactly the omitted textbook map: first extend constants to `k'(X)`,
  -- then pass through the polynomial pushout, localize the `K[X]` factor to `K(X)`, and finally
  -- rewrite the base from `k[X]` to `k(X)`.
  exact step₄.comp <| step₃.comp <| step₂.comp step₁

/-- Helper for Lemma 10.47.10: after rewriting the polynomial-stage tensor as `K ⊗[k] Ω`, the
constants map coming from a field extension `k' / k` stays injective. -/
private theorem tensor_constants_to_polynomial_base_injective
    {k' Ω : Type u} [Field k'] [Field Ω] [Algebra k k'] [Algebra k Ω] [Algebra k' Ω]
    [IsScalarTower k k' Ω] [Algebra (Polynomial k) Ω] [IsScalarTower k (Polynomial k) Ω] :
    Function.Injective
      ((((polynomial_baseChange_ringEquiv_over_ratFuncBase
          (k := k) (K := K) (Ω := Ω)).symm).toRingHom).comp
        ((Algebra.TensorProduct.map (AlgHom.id k K)
          (IsScalarTower.toAlgHom k k' Ω)).toRingHom :
          K ⊗[k] k' →+* K ⊗[k] Ω)) := by
  -- Proof comment: tensoring by a field preserves injectivity on the right factor, and the
  -- polynomial pushout equivalence just transports that injective map to the polynomial stage.
  have hmap :
      Function.Injective
        (Algebra.TensorProduct.map (AlgHom.id k K) (IsScalarTower.toAlgHom k k' Ω) :
          K ⊗[k] k' →ₐ[k] K ⊗[k] Ω) := by
    simpa using TensorProduct.map_injective_of_flat_flat
      (AlgHom.id k K).toLinearMap (IsScalarTower.toAlgHom k k' Ω).toLinearMap
      Function.injective_id (RingHom.injective (algebraMap k' Ω))
  exact
    ((polynomial_baseChange_ringEquiv_over_ratFuncBase
      (k := k) (K := K) (Ω := Ω)).symm.injective).comp hmap

/-- Helper for Chap10 Lemma 10 47 10: localizing the polynomial factor
`Polynomial K → K⟮X⟯` remains injective after right tensoring over `Polynomial k`. -/
private theorem tensorRightMap_ratFuncPolynomial_injective
    {k' : Type u} [Field k'] [Algebra k k'] :
    Function.Injective
      (tensor_right_map (R := Polynomial k) (S := K⟮X⟯)
        (Q := Polynomial K) (T := k'⟮X⟯)) := by
  letI : Algebra k'⟮X⟯ (Polynomial K ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := k'⟮X⟯)
  letI : Algebra k'⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := k'⟮X⟯)
  -- Proof comment: `tensor_right_map` is a tensor map conjugated by tensor-factor
  -- commutativity, so it is injective because `Polynomial K → K(X)` is injective.
  have hPolynomial :
      Function.Injective
        (IsScalarTower.toAlgHom (Polynomial k) (Polynomial K) K⟮X⟯) :=
    RatFunc.algebraMap_injective (K := K)
  have hTensor :
      Function.Injective
        (Algebra.TensorProduct.map
          (AlgHom.id (Polynomial k) k'⟮X⟯)
          (IsScalarTower.toAlgHom (Polynomial k) (Polynomial K) K⟮X⟯)) := by
    simpa using
      TensorProduct.map_injective_of_flat_flat
        (AlgHom.id (Polynomial k) k'⟮X⟯).toLinearMap
        (IsScalarTower.toAlgHom (Polynomial k) (Polynomial K) K⟮X⟯).toLinearMap
        (fun _ _ h ↦ h)
        hPolynomial
  simpa [tensor_right_map] using
    (Algebra.TensorProduct.commRight (Polynomial k) k'⟮X⟯ K⟮X⟯).injective.comp <|
      hTensor.comp
        (Algebra.TensorProduct.commRight (Polynomial k) k'⟮X⟯ (Polynomial K)).symm.injective

/-- Helper for Lemma 10.47.10: after passing from the polynomial-stage tensor to the rational
function-stage tensor, the constants map remains injective. -/
private theorem tensor_constants_to_ratFuncTensor_injective
    {k' : Type u} [Field k'] [Algebra k k'] :
    Function.Injective (constants_to_ratFuncTensor (k := k) (K := K) (k' := k')) :=
by
  letI : IsScalarTower k k' k'⟮X⟯ := by
    refine ⟨fun x y z => ?_⟩
    apply RatFunc.toFractionRing_injective
    simp [RatFunc.toFractionRing_smul, smul_assoc]
  letI : IsScalarTower k (Polynomial k) k'⟮X⟯ :=
    ratFunc_extension_polynomial_default_isScalarTower (k := k) (k' := k')
  letI : IsScalarTower (Polynomial k) k⟮X⟯ k'⟮X⟯ :=
    ratFunc_extension_ratFunc_default_isScalarTower (k := k) (k' := k')
  letI : Algebra k'⟮X⟯ (Polynomial K ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := k'⟮X⟯)
  letI : Algebra k'⟮X⟯ (K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯) :=
    Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := k'⟮X⟯)
  let step₁ :
      K ⊗[k] k' →+* K ⊗[k] k'⟮X⟯ :=
    (Algebra.TensorProduct.map (AlgHom.id k K)
      (IsScalarTower.toAlgHom k k' k'⟮X⟯)).toRingHom
  let step₂ :
      K ⊗[k] k'⟮X⟯ →+* Polynomial K ⊗[Polynomial k] k'⟮X⟯ :=
    ((polynomial_baseChange_ringEquiv_over_ratFuncBase
      (k := k) (K := K) (Ω := k'⟮X⟯)).symm).toRingHom
  let step₃ :
      Polynomial K ⊗[Polynomial k] k'⟮X⟯ →+* K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯ :=
    (tensor_right_map (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K)
      (T := k'⟮X⟯)).toRingHom
  let step₄ :
      K⟮X⟯ ⊗[Polynomial k] k'⟮X⟯ →+* K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯ :=
    (ratFunc_tensor_polynomialBase_to_ratFuncBase_ringEquiv
      (k := k) (K := K) (Ω := k'⟮X⟯)).toRingHom
  have h₁₂ : Function.Injective (step₂.comp step₁) := by
    -- Proof comment: the first two steps are exactly the already-proved polynomial-stage
    -- constants comparison.
    simpa [step₁, step₂] using
      tensor_constants_to_polynomial_base_injective (k := k) (K := K) (k' := k') (Ω := k'⟮X⟯)
  have h₃ : Function.Injective step₃ := by
    -- Proof comment: the third step is the cached right-tensor localization map.
    simpa [step₃] using
      tensorRightMap_ratFuncPolynomial_injective (k := k) (K := K) (k' := k')
  have h₄ : Function.Injective step₄ := by
    -- Proof comment: the final step is a ring equivalence rewriting the base from `k[X]` to
    -- `k(X)`.
    simpa [step₄] using
      (ratFunc_tensor_polynomialBase_to_ratFuncBase_ringEquiv
        (k := k) (K := K) (Ω := k'⟮X⟯)).injective
  -- Proof comment: unfold the omitted constants map and compose the injectivity of its four
  -- named stages.
  simpa [constants_to_ratFuncTensor, step₁, step₂, step₃, step₄] using h₄.comp (h₃.comp h₁₂)

-- Proof sketch: for the forward implication, identify `K(t)` with the localization of
-- `K ⊗[k] k(t)` at the nonzero polynomials and use stability of irreducibility under
-- localization. For the reverse implication, for any field extension `k' / k`, compare
-- `K ⊗[k] k'` with its localization `K(t) ⊗[k(t)] k'(t)`; injectivity together with the
-- minimal-prime comparison lemmas recovers irreducibility before localization.
/-- Chap10 Lemma 10 47 10: a field extension `K / k` is geometrically irreducible if and only if the
induced extension on one-variable rational function fields `K(t) / k(t)` is geometrically
irreducible. -/
@[stacks 0G31]
theorem isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) := by
  rw [geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange,
    geometricallyIrreducible_iff_irreducibleSpace_primeSpectrum_baseChange]
  constructor
  · intro h Ω _ _
    letI : Algebra k Ω := ((algebraMap k⟮X⟯ Ω).comp (algebraMap k k⟮X⟯)).toAlgebra
    letI : Algebra (Polynomial k) Ω := polynomial_base_of_ratFuncAlgebra (k := k) (Ω := Ω)
    letI : IsScalarTower (Polynomial k) k⟮X⟯ Ω :=
      polynomial_base_of_ratFuncAlgebra_isScalarTower (k := k) (Ω := Ω)
    letI : IsScalarTower k (Polynomial k) Ω :=
      polynomial_base_of_ratFuncAlgebra_baseFieldTower (k := k) (Ω := Ω)
    have hPolyBase : IrreducibleSpace (PrimeSpectrum (Polynomial K ⊗[Polynomial k] Ω)) := by
      -- Proof comment: geometric irreducibility over `k` identifies the polynomial-stage base
      -- change with the field-stage base change `K ⊗[k] Ω`.
      exact (irreducibleSpace_primeSpectrum_polynomial_baseChange_iff
        (k := k) (K := K) (Ω := Ω)).2 (h Ω)
    let eCompare :=
      ratFunc_tensor_polynomialBase_to_ratFuncBase_ringEquiv (k := k) (K := K) (Ω := Ω)
    letI : Nontrivial (K⟮X⟯ ⊗[k⟮X⟯] Ω) := inferInstance
    have hNontrivialRatBase : Nontrivial (K⟮X⟯ ⊗[Polynomial k] Ω) :=
      eCompare.symm.injective.nontrivial
    letI : Nontrivial (K⟮X⟯ ⊗[Polynomial k] Ω) := hNontrivialRatBase
    have hRatBase : IrreducibleSpace (PrimeSpectrum (K⟮X⟯ ⊗[Polynomial k] Ω)) := by
      -- Proof comment: after localizing the polynomial tensor at the nonzero polynomials of
      -- `K[X]`, irreducibility survives because the localization is nontrivial.
      letI : Algebra Ω (Polynomial K ⊗[Polynomial k] Ω) :=
        Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := Polynomial K) (B := Ω)
      letI : Algebra Ω (K⟮X⟯ ⊗[Polynomial k] Ω) :=
        Algebra.TensorProduct.rightAlgebra (R := Polynomial k) (A := K⟮X⟯) (B := Ω)
      let tensorQS : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) :=
        (tensor_right_map (R := Polynomial k) (S := K⟮X⟯) (Q := Polynomial K) (T := Ω)).toAlgebra
      letI : Algebra (Polynomial K ⊗[Polynomial k] Ω) (K⟮X⟯ ⊗[Polynomial k] Ω) := tensorQS
      letI :
          IsLocalization
            (Algebra.algebraMapSubmonoid (Polynomial K ⊗[Polynomial k] Ω)
              (nonZeroDivisors (Polynomial K)))
            (K⟮X⟯ ⊗[Polynomial k] Ω) :=
        ratFunc_tensor_over_polynomial_isLocalization (k := k) (K := K) (Ω := Ω)
      exact irreducibleSpace_primeSpectrum_of_isLocalization
        (Algebra.algebraMapSubmonoid (Polynomial K ⊗[Polynomial k] Ω)
          (nonZeroDivisors (Polynomial K))) hPolyBase
    -- Proof comment: the final comparison equivalence rewrites the polynomial-base tensor as the
    -- literal rational-function-base tensor appearing in geometric irreducibility over `k(X)`.
    exact (PrimeSpectrum.homeomorphOfRingEquiv eCompare).irreducibleSpace_iff.1 hRatBase
  · intro h k' _ _
    have hRat :
        IrreducibleSpace (PrimeSpectrum (K⟮X⟯ ⊗[k⟮X⟯] k'⟮X⟯)) := h k'⟮X⟯
    -- Proof comment: the omitted constants map is injective, so irreducibility descends from the
    -- rational-function tensor back to the original field tensor.
    exact irreducibleSpace_primeSpectrum_of_injective
      (constants_to_ratFuncTensor (k := k) (K := K) (k' := k'))
      (tensor_constants_to_ratFuncTensor_injective (k := k) (K := K) (k' := k')) hRat

/-- Compatibility alias for Chap10 Lemma 10 47 10: the rational-function-field criterion for
geometric irreducibility. -/
abbrev Lemma_10_47_10 :
    GeometricallyIrreducible (Spec.map (ofHom (algebraMap k K))) ↔
      GeometricallyIrreducible (Spec.map (ofHom (algebraMap k⟮X⟯ K⟮X⟯))) :=
  isGeometricallyIrreducibleOver_iff_ratFuncExtension_isGeometricallyIrreducible

end

end Algebra
