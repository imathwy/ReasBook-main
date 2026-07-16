import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_135_5
import stacks_proof.stacks_project.Chap10.Lemma_10_68_5
import stacks_proof.stacks_project.Chap10.Lemma_10_112_7
import stacks_proof.stacks_project.Chap10.Lemma_10_135_8

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.TensorProduct
open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u v w

section

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {S : Type w} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

local notation "S_K" => K ⊗[k] S
local notation "iSK" => (((includeRight : S →ₐ[k] S_K) : S →+* S_K))

/-- Helper for Chap10 Lemma 10 135 10: coefficient extension gives the local algebra structure on
polynomial rings over a field extension. -/
noncomputable local instance mvPolynomialFieldExtensionAlgebra_local {n : ℕ} :
    Algebra (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
  (MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toAlgebra

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the prime of a base-changed polynomial presentation
contracts to the prime of the original presentation over the contracted point. -/
private lemma baseChangePresentation_prime_comap
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    PrimeSpectrum.comap β.toRingHom (PolynomialPresentationAtPrime.prime πK qK) =
      PolynomialPresentationAtPrime.prime π q := by
  intro q πK β
  -- Proof comment: first identify the base-changed presentation after restricting scalars with
  -- the original presentation followed by the right tensor inclusion.
  have hcompAlg :
      (AlgHom.restrictScalars k πK).comp β =
        (includeRight : S →ₐ[k] S_K).comp π := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [πK, β]
  have hcompRing :
      πK.toRingHom.comp β.toRingHom =
        ((includeRight : S →ₐ[k] S_K).comp π).toRingHom := by
    simpa using congrArg AlgHom.toRingHom hcompAlg
  -- Proof comment: functoriality of `Spec` turns the algebra-map square into the desired
  -- equality of contracted presentation primes.
  rw [PolynomialPresentationAtPrime.prime, PolynomialPresentationAtPrime.prime]
  rw [← PrimeSpectrum.comap_comp_apply]
  rw [hcompRing]
  have hincludeRing :
      ((includeRight : S →ₐ[k] S_K).comp π).toRingHom =
        (((includeRight : S →ₐ[k] S_K) : S →+* S_K).comp π.toRingHom) := rfl
  rw [hincludeRing]
  rw [PrimeSpectrum.comap_comp_apply]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the base-changed presentation prime contracts to a named
downstairs point once the tensor-prime contraction is identified. -/
private lemma baseChangePresentation_prime_comap_of_eq
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K)
    (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    PrimeSpectrum.comap β.toRingHom yK = y := by
  intro πK y yK β
  -- Proof comment: first use the functorial base-change square, then replace the contraction by
  -- the named downstairs point.
  calc
    PrimeSpectrum.comap β.toRingHom yK =
        PolynomialPresentationAtPrime.prime π (PrimeSpectrum.comap iSK xK) := by
      simpa [πK, yK, β] using baseChangePresentation_prime_comap (K := K) π xK
    _ = y := by
      rw [hxK]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the `aeval` presentation over `K` is the tensor product
of the original presentation after the standard polynomial/tensor equivalence. -/
private lemma tensorBaseChangePolynomialAlgHom_restrictScalars_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) :
    (AlgHom.restrictScalars k
      (MvPolynomial.aeval (R := K) (S₁ := S_K)
        fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
          MvPolynomial (Fin n) K →ₐ[K] S_K)) =
      (Algebra.TensorProduct.map (AlgHom.id k K) π).comp
        ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) := by
  -- Proof comment: compare the two `k`-algebra maps on coefficients and on polynomial variables.
  apply MvPolynomial.algHom_ext'
  · ext c
    simp [MvPolynomial.algebraTensorAlgEquiv]
  · intro i
    simp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: a surjective polynomial presentation remains surjective
after extending coefficients to the field extension. -/
private lemma tensorBaseChangePolynomialAlgHom_surjective_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π) :
    Function.Surjective
      (MvPolynomial.aeval (R := K) (S₁ := S_K)
        fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i) :
          MvPolynomial (Fin n) K →ₐ[K] S_K) := by
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  have hmap :
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k K) π :
        K ⊗[k] MvPolynomial (Fin n) k →ₐ[k] S_K) := by
    -- Proof comment: tensor the original surjection with the identity map of `K`.
    exact Algebra.TensorProduct.map_surjective (f := AlgHom.id k K) (g := π)
      Function.surjective_id hπ
  have hraw :
      Function.Surjective
        ((Algebra.TensorProduct.map (AlgHom.id k K) π).comp
          ((MvPolynomial.algebraTensorAlgEquiv k K).symm.toAlgHom.restrictScalars k) :
            MvPolynomial (Fin n) K →ₐ[k] S_K) := by
    -- Proof comment: precompose with the polynomial/tensor equivalence to move to the standard
    -- polynomial ring over `K`.
    exact hmap.comp (MvPolynomial.algebraTensorAlgEquiv k K).symm.surjective
  have hrestricted :
      Function.Surjective
        ((AlgHom.restrictScalars k πK) : MvPolynomial (Fin n) K →ₐ[k] S_K) := by
    -- Proof comment: identify the transported tensor presentation with the `aeval` presentation
    -- on polynomial generators.
    simpa [πK, tensorBaseChangePolynomialAlgHom_restrictScalars_local (K := K) π] using hraw
  simpa [πK] using hrestricted

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the kernel of the base-changed presentation is the
extension of the original kernel along coefficient extension. -/
private lemma tensorBaseChangePolynomialAlgHom_ker_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    RingHom.ker πK.toRingHom = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
  intro πK β
  let e : K ⊗[k] MvPolynomial (Fin n) k ≃ₐ[K] MvPolynomial (Fin n) K :=
    MvPolynomial.algebraTensorAlgEquiv k K
  let raw : K ⊗[k] MvPolynomial (Fin n) k →ₐ[k] S_K :=
    Algebra.TensorProduct.map (AlgHom.id k K) π
  have hraw : RingHom.ker raw.toRingHom =
      Ideal.map (includeRight :
        MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom
        (RingHom.ker π.toRingHom) := by
    -- Proof comment: tensoring a surjective algebra map extends its kernel along the tensor
    -- inclusion.
    simpa [raw] using Algebra.TensorProduct.lTensor_ker (A := K) π hπ
  have hπK : πK.toRingHom = raw.toRingHom.comp e.symm.toRingHom := by
    -- Proof comment: rewrite the `aeval` presentation as the tensor presentation through the
    -- polynomial/tensor equivalence.
    simpa [πK, raw, e] using
      congrArg AlgHom.toRingHom
        (tensorBaseChangePolynomialAlgHom_restrictScalars_local (K := K) π)
  have hβ : β.toRingHom = e.toRingHom.comp
      (includeRight : MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom := by
    have hβAlg : β =
        (e.toAlgHom.restrictScalars k).comp
          (includeRight : MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k) := by
      -- Proof comment: the coefficient-extension map is the tensor inclusion followed by the
      -- polynomial/tensor equivalence.
      apply MvPolynomial.algHom_ext
      intro i
      simp [β, e]
    simpa using congrArg AlgHom.toRingHom hβAlg
  calc
    RingHom.ker πK.toRingHom = Ideal.comap e.symm.toRingHom (RingHom.ker raw.toRingHom) := by
      rw [hπK]
      exact (RingHom.comap_ker raw.toRingHom e.symm.toRingHom).symm
    _ = Ideal.map e.toRingHom (RingHom.ker raw.toRingHom) := by
      exact Ideal.comap_symm (f := e.toRingEquiv) (I := RingHom.ker raw.toRingHom)
    _ = Ideal.map e.toRingHom
          (Ideal.map (includeRight :
            MvPolynomial (Fin n) k →ₐ[k] K ⊗[k] MvPolynomial (Fin n) k).toRingHom
            (RingHom.ker π.toRingHom)) := by
      rw [hraw]
    _ = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
      rw [Ideal.map_map]
      rw [hβ]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: tensoring a `k`-algebra with `K` is flat over the original
algebra through the right tensor inclusion. -/
private lemma tensorProductIncludeRight_moduleFlat_local
    (A : Type*) [CommRing A] [Algebra k A] :
    Module.Flat A (K ⊗[k] A) := by
  -- Proof comment: compare `K ⊗ A` with the standard flat base change `A ⊗ K`.
  have hflatTensor : Module.Flat A (A ⊗[k] K) := by
    exact Module.Flat.baseChange k A K
  let e : K ⊗[k] A ≃ₗ[A] A ⊗[k] K := by
    let e0 : K ⊗[k] A ≃ₗ[k] A ⊗[k] K := TensorProduct.comm k K A
    refine
      { toFun := e0
        invFun := e0.symm
        map_add' := e0.map_add
        map_smul' := ?_
        left_inv := e0.left_inv
        right_inv := e0.right_inv }
    intro a x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c b =>
        change (TensorProduct.comm k K A)
            (((includeRight : A →ₐ[k] K ⊗[k] A) a) * (c ⊗ₜ[k] b)) =
          (a * b) ⊗ₜ[k] c
        simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
          TensorProduct.comm_tmul]
    | add x y hx hy => simp [hx, hy]
  -- Proof comment: flatness transports across the explicit `A`-linear equivalence.
  exact Module.Flat.of_linearEquiv e

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the coefficient-extension map on polynomial rings is flat. -/
private lemma mvPolynomialFieldExtension_moduleFlat_local
    {n : ℕ} :
    let P := MvPolynomial (Fin n) k
    let PK := MvPolynomial (Fin n) K
    let β : P →ₐ[k] PK := MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    letI : Algebra P PK := β.toAlgebra
    Module.Flat P PK := by
  intro P PK β
  letI : Algebra P PK := β.toAlgebra
  have hflatTensor : Module.Flat P (K ⊗[k] P) :=
    tensorProductIncludeRight_moduleFlat_local (K := K) P
  -- Proof comment: identify the polynomial ring over `K` with the tensor product as a
  -- coefficient-extension module.
  let ePoly : PK ≃ₗ[P] K ⊗[k] P := by
    let eForward : K ⊗[k] P ≃ₐ[K] PK := MvPolynomial.algebraTensorAlgEquiv k K
    let eBackward : PK ≃ₐ[K] K ⊗[k] P := eForward.symm
    have hβAlg :
        β = (eForward.toAlgHom.restrictScalars k).comp
          (includeRight : P →ₐ[k] K ⊗[k] P) := by
      apply MvPolynomial.algHom_ext
      intro i
      calc
        β (MvPolynomial.X i) =
            (MvPolynomial.map (algebraMap k K)) (MvPolynomial.X i) := by
          rfl
        _ = MvPolynomial.X i := MvPolynomial.map_X (algebraMap k K) i
        _ = eForward (1 ⊗ₜ[k] MvPolynomial.X i) := by
          simp [eForward, MvPolynomial.algebraTensorAlgEquiv]
    have hβ_apply (p : P) :
        eBackward (β p) = (includeRight : P →ₐ[k] K ⊗[k] P) p := by
      have hp : eForward ((includeRight : P →ₐ[k] K ⊗[k] P) p) = β p := by
        simpa using congrArg (fun f : P →ₐ[k] PK => f p) hβAlg.symm
      rw [← hp]
      exact eForward.symm_apply_apply ((includeRight : P →ₐ[k] K ⊗[k] P) p)
    let e0 : PK ≃ₗ[K] K ⊗[k] P := eBackward.toLinearEquiv
    refine
      { toFun := e0
        invFun := e0.symm
        map_add' := e0.map_add
        map_smul' := ?_
        left_inv := e0.left_inv
        right_inv := e0.right_inv }
    intro p x
    change eBackward (β p * x) = (includeRight : P →ₐ[k] K ⊗[k] P) p * eBackward x
    rw [map_mul, hβ_apply]
  -- Proof comment: the standard tensor flatness gives flatness of coefficient extension.
  exact Module.Flat.of_linearEquiv ePoly

/-- Helper for Chap10 Lemma 10 135 10: Lemma 10.112.7 rewrites prime height under going-down as
the contracted height plus the fiber-prime height. -/
private lemma height_eq_under_add_fiberPrimeHeight_of_hasGoingDown_local
    {R : Type*} {T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Algebra.HasGoingDown R T]
    (q : PrimeSpectrum T) :
    q.asIdeal.height = (q.asIdeal.under R).height + (fiberPrimeAt R T q).asIdeal.height := by
  -- Proof comment: convert the local-ring dimension equality to the corresponding equality of
  -- prime heights.
  have h : ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
      ((q.asIdeal.under R).height : ℕ∞) +
        (((fiberPrimeAt R T q).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
    calc
      ((q.asIdeal.height : ℕ∞) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime q.asIdeal) := by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal
              (Localization.AtPrime q.asIdeal)]
      _ = ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
            ringKrullDim (fiberLocalRingAt R T q) :=
          ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
            q
      _ = ((q.asIdeal.under R).height : ℕ∞) +
          (((fiberPrimeAt R T q).asIdeal.height : ℕ∞) : WithBot ℕ∞) := by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height (q.asIdeal.under R)
              (Localization.AtPrime (q.asIdeal.under R))]
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height (fiberPrimeAt R T q).asIdeal
              (fiberLocalRingAt R T q)]
  exact_mod_cast h

/-- Helper for Chap10 Lemma 10 135 10: the going-down height formula after naming the contracted
prime explicitly. -/
private lemma height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown_local
    {R : Type*} {T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsNoetherianRing R] [IsNoetherianRing T] [Algebra.HasGoingDown R T]
    {p : PrimeSpectrum R} (q : PrimeSpectrum T)
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p) :
    q.asIdeal.height = p.asIdeal.height + (fiberPrimeAt R T q).asIdeal.height := by
  -- Proof comment: replace the anonymous `under` prime by the named contraction point.
  have h_under : q.asIdeal.under R = p.asIdeal := by
    simpa [Ideal.under_def, PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal hq
  simpa [h_under] using
    height_eq_under_add_fiberPrimeHeight_of_hasGoingDown_local (R := R) (T := T) q

/-- Helper for Chap10 Lemma 10 135 10: the height of a canonical fiber prime is its order height
in the raw prime-spectrum fiber. -/
private lemma fiberPrimeAt_height_eq_preimage_height_local
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    (fiberPrimeAt R T q).asIdeal.height =
      Order.height
        (⟨q, rfl⟩ :
          (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R T) q}) := by
  -- Proof comment: pass through the standard raw-fiber order isomorphism.
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R T) q
  let qOver : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}) := ⟨q, rfl⟩
  let ePre : ↑(PrimeSpectrum.comap (algebraMap R T) ⁻¹' {p}) ≃o
      PrimeSpectrum (p.asIdeal.Fiber T) :=
    PrimeSpectrum.preimageOrderIsoFiber R T p
  have heq : ePre qOver = fiberPrimeAt R T q := rfl
  calc
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) := by
      rw [Ideal.height_eq_primeHeight]
      rfl
    _ = Order.height (ePre qOver) := by
      exact congrArg Order.height heq.symm
    _ = Order.height qOver := Order.height_orderIso ePre qOver
    _ =
        Order.height
          (⟨q, rfl⟩ :
            (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
              {PrimeSpectrum.comap (algebraMap R T) q}) := by
      rfl

/-- Helper for Chap10 Lemma 10 135 10: the ideal height of a fiber prime equals its order height
as a point of the fiber spectrum. -/
private lemma fiberPrimeAt_height_eq_orderHeight_local
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) := by
  -- Proof comment: unfold only the standard prime-height comparison.
  rw [Ideal.height_eq_primeHeight]
  rfl

/-- Helper for Chap10 Lemma 10 135 10: equality of fiber-prime order heights gives equality of
their ideal-height spellings. -/
private lemma fiberPrimeAt_asIdeal_height_eq_of_orderHeight_eq_local
    {R T R' T' : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [CommRing R'] [CommRing T'] [Algebra R' T']
    {q : PrimeSpectrum T} {q' : PrimeSpectrum T'}
    (h : Order.height (fiberPrimeAt R T q) = Order.height (fiberPrimeAt R' T' q')) :
    (fiberPrimeAt R T q).asIdeal.height = (fiberPrimeAt R' T' q').asIdeal.height := by
  -- Proof comment: move both sides once into the canonical order-height spelling.
  calc
    (fiberPrimeAt R T q).asIdeal.height = Order.height (fiberPrimeAt R T q) :=
      fiberPrimeAt_height_eq_orderHeight_local (R := R) (T := T) q
    _ = Order.height (fiberPrimeAt R' T' q') := h
    _ = (fiberPrimeAt R' T' q').asIdeal.height :=
      (fiberPrimeAt_height_eq_orderHeight_local (R := R') (T := T') q').symm

/-- Helper for Chap10 Lemma 10 135 10: the order height of a fiber prime is the order height of
the corresponding point in the raw prime-spectrum fiber. -/
private lemma fiberPrimeAt_orderHeight_eq_preimage_height_local
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (q : PrimeSpectrum T) :
    Order.height (fiberPrimeAt R T q) =
      Order.height
        (⟨q, rfl⟩ :
          (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
            {PrimeSpectrum.comap (algebraMap R T) q}) := by
  -- Proof comment: reuse the ideal-height/raw-fiber adapter and rewrite both sides.
  calc
    Order.height (fiberPrimeAt R T q) = (fiberPrimeAt R T q).asIdeal.height :=
      (fiberPrimeAt_height_eq_orderHeight_local (R := R) (T := T) q).symm
    _ =
        Order.height
          (⟨q, rfl⟩ :
            (PrimeSpectrum.comap (algebraMap R T)) ⁻¹'
              {PrimeSpectrum.comap (algebraMap R T) q}) :=
      fiberPrimeAt_height_eq_preimage_height_local (R := R) (T := T) q

/-- Helper for Chap10 Lemma 10 135 10: the raw-fiber height comparison can be read over any
explicitly equal base point. -/
private lemma fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq_local
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    {p : PrimeSpectrum R} (q : PrimeSpectrum T)
    (hq : PrimeSpectrum.comap (algebraMap R T) q = p) :
    Order.height (fiberPrimeAt R T q) =
      Order.height
        (⟨q, hq⟩ : (PrimeSpectrum.comap (algebraMap R T)) ⁻¹' {p}) := by
  -- Proof comment: reduce to the canonical contraction point.
  subst p
  simpa using fiberPrimeAt_orderHeight_eq_preimage_height_local (R := R) (T := T) q

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: a polynomial prime over the downstairs presentation point
contains the base-changed presentation kernel. -/
private lemma tensorProductPresentation_ker_le_of_comap_eq_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (y : PrimeSpectrum (MvPolynomial (Fin n) k))
    (r : PrimeSpectrum (MvPolynomial (Fin n) K))
    (hker_y : RingHom.ker π.toRingHom ≤ y.asIdeal)
    (hr : PrimeSpectrum.comap
        ((MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)).toRingHom) r = y) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    RingHom.ker πK.toRingHom ≤ r.asIdeal := by
  intro πK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  have hker :
      RingHom.ker πK.toRingHom = Ideal.map β.toRingHom (RingHom.ker π.toRingHom) := by
    simpa [πK, β] using tensorBaseChangePolynomialAlgHom_ker_local (K := K) π hπ
  -- Proof comment: the kernel containment is exactly the map/comap adjunction after the kernel
  -- has been identified as an extended ideal.
  rw [hker, Ideal.map_le_iff_le_comap]
  have hy : y.asIdeal = Ideal.comap β.toRingHom r.asIdeal := by
    simpa [β, PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hr).symm
  exact le_trans hker_y hy.le

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the raw fibers over a surjective base-changed presentation
and over the quotient have equal distinguished order height. -/
private lemma tensorProductPresentation_preimageFiber_height_eq_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
      MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
    Order.height
        (⟨yK, by
          exact baseChangePresentation_prime_comap_of_eq (K := K) π x xK hxK⟩ :
          (PrimeSpectrum.comap β.toRingHom) ⁻¹' Set.singleton y) =
      Order.height (⟨xK, hxK⟩ : (PrimeSpectrum.comap iSK) ⁻¹' Set.singleton x) := by
  intro πK y yK β
  have hπK : Function.Surjective πK := by
    -- Proof comment: the upstairs polynomial presentation is surjective after tensor base change.
    simpa [πK] using tensorBaseChangePolynomialAlgHom_surjective_local (K := K) π hπ
  have hker_y : RingHom.ker π.toRingHom ≤ y.asIdeal := by
    intro a ha
    change π.toRingHom a ∈ x.asIdeal
    rw [RingHom.mem_ker.mp ha]
    exact x.asIdeal.zero_mem
  let eQuot := Ideal.primeSpectrumOrderIsoZeroLocusOfSurj πK.toRingHom hπK rfl
  have hQuot_val (s : PrimeSpectrum S_K) :
      (eQuot s).1 = PrimeSpectrum.comap πK.toRingHom s := rfl
  -- Proof comment: define the comparison map by descending a polynomial-fiber prime through the
  -- quotient presentation.
  let toFun : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) →
      ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := fun rOver ↦ by
    have hker_r : RingHom.ker πK.toRingHom ≤ rOver.1.asIdeal := by
      simpa [πK, β] using
        tensorProductPresentation_ker_le_of_comap_eq_local (K := K) (S := S)
          π hπ y rOver.1 hker_y rOver.2
    let s : PrimeSpectrum S_K := eQuot.symm ⟨rOver.1, hker_r⟩
    refine ⟨s, ?_⟩
    have hπK_s : PrimeSpectrum.comap πK.toRingHom s = rOver.1 :=
      congrArg Subtype.val (eQuot.right_inv ⟨rOver.1, hker_r⟩)
    have hcomp : PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK s) = y := by
      calc
        PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK s) =
            PrimeSpectrum.comap β.toRingHom (PrimeSpectrum.comap πK.toRingHom s) := by
          simpa [πK, β] using (baseChangePresentation_prime_comap (K := K) π s).symm
        _ = PrimeSpectrum.comap β.toRingHom rOver.1 := by
          rw [hπK_s]
        _ = y := rOver.2
    exact (PrimeSpectrum.comap_injective_of_surjective π.toRingHom hπ) (by simpa [y] using hcomp)
  -- Proof comment: the inverse map contracts along the upstairs presentation.
  let invFun : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) →
      ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) := fun sOver ↦ by
    refine ⟨PrimeSpectrum.comap πK.toRingHom sOver.1, ?_⟩
    calc
      PrimeSpectrum.comap β.toRingHom (PrimeSpectrum.comap πK.toRingHom sOver.1) =
          PrimeSpectrum.comap π.toRingHom (PrimeSpectrum.comap iSK sOver.1) := by
        simpa [πK, β] using baseChangePresentation_prime_comap (K := K) π sOver.1
      _ = PrimeSpectrum.comap π.toRingHom x := by
        rw [sOver.2]
      _ = y := by
        simp [y]
  have hπK_toFun (rOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y})) :
      PrimeSpectrum.comap πK.toRingHom (toFun rOver).1 = rOver.1 := by
    dsimp [toFun]
    have hker_r : RingHom.ker πK.toRingHom ≤ rOver.1.asIdeal := by
      simpa [πK, β] using
        tensorProductPresentation_ker_le_of_comap_eq_local (K := K) (S := S)
          π hπ y rOver.1 hker_y rOver.2
    exact congrArg Subtype.val (eQuot.right_inv ⟨rOver.1, hker_r⟩)
  let eRaw : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) ≃o
      ((PrimeSpectrum.comap iSK) ⁻¹' {x}) :=
    { toEquiv :=
        { toFun := toFun
          invFun := invFun
          left_inv := by
            intro rOver
            apply Subtype.ext
            exact hπK_toFun rOver
          right_inv := by
            intro sOver
            apply Subtype.ext
            apply PrimeSpectrum.comap_injective_of_surjective πK.toRingHom hπK
            rw [hπK_toFun (invFun sOver)] }
      map_rel_iff' := by
        intro a b
        constructor
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 := by
            exact (eQuot.map_rel_iff').2 h
          change a.1 ≤ b.1
          change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1 at h'
          rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1] at h'
          rwa [hπK_toFun a, hπK_toFun b] at h'
        · intro h
          have h' : eQuot (toFun a).1 ≤ eQuot (toFun b).1 := by
            change (eQuot (toFun a).1).1 ≤ (eQuot (toFun b).1).1
            rw [hQuot_val (toFun a).1, hQuot_val (toFun b).1]
            rwa [hπK_toFun a, hπK_toFun b]
          exact (eQuot.map_rel_iff').1 h' }
  let yKOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) :=
    ⟨yK, by
      exact baseChangePresentation_prime_comap_of_eq (K := K) π x xK hxK⟩
  let xKOver : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := ⟨xK, hxK⟩
  have hendpoint : eRaw yKOver = xKOver := by
    apply Subtype.ext
    apply PrimeSpectrum.comap_injective_of_surjective πK.toRingHom hπK
    calc
      PrimeSpectrum.comap πK.toRingHom (eRaw yKOver).1 = yKOver.1 :=
        hπK_toFun yKOver
      _ = PrimeSpectrum.comap πK.toRingHom xKOver.1 := rfl
  -- Proof comment: order isomorphisms preserve the height of the distinguished fiber point.
  calc
    Order.height yKOver = Order.height (eRaw yKOver) :=
      (Order.height_orderIso eRaw yKOver).symm
    _ = Order.height xKOver := by
      rw [hendpoint]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the fiber prime over the base-changed polynomial
presentation and the fiber prime over the quotient presentation have equal height. -/
private lemma baseChangedPresentation_fiberPrimeHeight_eq_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
      Order.height (fiberPrimeAt S S_K xK) := by
  intro πK yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
  have hcomap : PrimeSpectrum.comap β.toRingHom yK = y := by
    -- Proof comment: the base-change square contracts the upstairs polynomial point to the
    -- downstairs polynomial point.
    exact baseChangePresentation_prime_comap_of_eq (K := K) π x xK hxK
  let yKOver : ((PrimeSpectrum.comap β.toRingHom) ⁻¹' {y}) := ⟨yK, hcomap⟩
  let xKOver : ((PrimeSpectrum.comap iSK) ⁻¹' {x}) := ⟨xK, hxK⟩
  have hleft :
      Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height yKOver := by
    simpa [yKOver] using
      fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq_local
        (R := MvPolynomial (Fin n) k) (T := MvPolynomial (Fin n) K) yK hcomap
  have hright :
      Order.height (fiberPrimeAt S S_K xK) = Order.height xKOver := by
    simpa [xKOver] using
      fiberPrimeAt_orderHeight_eq_preimage_height_of_comap_eq_local (R := S) (T := S_K) xK hxK
  have hraw : Order.height yKOver = Order.height xKOver := by
    simpa [πK, y, yK, β, yKOver, xKOver] using
      tensorProductPresentation_preimageFiber_height_eq_local (K := K) π hπ x xK hxK
  calc
    Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height yKOver := hleft
    _ = Order.height xKOver := hraw
    _ = Order.height (fiberPrimeAt S S_K xK) := hright.symm

/-- Helper for Chap10 Lemma 10 135 10: subtracting two decompositions with the same finite
summand leaves the same `ℕ∞` defect. -/
private lemma enat_sub_eq_sub_of_eq_add_common_local {x y x' y' c : ℕ∞}
    (hy' : y' = y + c) (hx' : x' = x + c) (hxy : x ≤ y)
    (hx_ne_top : x ≠ ⊤) (hy'_ne_top : y' ≠ ⊤) :
    y' - x' = y - x := by
  -- Proof comment: prove the common summand is finite, then cancel it in the decomposed sum.
  have hc_ne_top : c ≠ ⊤ := by
    intro hc
    apply hy'_ne_top
    calc
      y' = y + c := hy'
      _ = ⊤ := by
        rw [hc]
        simp
  have hxc_ne_top : x + c ≠ ⊤ := by
    have hx_lt_top : x < ⊤ := (lt_top_iff_ne_top).2 hx_ne_top
    have hc_lt_top : c < ⊤ := (lt_top_iff_ne_top).2 hc_ne_top
    exact (lt_top_iff_ne_top).1 ((ENat.add_lt_top).2 ⟨hx_lt_top, hc_lt_top⟩)
  have hdecomp : y + c = (y - x) + (x + c) := by
    calc
      y + c = (y - x + x) + c := by
        rw [tsub_add_cancel_of_le hxy]
      _ = (y - x) + (x + c) := by
        ac_rfl
  rw [hy', hx']
  exact AddLECancellable.tsub_eq_of_eq_add
    (ENat.addLECancellable_of_ne_top hxc_ne_top) hdecomp

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the base-changed polynomial prime height decomposes as the
contracted height plus a fiber height. -/
private lemma baseChangedPresentation_polynomial_height_eq_add_commonFiber_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    yK.asIdeal.height = y.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
  intro πK y yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  letI : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  letI : IsNoetherianRing (MvPolynomial (Fin n) K) := inferInstance
  letI : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    mvPolynomialFieldExtension_moduleFlat_local (k := k) (K := K) (n := n)
  letI : Algebra.HasGoingDown (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) :=
    Algebra.HasGoingDown.of_flat
  have hcomap : PrimeSpectrum.comap β.toRingHom yK = y := by
    -- Proof comment: use the polynomial coefficient-extension square to identify the contraction.
    exact baseChangePresentation_prime_comap_of_eq (K := K) π x xK hxK
  exact height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown_local
    (R := MvPolynomial (Fin n) k) (T := MvPolynomial (Fin n) K) yK hcomap

/-- Helper for Chap10 Lemma 10 135 10: the quotient prime height decomposes with the same fiber
height as the polynomial presentation. -/
private lemma baseChangedPresentation_quotient_height_eq_add_commonFiber_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    xK.asIdeal.height = x.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
  intro πK yK
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  letI : Algebra.FiniteType K S_K := inferInstance
  letI : IsNoetherianRing S_K := Algebra.FiniteType.isNoetherianRing K S_K
  letI : Module.Flat S S_K := tensorProductIncludeRight_moduleFlat_local (K := K) S
  letI : Algebra.HasGoingDown S S_K := Algebra.HasGoingDown.of_flat
  have hfiberOrder :
      Order.height (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK) =
        Order.height (fiberPrimeAt S S_K xK) := by
    -- Proof comment: compare the two fiber primes using the surjective presentation square.
    simpa [πK, yK] using
      baseChangedPresentation_fiberPrimeHeight_eq_local (K := K) π hπ x xK hxK
  have hfiberIdeal := fiberPrimeAt_asIdeal_height_eq_of_orderHeight_eq_local hfiberOrder
  have hquotBase :=
    height_eq_comap_add_fiberPrimeHeight_of_hasGoingDown_local (R := S) (T := S_K) xK hxK
  exact hquotBase.trans (by rw [← hfiberIdeal])

/-- Helper for Chap10 Lemma 10 135 10: the height defect in a fixed polynomial presentation is
unchanged by tensor base change. -/
private lemma baseChangedPresentation_heightDefect_eq_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (x : PrimeSpectrum S) (xK : PrimeSpectrum S_K) (hxK : PrimeSpectrum.comap iSK xK = x) :
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PrimeSpectrum.comap π.toRingHom x
    let yK : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap πK.toRingHom xK
    yK.asIdeal.height - xK.asIdeal.height = y.asIdeal.height - x.asIdeal.height := by
  intro πK y yK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  letI : IsNoetherianRing (MvPolynomial (Fin n) K) := inferInstance
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hpoly : yK.asIdeal.height = y.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
    -- Proof comment: decompose the polynomial prime height using going-down for coefficient
    -- extension.
    simpa [πK, y, yK, β] using
      baseChangedPresentation_polynomial_height_eq_add_commonFiber_local (K := K) π x xK hxK
  have hquot : xK.asIdeal.height = x.asIdeal.height +
      (fiberPrimeAt (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) yK).asIdeal.height := by
    -- Proof comment: decompose the quotient prime height with the same fiber summand.
    simpa [πK, y, yK, β] using
      baseChangedPresentation_quotient_height_eq_add_commonFiber_local (K := K) π hπ x xK hxK
  have hx_le_y : x.asIdeal.height ≤ y.asIdeal.height := by
    simpa [Ideal.height_eq_primeHeight, Ideal.primeHeight, y] using
      (Order.height_le_height_apply_of_strictMono
        (PrimeSpectrum.comap π.toRingHom)
        (RingHom.strictMono_comap_of_surjective hπ)
        x)
  have hyK_ne_top : yK.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime yK))
  have hx_ne_top : x.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime x))
  -- Proof comment: cancel the common finite fiber summand from the two decompositions.
  exact enat_sub_eq_sub_of_eq_add_common_local hpoly hquot hx_le_y hx_ne_top hyK_ne_top

/-- Helper for Chap10 Lemma 10 135 10: the original presentation and its tensor base change have
the same finite height defect at corresponding presentation primes. -/
private lemma baseChangedPresentation_commonHeightDefect_local
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    ∃ d : ℕ,
      (PolynomialPresentationAtPrime.prime π q).asIdeal.height - q.asIdeal.height = (d : ℕ∞) ∧
        (PolynomialPresentationAtPrime.prime πK qK).asIdeal.height - qK.asIdeal.height =
          (d : ℕ∞) := by
  intro q πK
  let y : PrimeSpectrum (MvPolynomial (Fin n) k) := PolynomialPresentationAtPrime.prime π q
  let yK : PrimeSpectrum (MvPolynomial (Fin n) K) :=
    PolynomialPresentationAtPrime.prime πK qK
  have hxK : PrimeSpectrum.comap iSK qK = q := rfl
  have hdefEq : yK.asIdeal.height - qK.asIdeal.height = y.asIdeal.height - q.asIdeal.height := by
    -- Proof comment: the height-defect helper has already aligned the polynomial and quotient
    -- fiber-height decompositions for this fixed presentation.
    simpa [πK, y, yK, PolynomialPresentationAtPrime.prime] using
      baseChangedPresentation_heightDefect_eq_local (K := K) π hπ q qK hxK
  let d : ℕ := (y.asIdeal.height - q.asIdeal.height).toNat
  have hy_ne_top : y.asIdeal.height ≠ ⊤ :=
    Ideal.height_ne_top (Ideal.IsPrime.ne_top (PrimeSpectrum.isPrime y))
  have hdef_ne_top : y.asIdeal.height - q.asIdeal.height ≠ ⊤ :=
    ne_top_of_le_ne_top hy_ne_top tsub_le_self
  refine ⟨d, ?_, ?_⟩
  · -- Proof comment: the downstairs defect is finite because it is bounded by the polynomial
    -- prime height.
    exact_mod_cast (ENat.coe_toNat hdef_ne_top).symm
  · -- Proof comment: the upstairs defect is the same finite value.
    calc
      (PolynomialPresentationAtPrime.prime πK qK).asIdeal.height - qK.asIdeal.height =
          y.asIdeal.height - q.asIdeal.height := by
        simpa [yK] using hdefEq
      _ = (d : ℕ∞) := by
        exact_mod_cast (ENat.coe_toNat hdef_ne_top).symm

/-- Helper for Chap10 Lemma 10 135 10: a finite-dimensional vector space generated by at most
`d` basis vectors admits an explicit generating family indexed by `Fin d`. -/
private lemma exists_generators_of_finrank_le_of_field
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {d : ℕ} (hd : Module.finrank F V ≤ d) :
    ∃ v : Fin d → V, Submodule.span F (Set.range v) = ⊤ := by
  let r := Module.finrank F V
  let e : V ≃ₗ[F] (Fin r → F) := (Module.finBasis F V).equivFun
  let ρ : (Fin d → F) →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i : Fin r ↦ LinearMap.proj (Fin.castLE hd i)
  have hρ : Function.Surjective ρ := by
    -- Proof comment: extend coordinates by zero beyond the first `r` positions.
    intro y
    refine ⟨fun i ↦ if h : i.1 < r then y ⟨i.1, h⟩ else 0, ?_⟩
    ext i
    simp [ρ, i.2]
  let σ : (Fin d → F) →ₗ[F] V := e.symm.toLinearMap.comp ρ
  have hσ : Function.Surjective σ := e.symm.surjective.comp hρ
  let v : Fin d → V := fun i ↦ σ (Pi.single i (1 : F))
  have hlin : Fintype.linearCombination F v = σ := by
    -- Proof comment: the chosen vectors are the images of the standard coordinate vectors, so
    -- their linear-combination map is exactly `σ`.
    apply LinearMap.ext
    intro x
    calc
      (Fintype.linearCombination F v) x
          = ∑ i, x i • σ (Pi.single i (1 : F)) := by
              simp [v, Fintype.linearCombination_apply]
      _ = ∑ i, σ (x i • (Pi.single i (1 : F) : Fin d → F)) := by
            congr with i
            exact (σ.map_smul (x i) (Pi.single i (1 : F))).symm
      _ = σ (∑ i, x i • (Pi.single i (1 : F) : Fin d → F)) := by
            symm
            simp [map_sum]
      _ = σ x := by
            congr 1
            ext i
            simpa [Pi.single_apply, mul_comm] using
              (Fintype.sum_pi_single (i := i) (f := x))
  refine ⟨v, ?_⟩
  rw [span_range_eq_top_iff_surjective_fintypeLinearCombination]
  intro x
  rcases hσ x with ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  simpa [hlin]

/-- Helper for Chap10 Lemma 10 135 10: over a local ring, `d` generators are equivalent to a
residue-vector-space dimension bound. -/
private lemma exists_fin_generators_iff_residue_finrank_le
    {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d : ℕ) :
    (∃ xs : Fin d → M, Submodule.span R (Set.range xs) = ⊤) ↔
      Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) ≤ d := by
  constructor
  · rintro ⟨xs, hxs⟩
    have hR :
        Submodule.span R
          (Set.range ((TensorProduct.mk R (ResidueField R) M 1) ∘ xs)) = ⊤ := by
      -- Proof comment: tensoring the spanning submodule with the residue field still spans.
      have h := (IsLocalRing.map_tensorProduct_mk_eq_top
        (N := Submodule.span R (Set.range xs)) (M := M)).2 hxs
      rw [Submodule.map_span] at h
      simpa [Set.range_comp] using h
    have hκ :
        Submodule.span (ResidueField R)
          (Set.range ((TensorProduct.mk R (ResidueField R) M 1) ∘ xs)) = ⊤ := by
      -- Proof comment: upgrade the same set from an `R`-span statement to a residue-field span.
      rw [← Submodule.restrictScalars_eq_top_iff R (ResidueField R)
        (ResidueField R ⊗[R] M)]
      rw [Submodule.restrictScalars_span R (ResidueField R) Ideal.Quotient.mk_surjective]
      exact hR
    simpa using finrank_le_of_span_eq_top hκ
  · intro hfin
    obtain ⟨ys, hys⟩ := exists_generators_of_finrank_le_of_field
      (F := ResidueField R) (V := ResidueField R ⊗[R] M) hfin
    choose xs hxs using fun i : Fin d ↦ TensorProduct.mk_surjective R M (ResidueField R)
      Ideal.Quotient.mk_surjective (ys i)
    refine ⟨xs, ?_⟩
    -- Proof comment: lift residue generators to `M`, then use Nakayama's tensor criterion.
    rw [← IsLocalRing.map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range xs))]
    rw [Submodule.map_span]
    have hrange : (TensorProduct.mk R (ResidueField R) M 1) '' Set.range xs = Set.range ys := by
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hxs i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨xs i, ⟨i, rfl⟩, hxs i⟩
    rw [hrange]
    rw [← Submodule.restrictScalars_span R (ResidueField R) Ideal.Quotient.mk_surjective]
    rw [Submodule.restrictScalars_eq_top_iff]
    exact hys

/-- Helper for Chap10 Lemma 10 135 10: residue-fiber dimension is unchanged by flat local
base change. -/
private lemma residue_finrank_tensorProduct_baseChange_eq
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsLocalRing R] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.finrank (ResidueField T) (ResidueField T ⊗[T] (T ⊗[R] M)) =
      Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
  letI : Algebra (ResidueField R) (ResidueField T) :=
    (IsLocalRing.ResidueField.map (algebraMap R T)).toAlgebra
  have htower_res : IsScalarTower R (ResidueField R) (ResidueField T) := by
    -- Proof comment: the residue-field map is compatible with the original algebra map.
    apply IsScalarTower.of_algebraMap_eq
    intro r
    change algebraMap R (ResidueField T) r = residue T (algebraMap R T r)
    rw [IsScalarTower.algebraMap_apply R T (ResidueField T) r]
    rw [IsLocalRing.ResidueField.algebraMap_eq]
  letI : IsScalarTower R (ResidueField R) (ResidueField T) := htower_res
  let eLeft : ResidueField T ⊗[T] (T ⊗[R] M) ≃ₗ[ResidueField T]
      ResidueField T ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R T (ResidueField T)
      (ResidueField T) M
  let eRight : ResidueField T ⊗[ResidueField R] (ResidueField R ⊗[R] M)
      ≃ₗ[ResidueField T] ResidueField T ⊗[R] M :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange R (ResidueField R) (ResidueField T)
      (ResidueField T) M
  -- Proof comment: reassociate the two residue fibers, then use finrank invariance under field
  -- extension.
  calc
    Module.finrank (ResidueField T) (ResidueField T ⊗[T] (T ⊗[R] M)) =
        Module.finrank (ResidueField T)
          (ResidueField T ⊗[ResidueField R] (ResidueField R ⊗[R] M)) := by
      exact (eLeft.trans eRight.symm).finrank_eq
    _ = Module.finrank (ResidueField R) (ResidueField R ⊗[R] M) := by
      simpa using (Module.finrank_baseChange (R := ResidueField T) (S := ResidueField R)
        (M' := ResidueField R ⊗[R] M))

/-- Helper for Chap10 Lemma 10 135 10: a finite module admits `d` generators if and only if its
flat local base change does. -/
private lemma exists_fin_generators_tensorProduct_iff_of_flatLocal
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsLocalRing R] [IsLocalRing T] [Module.Flat R T] [IsLocalHom (algebraMap R T)]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M] (d : ℕ) :
    (∃ xs : Fin d → M, Submodule.span R (Set.range xs) = ⊤) ↔
      ∃ ys : Fin d → T ⊗[R] M, Submodule.span T (Set.range ys) = ⊤ := by
  constructor
  · intro h
    -- Proof comment: compare both generator counts on residue fibers.
    have hfin := (exists_fin_generators_iff_residue_finrank_le (R := R) (M := M) d).1 h
    exact (exists_fin_generators_iff_residue_finrank_le (R := T) (M := T ⊗[R] M) d).2 <| by
      rwa [residue_finrank_tensorProduct_baseChange_eq (R := R) (T := T) (M := M)]
  · intro h
    -- Proof comment: the same residue-fiber comparison reflects the bound back downstairs.
    have hfin := (exists_fin_generators_iff_residue_finrank_le (R := T) (M := T ⊗[R] M) d).1 h
    exact (exists_fin_generators_iff_residue_finrank_le (R := R) (M := M) d).2 <| by
      rwa [residue_finrank_tensorProduct_baseChange_eq (R := R) (T := T) (M := M)] at hfin

/-- Helper for Chap10 Lemma 10 135 10: ambient ideal generators are equivalent to module
generators of the ideal subtype. -/
private lemma ideal_generators_iff_submodule_generators
    {R : Type*} [CommRing R] (I : Ideal R) (d : ℕ) :
    (∃ xs : Fin d → R, Ideal.span (Set.range xs) = I) ↔
      ∃ ys : Fin d → I, Submodule.span R (Set.range ys) = ⊤ := by
  constructor
  · rintro ⟨xs, hxs⟩
    have hmem : ∀ i, xs i ∈ I := by
      intro i
      rw [← hxs]
      exact Ideal.subset_span ⟨i, rfl⟩
    refine ⟨fun i ↦ ⟨xs i, hmem i⟩, ?_⟩
    -- Proof comment: turn the ambient span equality into a top-span statement inside `I`.
    exact (Submodule.span_range_subtype_eq_top_iff (p := I) (s := xs) hmem).2
      (by simpa using hxs)
  · rintro ⟨ys, hys⟩
    refine ⟨fun i ↦ (ys i : R), ?_⟩
    -- Proof comment: forget the subtype coercions and recover the ambient ideal span.
    exact (Submodule.span_range_subtype_eq_top_iff (p := I) (s := fun i ↦ (ys i : R))
      (fun i ↦ (ys i).2)).1 hys

/-- Helper for Chap10 Lemma 10 135 10: the tensor map from a base-changed ideal to the upstairs
ring used to identify the tensor product with the mapped ideal. -/
private noncomputable def idealMapTensorLinearMap
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (I : Ideal R) :
    T ⊗[R] I →ₗ[T] T :=
  (TensorProduct.AlgebraTensorModule.rid R T T).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor T T I.subtype

/-- Helper for Chap10 Lemma 10 135 10: flatness makes the tensor map from a base-changed ideal
injective. -/
private lemma idealMapTensorLinearMap_injective
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Flat R T] (I : Ideal R) :
    Function.Injective (idealMapTensorLinearMap (T := T) I) := by
  -- Proof comment: tensor the injective ideal inclusion and then compose with the right-unit
  -- equivalence for tensor products.
  exact (TensorProduct.AlgebraTensorModule.rid R T T).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)

/-- Helper for Chap10 Lemma 10 135 10: the range of the base-changed ideal tensor map is exactly
the mapped ideal. -/
private lemma idealMapTensorLinearMap_range_eq
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] (I : Ideal R) :
    I.map (algebraMap R T) = LinearMap.range (idealMapTensorLinearMap (T := T) I) := by
  refine le_antisymm ?_ ?_
  · -- Proof comment: each mapped downstairs element is the image of the elementary tensor
    -- `1 ⊗ x`.
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    use 1 ⊗ₜ[R] ⟨x, hx⟩
    simp [idealMapTensorLinearMap, Algebra.smul_def]
  · -- Proof comment: every elementary tensor lands in the ideal generated by the mapped
    -- downstairs ideal, and sums preserve membership.
    rintro - ⟨x, rfl⟩
    induction x with
    | zero => simp
    | add x y hx hy => simpa [Ideal.add_mem] using Ideal.add_mem _ hx hy
    | tmul t x =>
        have : idealMapTensorLinearMap (T := T) I (t ⊗ₜ[R] x) =
            t • idealMapTensorLinearMap (T := T) I (1 ⊗ₜ[R] x) := by
          simp [idealMapTensorLinearMap]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [idealMapTensorLinearMap, Algebra.smul_def] using
          Ideal.mem_map_of_mem (algebraMap R T) x.2

/-- Helper for Chap10 Lemma 10 135 10: a flat base-changed ideal is linearly equivalent to the
mapped ideal. -/
private noncomputable def idealMapTensorLinearEquiv
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [Module.Flat R T] (I : Ideal R) :
    T ⊗[R] I ≃ₗ[T] I.map (algebraMap R T) :=
  (LinearEquiv.ofInjective (idealMapTensorLinearMap (T := T) I)
      (idealMapTensorLinearMap_injective (T := T) I)).trans
    (LinearEquiv.ofEq _ _ (idealMapTensorLinearMap_range_eq (T := T) I).symm)

/-- Helper for Chap10 Lemma 10 135 10: if the mapped ideal has `d` generators after a flat local
base change, then the original finite ideal has `d` generators. -/
private lemma ideal_generators_descend_of_flatLocal_map_eq
    {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [IsLocalRing R] [IsLocalRing T] [Module.Flat R T] [IsLocalHom (algebraMap R T)]
    (I : Ideal R) [Module.Finite R I] (J : Ideal T) {d : ℕ}
    (hIJ : Ideal.map (algebraMap R T) I = J)
    (hJ : ∃ ys : Fin d → T, Ideal.span (Set.range ys) = J) :
    ∃ xs : Fin d → R, Ideal.span (Set.range xs) = I := by
  have hJsub : ∃ ys : Fin d → J, Submodule.span T (Set.range ys) = ⊤ :=
    (ideal_generators_iff_submodule_generators J d).1 hJ
  letI : Module.Finite T J := by
    -- Proof comment: the displayed `d` generators give finite generation of `J` as a module.
    rw [Module.Finite.iff_fg]
    rcases hJ with ⟨ys, hys⟩
    exact Submodule.fg_def.mpr ⟨Set.range ys, Set.finite_range ys, hys⟩
  have hJfin : Module.finrank (ResidueField T) (ResidueField T ⊗[T] J) ≤ d :=
    (exists_fin_generators_iff_residue_finrank_le (R := T) (M := J) d).1 hJsub
  let eIJ : T ⊗[R] I ≃ₗ[T] J :=
    (idealMapTensorLinearEquiv (T := T) I).trans (LinearEquiv.ofEq _ _ hIJ)
  have hTensorFin :
      Module.finrank (ResidueField T) (ResidueField T ⊗[T] (T ⊗[R] I)) ≤ d := by
    -- Proof comment: transport the residue-fiber bound through the linear equivalence
    -- identifying the tensor product with `J`.
    rw [(LinearEquiv.baseChange T (ResidueField T) (T ⊗[R] I) J eIJ).finrank_eq]
    exact hJfin
  have hIfin : Module.finrank (ResidueField R) (ResidueField R ⊗[R] I) ≤ d := by
    -- Proof comment: reflect the bound across the flat local residue-fiber comparison.
    rwa [residue_finrank_tensorProduct_baseChange_eq (R := R) (T := T) (M := I)] at hTensorFin
  have hIsub : ∃ xs : Fin d → I, Submodule.span R (Set.range xs) = ⊤ :=
    (exists_fin_generators_iff_residue_finrank_le (R := R) (M := I) d).2 hIfin
  exact (ideal_generators_iff_submodule_generators I d).2 hIsub

/-- Helper for Chap10 Lemma 10 135 10: a generating family for an ideal maps to a generating
family for the mapped ideal. -/
private lemma ideal_generators_map_of_generators
    {R T : Type*} [CommRing R] [CommRing T] (f : R →+* T)
    {I : Ideal R} {J : Ideal T} {d : ℕ}
    (hIJ : Ideal.map f I = J)
    (hI : ∃ xs : Fin d → R, Ideal.span (Set.range xs) = I) :
    ∃ ys : Fin d → T, Ideal.span (Set.range ys) = J := by
  rcases hI with ⟨xs, hxs⟩
  -- Proof comment: map the selected generators and rewrite `map_span` to identify the generated
  -- upstairs ideal with the image of the downstairs generated ideal.
  refine ⟨fun i ↦ f (xs i), ?_⟩
  calc
    Ideal.span (Set.range fun i ↦ f (xs i)) =
        Ideal.map f (Ideal.span (Set.range xs)) := by
      rw [Ideal.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨xs i, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    _ = J := by
      rw [hxs, hIJ]

omit [Algebra.FiniteType k S] in
/-- Helper for Chap10 Lemma 10 135 10: the number of generators of the localized kernel is
invariant for a presentation and its tensor base change. -/
private lemma kernelGeneratedByCondition_iff_baseChangedPresentation
    {n : ℕ} (π : MvPolynomial (Fin n) k →ₐ[k] S) (hπ : Function.Surjective π)
    (qK : PrimeSpectrum S_K) (d : ℕ) :
    let q := PrimeSpectrum.comap iSK qK
    let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
      MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
    PolynomialPresentationAtPrime.kernelGeneratedByCondition π q d ↔
      PolynomialPresentationAtPrime.kernelGeneratedByCondition πK qK d := by
  intro q πK
  let β : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) K :=
    MvPolynomial.mapAlgHom (σ := Fin n) (Algebra.ofId k K)
  have hprime :
      PrimeSpectrum.comap β.toRingHom (PolynomialPresentationAtPrime.prime πK qK) =
        PolynomialPresentationAtPrime.prime π q := by
    -- Proof comment: the base-change square identifies the two localized presentation primes.
    simpa [πK, β] using baseChangePresentation_prime_comap (K := K) π qK
  have hIdealPrime :
      (PolynomialPresentationAtPrime.prime π q).asIdeal =
        (PolynomialPresentationAtPrime.prime πK qK).asIdeal.comap β.toRingHom := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hprime.symm
  let φ : PolynomialPresentationAtPrime.localRing π q →+*
      PolynomialPresentationAtPrime.localRing πK qK :=
    Localization.localRingHom
      (PolynomialPresentationAtPrime.prime π q).asIdeal
      (PolynomialPresentationAtPrime.prime πK qK).asIdeal β.toRingHom hIdealPrime
  have hmap :
      Ideal.map φ (PolynomialPresentationAtPrime.localizedKernelIdeal π q) =
        PolynomialPresentationAtPrime.localizedKernelIdeal πK qK := by
    -- Proof comment: reduce both localized kernels to maps of the downstairs kernel and compare
    -- the resulting ring homomorphisms by the computation rule for `Localization.localRingHom`.
    unfold PolynomialPresentationAtPrime.localizedKernelIdeal
    rw [Ideal.map_map]
    rw [tensorBaseChangePolynomialAlgHom_ker_local (K := K) π hπ]
    rw [Ideal.map_map]
    apply congrArg
      (fun f : MvPolynomial (Fin n) k →+* PolynomialPresentationAtPrime.localRing πK qK =>
        Ideal.map f (RingHom.ker π.toRingHom))
    apply RingHom.ext
    intro x
    exact Localization.localRingHom_to_map
      (PolynomialPresentationAtPrime.prime π q).asIdeal
      (PolynomialPresentationAtPrime.prime πK qK).asIdeal β.toRingHom hIdealPrime x
  constructor
  · intro hqGen
    -- Proof comment: the ascent direction is formal once the localized kernel is identified as
    -- the image ideal under the localized coefficient-extension map.
    exact ideal_generators_map_of_generators φ hmap hqGen
  · intro hqKGen
    -- Proof comment: the reverse direction descends the generator count along the flat local
    -- homomorphism between the two localized presentation rings.
    let R := PolynomialPresentationAtPrime.localRing π q
    let T := PolynomialPresentationAtPrime.localRing πK qK
    let I : Ideal R := PolynomialPresentationAtPrime.localizedKernelIdeal π q
    let J : Ideal T := PolynomialPresentationAtPrime.localizedKernelIdeal πK qK
    letI : Algebra R T := φ.toAlgebra
    have hβflat : β.toRingHom.Flat := by
      -- Proof comment: coefficient extension on polynomial rings is flat, read as flatness of
      -- the associated ring homomorphism.
      have hmod : Module.Flat (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K) := by
        simpa [β] using mvPolynomialFieldExtension_moduleFlat_local (k := k) (K := K) (n := n)
      have halgFlat :
          (algebraMap (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) K)).Flat :=
        (RingHom.flat_algebraMap_iff).2 hmod
      simpa [β] using halgFlat
    have hφflat : φ.Flat := by
      -- Proof comment: localizing the flat polynomial coefficient map at the corresponding
      -- presentation primes preserves flatness.
      simpa [φ] using
        (RingHom.Flat.localRingHom hβflat
          (PolynomialPresentationAtPrime.prime πK qK).asIdeal
          (PolynomialPresentationAtPrime.prime π q).asIdeal hIdealPrime)
    letI : Module.Flat R T := by
      have hAlgFlat : (algebraMap R T).Flat := by
        simpa [R, T, RingHom.algebraMap_toAlgebra] using hφflat
      exact (RingHom.flat_algebraMap_iff).1 hAlgFlat
    letI : IsLocalHom (algebraMap R T) := by
      -- Proof comment: the algebra map is definitionally the canonical local homomorphism `φ`.
      have hφlocal : IsLocalHom φ := by
        simpa [φ] using
          (Localization.isLocalHom_localRingHom
            (I := (PolynomialPresentationAtPrime.prime π q).asIdeal)
            (J := (PolynomialPresentationAtPrime.prime πK qK).asIdeal)
            (f := β.toRingHom) hIdealPrime)
      simpa [R, T, RingHom.algebraMap_toAlgebra] using hφlocal
    letI : Module.Finite R I := by
      -- Proof comment: over the noetherian localized polynomial ring, every ideal is a finite
      -- module.
      rw [Module.Finite.iff_fg]
      exact I.fg_of_isNoetherianRing
    have hIJ : Ideal.map (algebraMap R T) I = J := by
      -- Proof comment: rewrite the already-proved localized-kernel image equality from `φ` to
      -- the algebra-map spelling expected by the descent helper.
      simpa [R, T, I, J, RingHom.algebraMap_toAlgebra] using hmap
    exact ideal_generators_descend_of_flatLocal_map_eq I J hIJ (by simpa [J] using hqKGen)

/-- Helper for Chap10 Lemma 10 135 10: the basic-open global complete-intersection condition is
preserved and reflected at corresponding primes after tensoring by a field extension. -/
private theorem isGlobalCompleteIntersectionNearPrime_baseChange_iff
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    isGlobalCompleteIntersectionNearPrime k q ↔
      isGlobalCompleteIntersectionNearPrime K qK := by
  let q := PrimeSpectrum.comap iSK qK
  -- Route correction: the old direct neighbourhood-descent route was too broad. We choose one
  -- finite polynomial presentation and compare only its tensor base change via the presentation
  -- TFAE.
  obtain ⟨n, π, hπ⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := k) (S := S)).mp inferInstance
  let πK : MvPolynomial (Fin n) K →ₐ[K] S_K :=
    MvPolynomial.aeval fun i ↦ (1 : K) ⊗ₜ[k] π (MvPolynomial.X i)
  have hπK : Function.Surjective πK := by
    -- Proof comment: the selected presentation stays surjective after tensoring with `K`.
    simpa [πK] using tensorBaseChangePolynomialAlgHom_surjective_local (K := K) π hπ
  obtain ⟨d, hd, hdK⟩ :=
    baseChangedPresentation_commonHeightDefect_local (K := K) π hπ qK
  have hDownTFAE := PolynomialPresentationAtPrime.tfae π hπ q hd
  have hUpTFAE := PolynomialPresentationAtPrime.tfae πK hπK qK hdK
  have hGenerators :=
    kernelGeneratedByCondition_iff_baseChangedPresentation
      (K := K) π hπ qK d
  constructor
  · intro hq
    -- Proof comment: convert the downstairs neighbourhood condition to the plain generator-count
    -- clause, transport that smaller condition, then return through the upstairs TFAE.
    have hqGen : PolynomialPresentationAtPrime.kernelGeneratedByCondition π q d :=
      (hDownTFAE.out 0 1 rfl rfl).mp hq
    exact (hUpTFAE.out 1 0 rfl rfl).mp (hGenerators.mp hqGen)
  · intro hqK
    -- Proof comment: the reverse implication reflects the generator-count clause and lets the
    -- downstairs TFAE recover the global-near-prime condition.
    have hqKGen :
        PolynomialPresentationAtPrime.kernelGeneratedByCondition πK qK d :=
      (hUpTFAE.out 0 1 rfl rfl).mp hqK
    exact (hDownTFAE.out 1 0 rfl rfl).mp (hGenerators.mpr hqKGen)

/- Domain-style sampling pass.

Primary domain: local complete intersections under tensor base change along a field extension.

Sampled owner declarations:
* `IsCompleteIntersectionOver`;
* `completeIntersectionOver_atPrime_tfae`;
* `cohenMacaulay_localizationAtPrime_iff_of_tensorProduct_fieldExtension`;
* `Algebra.isSmoothAt_iff_isSmoothAt_tensor_fieldExtension`.

Best owner abstraction: the public statement should stay directly on the canonical local owner
`IsCompleteIntersectionOver` for the localized rings. The contraction `PrimeSpectrum.comap iSK qK`
is bridge/view data induced by the tensor-product owner map `iSK`; it should not be repackaged as
an extra local `abbrev`.

Primitive vs. derived:
* primitive data: the finite type `k`-algebra `S`, the extension field `K`, and the upstairs prime
  `qK : PrimeSpectrum S_K`;
* derived API: the downstairs prime `PrimeSpectrum.comap iSK qK` and the local-ring comparison
  theorem below.

Source/core/bridge triage:
* `source-facing`: invariance of the complete-intersection condition on the local rings at a prime
  under the base change `S ↦ K ⊗[k] S`;
* `core/canonical`: `IsCompleteIntersectionOver` on the two local rings;
* `bridge/view`: the contraction `PrimeSpectrum.comap iSK qK`.
-/

-- Proof sketch: use Lemma `10.135.8` to characterize complete intersections at a prime by the
-- presentation-theoretic criterion of Lemma `10.135.4`. After base change from `k` to `K`, the
-- relevant codimension is unchanged by Lemma `10.116.6`, and the minimal number of generators of
-- the localized defining ideal is preserved by the residue-field comparison and Nakayama's lemma.
/-- Chap10 Lemma 10 135 10: for a field extension `K / k`, a finite type `k`-algebra `S`, and a prime
`qK` of `K ⊗[k] S` with corresponding prime `q` of `S`, the local ring `S_q` is a complete
intersection over `k` if and only if the local ring `(K ⊗[k] S)_{qK}` is a complete intersection
over `K`. -/
@[stacks 00SI]
theorem isCompleteIntersectionOver_atPrime_iff_of_tensorProduct_fieldExtension
    (qK : PrimeSpectrum S_K) :
    let q := PrimeSpectrum.comap iSK qK
    IsCompleteIntersectionOver k (Localization.AtPrime q.asIdeal) ↔
      IsCompleteIntersectionOver K (Localization.AtPrime qK.asIdeal) := by
  let q := PrimeSpectrum.comap iSK qK
  -- Proof comment: Lemma 10.135.8 identifies complete-intersection local rings with the
  -- existence of a global complete-intersection basic neighbourhood at the prime.
  have hDownTFAE := completeIntersectionOver_atPrime_tfae (k := k) (S := S) q
  have hUpTFAE := completeIntersectionOver_atPrime_tfae (k := K) (S := S_K) qK
  have hNear := isGlobalCompleteIntersectionNearPrime_baseChange_iff (K := K) (S := S) qK
  constructor
  · intro hq
    -- Proof comment: move downstairs complete intersections to a downstairs global
    -- neighbourhood, base-change that neighbourhood, then return through the upstairs TFAE.
    have hqNear : isGlobalCompleteIntersectionNearPrime k q :=
      (hDownTFAE.out 0 2 rfl rfl).mp hq
    exact (hUpTFAE.out 2 0 rfl rfl).mp (hNear.mp hqNear)
  · intro hqK
    -- Proof comment: the reverse implication uses the reflected basic-neighbourhood condition
    -- and the same TFAE bridge at the contracted prime.
    have hqKNear : isGlobalCompleteIntersectionNearPrime K qK :=
      (hUpTFAE.out 0 2 rfl rfl).mp hqK
    exact (hDownTFAE.out 2 0 rfl rfl).mp (hNear.mpr hqKNear)

end
