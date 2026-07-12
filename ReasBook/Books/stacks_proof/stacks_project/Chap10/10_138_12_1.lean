import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.Extension

universe u v w

noncomputable section

section

variable {R : Type u} {S : Type v} {ι : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable (I : Ideal R)
variable [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S]

/- Domain triage:
* primary domain: cotangent/conormal sequences for surjective polynomial presentations, after
  base change along the quotient map `S → S ⧸ IS`;
* sampled owner declarations:
  - `Algebra.Extension.cotangentComplex`;
  - `Algebra.Extension.toKaehler`;
  - `Algebra.Extension.formallySmooth_iff_split_injection`;
  - `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`;
* best owner abstraction: the extension-level presentation
  `P[hSurj] : Algebra.Extension R S` coming from the surjection `MvPolynomial ι R → S`;
* primitive data: the quotient algebra `S̄ = S ⧸ IS` and the owner maps
  `P[hSurj].cotangentComplex`, `P[hSurj].toKaehler`;
* derived API: the base-changed maps `LinearMap.baseChange S̄ ...`;
* layer triage:
  - `source-facing`: the conormal sequence modulo `I`;
  - `core/canonical`: the presentation-level owners `cotangentComplex` and `toKaehler`;
  - `bridge/view`: quotienting/base-changing those owner maps along `S → S̄`. -/

local notation "S̄" => S ⧸ Ideal.map (algebraMap R S) I

/-- Helper for 10.138.12.1: the quotient-to-tensor target equivalence sends the class of `s` to
the pure tensor `1 ⊗ s`. -/
theorem quotient_target_tensor_apply_mk (s : S) :
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
        (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) s) =
      (1 : R ⧸ I) ⊗ₜ[R] s := by
  -- This is the defining formula of the quotient-to-tensor comparison.
  simpa using
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk (A := R) (B := S) (I := I) s)

/-- Helper for 10.138.12.1: formal smoothness of `S / IS` transports across the canonical
quotient-to-tensor algebra equivalence. -/
theorem quotient_target_tensor_formallySmooth
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) S̄) :
    Algebra.FormallySmooth (R ⧸ I) ((R ⧸ I) ⊗[R] S) := by
  -- The target tensor model is canonically isomorphic to the quotient algebra `S / IS`.
  let eS : S̄ ≃ₐ[R ⧸ I] ((R ⧸ I) ⊗[R] S) :=
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  letI : Algebra.FormallySmooth (R ⧸ I) S̄ := hSmooth
  exact Algebra.FormallySmooth.of_equiv eS

/-- Helper for 10.138.12.1: the quotient polynomial presentation
`MvPolynomial ι (R ⧸ I) → S ⧸ IS` induced from the original map
`MvPolynomial ι R → S`. -/
noncomputable def quotientPolynomialAlgHom :
    MvPolynomial ι (R ⧸ I) →ₐ[R ⧸ I] S̄ :=
  (MvPolynomial.aeval fun i ↦
      algebraMap S S̄ ((algebraMap (MvPolynomial ι R) S) (MvPolynomial.X i)))

/-- Helper for 10.138.12.1: surjectivity of the quotient polynomial presentation is inherited from
the original surjective presentation after reducing coefficients modulo `I`. -/
theorem quotientPolynomialAlgHom_surjective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    Function.Surjective (quotientPolynomialAlgHom (R := R) (S := S) (ι := ι) I) := by
  -- The quotient presentation factors the composite
  -- `MvPolynomial ι R → S → S̄`, and both maps in that composite are surjective.
  have hcomp :
      (quotientPolynomialAlgHom (R := R) (S := S) (ι := ι) I).toRingHom.comp
          (MvPolynomial.map (Ideal.Quotient.mkₐ R I).toRingHom) =
        (algebraMap S S̄).comp (algebraMap (MvPolynomial ι R) S) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa [MvPolynomial.algebraMap_eq] using
        (IsScalarTower.algebraMap_apply R (MvPolynomial ι R) S̄ r)
    · intro i
      simp [quotientPolynomialAlgHom]
  intro x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨p, rfl⟩ := hSurj s
  refine ⟨MvPolynomial.map (Ideal.Quotient.mkₐ R I).toRingHom p, ?_⟩
  -- Evaluate the factorization identity on the chosen polynomial preimage.
  exact RingHom.congr_fun hcomp p

-- Proof sketch: the unquotiented cotangent complex is a complex, so
-- `toKaehler.comp cotangentComplex = 0`; after base change to `S / IS`, the same relation holds
-- for the induced maps.
/-- The two base-changed maps in the conormal sequence compose to zero. -/
theorem polynomialConormalSequenceModuloIdeal_comp_eq_zero
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    (LinearMap.baseChange S̄ P.toKaehler).comp
        (LinearMap.baseChange S̄ P.cotangentComplex) =
      0 := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  -- Base change preserves the vanishing composite from the unquotiented conormal sequence.
  have hcomp : P.toKaehler.comp P.cotangentComplex = 0 :=
    Function.Exact.linearMap_comp_eq_zero P.exact_cotangentComplex_toKaehler
  calc
    (LinearMap.baseChange S̄ P.toKaehler).comp (LinearMap.baseChange S̄ P.cotangentComplex)
      = LinearMap.baseChange S̄ (P.toKaehler.comp P.cotangentComplex) := by
          simpa using
            (LinearMap.baseChange_comp
              (A := S̄) (f := P.cotangentComplex) (g := P.toKaehler)).symm
    _ = 0 := by
      simpa [hcomp]

-- Proof sketch: the unquotiented map `P ⊗[P] Ω[P⁄R] → Ω[S⁄R]` is surjective for a surjective
-- polynomial presentation, and base change along `S → S / IS` preserves surjectivity.
/-- The right map in the base-changed conormal sequence is surjective. -/
theorem polynomialBaseChangedKaehlerDifferentialToKaehlerModuloIdeal_surjective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Surjective (LinearMap.baseChange S̄ P.toKaehler) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  -- Tensoring on the left with `S̄` preserves surjectivity of the owner map `P.toKaehler`.
  change Function.Surjective (LinearMap.baseChange S̄ P.toKaehler)
  rw [LinearMap.baseChange_eq_ltensor]
  exact LinearMap.lTensor_surjective S̄ P.toKaehler_surjective

/-- Helper for 10.138.12.1: tensoring the owner conormal sequence with `S̄ = S/IS` preserves the
right-exact part of the sequence. -/
theorem polynomialConormalSequenceModuloIdeal_exact
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Exact
      (LinearMap.baseChange S̄ P.cotangentComplex)
      (LinearMap.baseChange S̄ P.toKaehler) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  -- Right exactness of tensor product gives the exactness at the middle term after quotienting by
  -- `IS`.
  change Function.Exact
    (LinearMap.baseChange S̄ P.cotangentComplex)
    (LinearMap.baseChange S̄ P.toKaehler)
  rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
  exact lTensor_exact S̄ P.exact_cotangentComplex_toKaehler P.toKaehler_surjective

/-- Helper for 10.138.12.1: formal smoothness of the quotient polynomial presentation gives a
split injection on its cotangent complex. -/
theorem quotient_polynomial_presentation_split_injection
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) S̄) :
    let f : MvPolynomial ι (R ⧸ I) →ₐ[R ⧸ I] S̄ :=
      quotientPolynomialAlgHom (R := R) (S := S) (ι := ι) I
    let Qbar : Algebra.Extension (R ⧸ I) S̄ :=
      Algebra.Extension.ofSurjective f
        (quotientPolynomialAlgHom_surjective (R := R) (S := S) (ι := ι) (I := I) hSurj)
    ∃ τ : Qbar.CotangentSpace →ₗ[S̄] Qbar.Cotangent,
        τ.comp Qbar.cotangentComplex = LinearMap.id := by
  let f : MvPolynomial ι (R ⧸ I) →ₐ[R ⧸ I] S̄ :=
    quotientPolynomialAlgHom (R := R) (S := S) (ι := ι) I
  have hfSurj : Function.Surjective f :=
    quotientPolynomialAlgHom_surjective (R := R) (S := S) (ι := ι) (I := I) hSurj
  let Qbar : Algebra.Extension (R ⧸ I) S̄ :=
    Algebra.Extension.ofSurjective f hfSurj
  let _ : Algebra.FormallySmooth (R ⧸ I) Qbar.Ring := by
    change Algebra.FormallySmooth (R ⧸ I) (MvPolynomial ι (R ⧸ I))
    infer_instance
  -- The quotient-side presentation is formally smooth, so its cotangent complex splits.
  exact (Algebra.Extension.formallySmooth_iff_split_injection Qbar).mp hSmooth

/-- Helper for 10.138.12.1: after transporting the quotient target to the tensor model
`(R ⧸ I) ⊗[R] S`, the genuinely base-changed polynomial presentation has injective cotangent
complex. -/
theorem polynomial_baseChange_presentation_cotangentComplex_injective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) S̄) :
    let G : Algebra.Generators R S ι :=
      Algebra.Generators.ofAlgHom
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex) := by
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  letI : Algebra.FormallySmooth (R ⧸ I) ((R ⧸ I) ⊗[R] S) :=
    quotient_target_tensor_formallySmooth (R := R) (S := S) (I := I) hSmooth
  letI : Algebra.FormallySmooth (R ⧸ I) ((G.baseChange (T := R ⧸ I)).toExtension.Ring) := by
    change Algebra.FormallySmooth (R ⧸ I) (MvPolynomial ι (R ⧸ I))
    infer_instance
  -- The base-changed polynomial ring is formally smooth over `R ⧸ I`, so injectivity is
  -- equivalent to vanishing of `H¹`, which follows from formal smoothness of the target tensor
  -- model.
  exact ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex_injective_iff).2
    Algebra.FormallySmooth.subsingleton_h1Cotangent

omit [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S] in
/-- Helper for 10.138.12.1: the canonical map from the actual base-changed polynomial extension to
the polynomial extension with base-changed coefficients is a left inverse to its reverse map. -/
theorem polynomial_baseChange_extension_to_from
    (G : Algebra.Generators R S ι) :
    (G.baseChangeToBaseChange (R ⧸ I)).comp (G.baseChangeFromBaseChange (R ⧸ I)) =
      .id (G.toExtension.baseChange (T := R ⧸ I)) := by
  -- The two extension maps are induced by the algebra equivalence
  -- `MvPolynomial.algebraTensorAlgEquiv`, so their composite is the identity.
  ext x
  change
    (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm
        ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)) x) = x
  exact (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm_apply_apply x

omit [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S] in
/-- Helper for 10.138.12.1: the reverse canonical map from the polynomial extension with
base-changed coefficients back to the actual base-changed polynomial extension is a left inverse
to the forward map. -/
theorem polynomial_baseChange_extension_from_to
    (G : Algebra.Generators R S ι) :
    (G.baseChangeFromBaseChange (R ⧸ I)).comp (G.baseChangeToBaseChange (R ⧸ I)) =
      .id ((G.baseChange (T := R ⧸ I)).toExtension) := by
  -- The reverse composite is the identity on the polynomial ring with coefficients in `R ⧸ I`.
  ext x
  change
    (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I))
        ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm x) = x
  exact (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).apply_symm_apply x

/-- Helper for 10.138.12.1: injectivity of the cotangent complex transfers from the canonical
base-changed polynomial presentation to the actual base-changed owner extension. -/
theorem polynomial_baseChange_extension_cotangentComplex_injective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) S̄) :
    let G : Algebra.Generators R S ι :=
      Algebra.Generators.ofAlgHom
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex) := by
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  -- First normalize the statement to the chosen generator family `G`.
  change Function.Injective ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex)
  let f := G.baseChangeFromBaseChange (R ⧸ I)
  let g := G.baseChangeToBaseChange (R ⧸ I)
  have hfg :
      g.comp f = .id (G.toExtension.baseChange (T := R ⧸ I)) :=
    polynomial_baseChange_extension_to_from (I := I) G
  have hPresentationInj :
      Function.Injective ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex) := by
    -- The source-faithful polynomial presentation already gives injectivity after base change.
    simpa [G] using
    polynomial_baseChange_presentation_cotangentComplex_injective
      (R := R) (S := S) (ι := ι) (I := I) hSurj hSmooth
  intro x y hxy
  -- Map the equality across the canonical comparison to the base-changed presentation.
  have hmap :
      ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex)
          (Algebra.Extension.Cotangent.map f x) =
        ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex)
          (Algebra.Extension.Cotangent.map f y) := by
    calc
      ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex)
          (Algebra.Extension.Cotangent.map f x)
        = Algebra.Extension.CotangentSpace.map f
            ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex x) := by
            symm
            exact LinearMap.congr_fun
              (Algebra.Extension.CotangentSpace.map_comp_cotangentComplex f) x
      _ = Algebra.Extension.CotangentSpace.map f
            ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex y) := by
            rw [hxy]
      _ = ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex)
            (Algebra.Extension.Cotangent.map f y) := by
            exact LinearMap.congr_fun
              (Algebra.Extension.CotangentSpace.map_comp_cotangentComplex f) y
  have hmap_eq :
      Algebra.Extension.Cotangent.map f x = Algebra.Extension.Cotangent.map f y :=
    hPresentationInj hmap
  have hcomp_apply (z : (G.toExtension.baseChange (T := R ⧸ I)).Cotangent) :
      Algebra.Extension.Cotangent.map g (Algebra.Extension.Cotangent.map f z) = z := by
    -- The pointwise composite on cotangent modules is the identity because `g.comp f = id`.
    calc
      Algebra.Extension.Cotangent.map g (Algebra.Extension.Cotangent.map f z)
        = Algebra.Extension.Cotangent.map (g.comp f) z := by
            simpa using
              LinearMap.congr_fun
                (Algebra.Extension.Cotangent.map_comp
                  (P := G.toExtension.baseChange (T := R ⧸ I))
                  (P' := (G.baseChange (T := R ⧸ I)).toExtension)
                  (P'' := G.toExtension.baseChange (T := R ⧸ I))
                  f g) z |>.symm
      _ = Algebra.Extension.Cotangent.map (.id (G.toExtension.baseChange (T := R ⧸ I))) z := by
            rw [hfg]
      _ = z := by simp
  -- Apply the inverse comparison map to recover equality in the original cotangent module.
  calc
    x = (Algebra.Extension.Cotangent.map g) (Algebra.Extension.Cotangent.map f x) := by
          symm
          exact hcomp_apply x
    _ = (Algebra.Extension.Cotangent.map g) (Algebra.Extension.Cotangent.map f y) := by
          rw [hmap_eq]
    _ = y := by
          exact hcomp_apply y

/-- Helper for 10.138.12.1: the explicit owner presentation
`Algebra.Extension.ofSurjective (algebraMap (MvPolynomial ι R) S)` has the same base-changed
cotangent-complex injectivity as the generator presentation built from the same surjective map. -/
theorem polynomial_owner_baseChange_extension_cotangentComplex_injective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) S̄) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective ((P.baseChange (T := R ⧸ I)).cotangentComplex) := by
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  change Function.Injective ((P.baseChange (T := R ⧸ I)).cotangentComplex)
  have hGeneratorInj :
      Function.Injective ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex) := by
    -- The generator presentation already has injective cotangent complex after genuine base
    -- change.
    simpa [G] using
      polynomial_baseChange_extension_cotangentComplex_injective
        (R := R) (S := S) (ι := ι) (I := I) hSurj hSmooth
  have hUnderlying :
      IsScalarTower.toAlgHom R P.Ring S = IsScalarTower.toAlgHom R G.toExtension.Ring S := by
    -- The explicit owner and generator presentation come from the same polynomial algebra map.
    change
      IsScalarTower.toAlgHom R (MvPolynomial ι R) S =
        MvPolynomial.aeval (fun j ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X j))
    ext i
    simp
  have hBaseChangeTarget :
      IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    ext x
    change
      Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R P.Ring S) x =
        Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R G.toExtension.Ring S) x
    rw [hUnderlying]
    rfl
  have hForward :
      (IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S)).comp
          (AlgHom.id (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    -- Both actual base-changed extensions are built from the same tensor-polynomial algebra map.
    simpa using hBaseChangeTarget
  have hBackward :
      (IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
            ((R ⧸ I) ⊗[R] S)).comp
          (AlgHom.id (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring) =
        IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) := by
    -- The reverse identity comparison is the same equality read in the opposite direction.
    simpa using hBaseChangeTarget.symm
  let f : (G.toExtension.baseChange (T := R ⧸ I)).Hom (P.baseChange (T := R ⧸ I)) :=
    .ofAlgHom (AlgHom.id _ _) hForward
  let g : (P.baseChange (T := R ⧸ I)).Hom (G.toExtension.baseChange (T := R ⧸ I)) :=
    .ofAlgHom (AlgHom.id _ _) hBackward
  let e :
      (G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent ≃ₗ[((R ⧸ I) ⊗[R] S)]
        (P.baseChange (T := R ⧸ I)).H1Cotangent :=
    Algebra.Extension.H1Cotangent.equiv f g
  have hGeneratorSub :
      Subsingleton ((G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent) :=
    (Algebra.Extension.subsingleton_h1Cotangent
      (G.toExtension.baseChange (T := R ⧸ I))).mpr hGeneratorInj
  have hOwnerSub :
      Subsingleton ((P.baseChange (T := R ⧸ I)).H1Cotangent) := by
    -- `H¹` is presentation-independent, so the owner and generator base changes vanish together.
    refine ⟨fun x y ↦ ?_⟩
    apply e.symm.injective
    exact hGeneratorSub.elim _ _
  -- Vanishing of `H¹` is equivalent to injectivity of the cotangent complex.
  exact (Algebra.Extension.subsingleton_h1Cotangent
    (P.baseChange (T := R ⧸ I))).mp hOwnerSub

omit [Algebra (MvPolynomial ι R) S] [IsScalarTower R (MvPolynomial ι R) S] in
/-- Helper for 10.138.12.1: injectivity of the cotangent complex transfers from the actual
base-changed polynomial extension to the polynomial presentation with coefficients reduced
modulo `I`. -/
theorem polynomial_baseChange_presentation_injective_of_extension_injective
    (G : Algebra.Generators R S ι) :
    Function.Injective ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex) →
      Function.Injective ((G.baseChange (T := R ⧸ I)).toExtension.cotangentComplex) := by
  intro hExtensionInj
  let f := G.baseChangeFromBaseChange (R ⧸ I)
  let g := G.baseChangeToBaseChange (R ⧸ I)
  let e :
      (G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent ≃ₗ[((R ⧸ I) ⊗[R] S)]
        ((G.baseChange (T := R ⧸ I)).toExtension.H1Cotangent) :=
    Algebra.Extension.H1Cotangent.equiv f g
  have hExtensionSub :
      Subsingleton ((G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent) :=
    (Algebra.Extension.subsingleton_h1Cotangent
      (G.toExtension.baseChange (T := R ⧸ I))).mpr hExtensionInj
  have hPresentationSub :
      Subsingleton (((G.baseChange (T := R ⧸ I)).toExtension).H1Cotangent) := by
    -- The canonical polynomial comparison maps induce an equivalence on `H¹`.
    refine ⟨fun x y ↦ ?_⟩
    apply e.symm.injective
    exact hExtensionSub.elim _ _
  -- We convert the `H¹`-vanishing statement back to injectivity of the cotangent complex.
  exact (Algebra.Extension.subsingleton_h1Cotangent
    ((G.baseChange (T := R ⧸ I)).toExtension)).mp hPresentationSub

/-- Helper for 10.138.12.1: once the canonical base-change map on the owner presentation is known
to be injective, the displayed base change of `P.cotangentComplex` is injective by the standard
tensor reassociation and the owner cotangent identification. -/
theorem owner_baseChange_injective_of_cotangentComplexBaseChange_injective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective (KaehlerDifferential.cotangentComplexBaseChange R S P.Ring S̄) →
      Function.Injective (LinearMap.baseChange S̄ P.cotangentComplex) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  dsimp
  intro hcanonical
  -- The owner-level base change is exactly the canonical map up to invertible transport on the
  -- source and target tensor factors.
  change Function.Injective (P.cotangentComplex.baseChange S̄)
  rw [P.lTensor_cotangentComplex_eq_cotangentComplexBaseChange (A := S̄)]
  exact
    (TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ Ω[P.Ring⁄R]).symm.injective.comp <|
      hcanonical.comp <|
        (((TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ P.ker).symm ≪≫ₗ
          P.cotangentEquiv.baseChange (A := S̄)).symm.injective)

/-- Helper for 10.138.12.1: for the owner presentation `P`, injectivity of the canonical
base-change cotangent-complex map is equivalent to injectivity of the displayed base change of
`P.cotangentComplex`. -/
theorem cotangentComplexBaseChange_injective_iff_owner_baseChange_injective
    (P : Algebra.Extension R S) :
    Function.Injective (KaehlerDifferential.cotangentComplexBaseChange R S P.Ring S̄) ↔
      Function.Injective (LinearMap.baseChange S̄ P.cotangentComplex) := by
  constructor
  · -- The forward implication is the standard owner transport already isolated above.
    intro hcanonical
    rw [P.lTensor_cotangentComplex_eq_cotangentComplexBaseChange (A := S̄)]
    exact
      (TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ Ω[P.Ring⁄R]).symm.injective.comp <|
        hcanonical.comp <|
          (((TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ P.ker).symm ≪≫ₗ
            P.cotangentEquiv.baseChange (A := S̄)).symm.injective)
  · -- The reverse implication is the same conjugation formula read from right to left.
    intro hbase
    rw [P.cotangentComplexBaseChange_eq_lTensor_cotangentComplex (A := S̄)]
    exact
      (TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ Ω[P.Ring⁄R]).injective.comp <|
        hbase.comp <|
          ((TensorProduct.AlgebraTensorModule.cancelBaseChange P.Ring S S̄ S̄ P.ker).symm ≪≫ₗ
            P.cotangentEquiv.baseChange (A := S̄)).injective

/-- Helper for 10.138.12.1: injectivity transfers across a commuting square whose horizontal maps
are linear equivalences. -/
theorem injective_of_linearEquiv_conj
    {A : Type*} [CommRing A]
    {M N M' N' : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
    [Module A M] [Module A N] [Module A M'] [Module A N']
    (eM : M ≃ₗ[A] M') (eN : N ≃ₗ[A] N')
    (f : M →ₗ[A] N) (g : M' →ₗ[A] N')
    (hcomm : eN.toLinearMap.comp f = g.comp eM.toLinearMap)
    (hg : Function.Injective g) :
    Function.Injective f := by
  -- Apply the commuting square and use injectivity after transporting to the conjugate map `g`.
  intro x y hxy
  apply eM.injective
  apply hg
  calc
    g (eM x) = eN (f x) := by
      simpa using (LinearMap.congr_fun hcomm x).symm
    _ = eN (f y) := by rw [hxy]
    _ = g (eM y) := by
      simpa using LinearMap.congr_fun hcomm y

/-- Helper for 10.138.12.1: injectivity of the cotangent complex for the genuinely base-changed
explicit owner extension already implies injectivity for the coefficient-basechanged polynomial
presentation. -/
theorem polynomial_owner_baseChange_presentation_cotangentComplex_injective_of_owner_extension_injective
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    Function.Injective
        (((Algebra.Extension.ofSurjective
            (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj).baseChange
            (T := R ⧸ I)).cotangentComplex) →
      Function.Injective
        (((Algebra.Generators.ofAlgHom
            (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj).baseChange
            (T := R ⧸ I)).toExtension.cotangentComplex) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  intro hbaseChangeExtensionInj
  have hUnderlying :
      IsScalarTower.toAlgHom R P.Ring S = IsScalarTower.toAlgHom R G.toExtension.Ring S := by
    -- The explicit owner and generator models are induced by the same polynomial algebra map.
    change
      IsScalarTower.toAlgHom R (MvPolynomial ι R) S =
        MvPolynomial.aeval (fun j ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X j))
    ext i
    simp
  have hBaseChangeTarget :
      IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    -- The two actual base changes have the same target algebra map after identifying the source
    -- polynomial algebras.
    ext x
    change
      Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R P.Ring S) x =
        Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R G.toExtension.Ring S) x
    rw [hUnderlying]
    rfl
  have hGeneratorExtensionInj :
      Function.Injective ((G.toExtension.baseChange (T := R ⧸ I)).cotangentComplex) := by
    have hForward :
        (IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S)).comp
            (AlgHom.id (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring) =
          IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
            ((R ⧸ I) ⊗[R] S) := by
      -- The forward comparison is the shared tensor-polynomial target map.
      simpa using hBaseChangeTarget
    have hBackward :
        (IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
              ((R ⧸ I) ⊗[R] S)).comp
            (AlgHom.id (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring) =
          IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) := by
      -- The reverse comparison is the same identity read in the opposite direction.
      simpa using hBaseChangeTarget.symm
    let f : (G.toExtension.baseChange (T := R ⧸ I)).Hom (P.baseChange (T := R ⧸ I)) :=
      .ofAlgHom (AlgHom.id _ _) hForward
    let g : (P.baseChange (T := R ⧸ I)).Hom (G.toExtension.baseChange (T := R ⧸ I)) :=
      .ofAlgHom (AlgHom.id _ _) hBackward
    let e :
        (G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent ≃ₗ[((R ⧸ I) ⊗[R] S)]
          (P.baseChange (T := R ⧸ I)).H1Cotangent :=
      Algebra.Extension.H1Cotangent.equiv f g
    have hOwnerSub :
        Subsingleton ((P.baseChange (T := R ⧸ I)).H1Cotangent) :=
      (Algebra.Extension.subsingleton_h1Cotangent
        (P.baseChange (T := R ⧸ I))).mpr hbaseChangeExtensionInj
    have hGeneratorSub :
        Subsingleton ((G.toExtension.baseChange (T := R ⧸ I)).H1Cotangent) := by
      -- The `H¹` comparison transports the input injectivity back to the generator model.
      refine ⟨fun x y ↦ ?_⟩
      apply e.injective
      exact hOwnerSub.elim _ _
    exact (Algebra.Extension.subsingleton_h1Cotangent
      (G.toExtension.baseChange (T := R ⧸ I))).mp hGeneratorSub
  -- The already-settled generator/presentation comparison finishes the injectivity transfer.
  exact polynomial_baseChange_presentation_injective_of_extension_injective
    (R := R) (S := S) (I := I) G hGeneratorExtensionInj

/-- Helper for 10.138.12.1: the actual base changes of the explicit owner and generator
presentations induce the same tensor-polynomial target map. -/
theorem polynomial_owner_baseChange_target_maps_eq
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    let G : Algebra.Generators R S ι :=
      Algebra.Generators.ofAlgHom
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) =
      IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
        ((R ⧸ I) ⊗[R] S) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  have hUnderlying :
      IsScalarTower.toAlgHom R P.Ring S = IsScalarTower.toAlgHom R G.toExtension.Ring S := by
    -- The explicit owner and generator presentation come from the same polynomial algebra map.
    change
      IsScalarTower.toAlgHom R (MvPolynomial ι R) S =
        MvPolynomial.aeval (fun j ↦ algebraMap (MvPolynomial ι R) S (MvPolynomial.X j))
    ext i
    simp
  have hBaseChangeTarget :
      IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    -- After actual base change, both presentations still induce the same tensor-polynomial map.
    ext x
    change
      Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R P.Ring S) x =
        Algebra.TensorProduct.map (AlgHom.id (R ⧸ I) (R ⧸ I))
          (IsScalarTower.toAlgHom R G.toExtension.Ring S) x
    rw [hUnderlying]
    rfl
  exact hBaseChangeTarget

/-- Helper for 10.138.12.1: the actual base-changed explicit owner presentation and the
coefficient-basechanged polynomial presentation are linked by inverse extension homomorphisms. -/
theorem owner_baseChange_presentation_hom_pair
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    let G : Algebra.Generators R S ι :=
      Algebra.Generators.ofAlgHom
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    ∃ f : (P.baseChange (T := R ⧸ I)).Hom ((G.baseChange (T := R ⧸ I)).toExtension),
      ∃ g : ((G.baseChange (T := R ⧸ I)).toExtension).Hom (P.baseChange (T := R ⧸ I)),
        g.comp f = .id (P.baseChange (T := R ⧸ I)) ∧
          f.comp g = .id ((G.baseChange (T := R ⧸ I)).toExtension) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  let G : Algebra.Generators R S ι :=
    Algebra.Generators.ofAlgHom
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  have hBaseChangeTarget :
      IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    -- The explicit owner and generator models agree on the actual tensor-polynomial target map.
    simpa [P, G] using
      polynomial_owner_baseChange_target_maps_eq
        (R := R) (S := S) (ι := ι) (I := I) hSurj
  have hf0 :
      (IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
            ((R ⧸ I) ⊗[R] S)).comp
          (AlgHom.id (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring) =
        IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S) := by
    -- The forward identity map is well-defined because the target algebra maps coincide.
    simpa using hBaseChangeTarget.symm
  have hg0 :
      (IsScalarTower.toAlgHom (R ⧸ I) (P.baseChange (T := R ⧸ I)).Ring ((R ⧸ I) ⊗[R] S)).comp
          (AlgHom.id (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring) =
        IsScalarTower.toAlgHom (R ⧸ I) (G.toExtension.baseChange (T := R ⧸ I)).Ring
          ((R ⧸ I) ⊗[R] S) := by
    -- The reverse identity map is the same comparison read backwards.
    simpa using hBaseChangeTarget
  let f0 : (P.baseChange (T := R ⧸ I)).Hom (G.toExtension.baseChange (T := R ⧸ I)) :=
    .ofAlgHom (AlgHom.id _ _) hf0
  let g0 : (G.toExtension.baseChange (T := R ⧸ I)).Hom (P.baseChange (T := R ⧸ I)) :=
    .ofAlgHom (AlgHom.id _ _) hg0
  let f : (P.baseChange (T := R ⧸ I)).Hom ((G.baseChange (T := R ⧸ I)).toExtension) :=
    (G.baseChangeFromBaseChange (R ⧸ I)).comp f0
  let g : ((G.baseChange (T := R ⧸ I)).toExtension).Hom (P.baseChange (T := R ⧸ I)) :=
    g0.comp (G.baseChangeToBaseChange (R ⧸ I))
  refine ⟨f, g, ?_, ?_⟩
  · -- The owner-side round-trip is the identity on the tensor-polynomial source ring.
    ext x
    change
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm
          ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)) x) = x
    exact (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm_apply_apply x
  · -- The presentation-side round-trip is the reverse identity.
    ext x
    change
      (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I))
          ((MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).symm x) = x
    exact (MvPolynomial.algebraTensorAlgEquiv (σ := ι) R (R ⧸ I)).apply_symm_apply x

/-- Helper for Chap10 10 138 12 1: a split injective linear map remains injective after
extension of scalars. -/
theorem baseChange_injective_of_splitInjection
    {A M N : Type*} [Semiring A] [Algebra S A]
    [AddCommMonoid M] [AddCommMonoid N] [Module S M] [Module S N]
    (f : M →ₗ[S] N) (g : N →ₗ[S] M) (hgf : g.comp f = LinearMap.id) :
    Function.Injective (LinearMap.baseChange A f) := by
  -- Base change preserves the displayed left inverse.
  have hbaseComp :
      (LinearMap.baseChange A g).comp (LinearMap.baseChange A f) = LinearMap.id := by
    calc
      (LinearMap.baseChange A g).comp (LinearMap.baseChange A f)
          = LinearMap.baseChange A (g.comp f) := by
              simpa using
                (LinearMap.baseChange_comp (A := A) (f := f) (g := g)).symm
      _ = LinearMap.baseChange A (LinearMap.id : M →ₗ[S] M) := by
            rw [hgf]
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (A := A) (M := M) (R := S))
  -- Applying the base-changed left inverse reduces equality to the original elements.
  intro x y hxy
  calc
    x = ((LinearMap.baseChange A g).comp (LinearMap.baseChange A f)) x := by
          simpa using (LinearMap.congr_fun hbaseComp x).symm
    _ = ((LinearMap.baseChange A g).comp (LinearMap.baseChange A f)) y := by
          simp [LinearMap.comp_apply, hxy]
    _ = y := by
          simpa using LinearMap.congr_fun hbaseComp y

/-- Helper for Chap10 10 138 12 1: formal smoothness of the target splits the presentation
cotangent complex, and the split remains injective after base change. -/
theorem cotangentComplex_baseChange_injective_of_formallySmooth
    {A : Type*} [CommRing A] [Algebra S A]
    (P : Algebra.Extension R S) [Algebra.FormallySmooth R P.Ring]
    (hSmooth : Algebra.FormallySmooth R S) :
    Function.Injective (LinearMap.baseChange A P.cotangentComplex) := by
  -- Formal smoothness gives a left inverse for the presentation cotangent complex.
  obtain ⟨split, hsplit⟩ :=
    (Algebra.Extension.formallySmooth_iff_split_injection P).mp hSmooth
  -- The linear-algebra helper transports that split through extension of scalars.
  exact baseChange_injective_of_splitInjection (A := A) P.cotangentComplex split hsplit

-- Proof sketch: in the source this displayed sequence is used inside Lemma 10.138.12 under
-- `I^2 = 0` and flatness of `R → S`. Formal smoothness of the quotient gives the quotient-side
-- splitting, while flatness identifies the reduced conormal source `J/(IJ + J^2)` with the
-- displayed owner base change.
/-- Chap10 10 138 12 1: under the hypotheses of Lemma 10.138.12, if the quotient map
`R ⧸ I → S ⧸ IS` is formally smooth, then for a surjective polynomial presentation
`P = MvPolynomial ι R → S` the base-changed conormal sequence
`0 → J / (I J + J²) → Ω[P⁄R] ⊗[P] S / IS → Ω[S⁄R] ⊗[S] S / IS → 0`
is exact; in Lean the three terms are represented by the quotiented conormal module, the
quotiented cotangent-space term, and the base change of `Ω[S⁄R]`. -/
theorem polynomial_presentation_conormal_sequence_mod_ideal
    [Module.Flat R S]
    (hSurj : Function.Surjective (algebraMap (MvPolynomial ι R) S))
    (_hI_square_zero : I * I = ⊥)
    (hSmooth : Algebra.FormallySmooth (R ⧸ I) (S ⧸ Ideal.map (algebraMap R S) I)) :
    let P : Algebra.Extension R S :=
      Algebra.Extension.ofSurjective
        (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
    Function.Injective
        (LinearMap.baseChange S̄ P.cotangentComplex) ∧
      Function.Exact
        (LinearMap.baseChange S̄ P.cotangentComplex)
        (LinearMap.baseChange S̄ P.toKaehler) := by
  let P : Algebra.Extension R S :=
    Algebra.Extension.ofSurjective
      (IsScalarTower.toAlgHom R (MvPolynomial ι R) S) hSurj
  refine ⟨?_, polynomialConormalSequenceModuloIdeal_exact (I := I) hSurj⟩
  have hSq : I ^ 2 = ⊥ := by
    -- The source hypothesis is written multiplicatively; the quotient descent theorem uses
    -- powers of the kernel ideal.
    simpa [pow_two] using _hI_square_zero
  have hsurjR : Function.Surjective (algebraMap R (R ⧸ I)) := by
    -- Quotient maps are surjective.
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  have hsurjS : Function.Surjective (algebraMap S S̄) := by
    -- The target quotient map is also surjective.
    simpa using
      (Ideal.Quotient.mk_surjective :
        Function.Surjective (Ideal.Quotient.mk (Ideal.map (algebraMap R S) I)))
  have hKer :
      RingHom.ker (algebraMap S S̄) =
        (RingHom.ker (algebraMap R (R ⧸ I))).map (algebraMap R S) := by
    -- The kernel of `S → S/IS` is the extension of the kernel of `R → R/I`.
    simp
  have hKerSq : (RingHom.ker (algebraMap R (R ⧸ I))) ^ 2 = ⊥ := by
    -- Re-express square-zero in the kernel notation expected by the descent theorem.
    simpa using hSq
  have hFormalSmooth : Algebra.FormallySmooth R S :=
    Algebra.FormallySmooth.of_surjective_of_ker_eq_map_of_flat
      hsurjR hsurjS hKer hKerSq hSmooth
  have hPresentationSmooth : Algebra.FormallySmooth R P.Ring := by
    -- The chosen presentation ring is a polynomial algebra, hence formally smooth.
    change Algebra.FormallySmooth R (MvPolynomial ι R)
    infer_instance
  letI : Algebra.FormallySmooth R P.Ring := hPresentationSmooth
  -- After descending formal smoothness to `S`, split the owner cotangent complex before base
  -- changing to `S/IS`.
  exact cotangentComplex_baseChange_injective_of_formallySmooth (A := S̄) P hFormalSmooth

end
