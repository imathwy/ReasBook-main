import Mathlib
import StacksProject_2024.Chap10.Lemma_10_52_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ModuleCat Polynomial
open IsLocalRing
open scoped BigOperators TensorProduct

universe u v w

/- Domain triage:
- primary domain: finite-length `R`-modules equipped with an endomorphism, viewed canonically as
  `R[X]`-modules;
- sampled owner API:
  `Module.compHom`,
  `IsFiniteLength`,
  `CompositionSeries.factor`,
  `Module.length_compositionSeries`,
  `LinearMap.det_eq_det_mul_det`;
- `source-facing`: the filtration-defined determinant, trace, and characteristic polynomial of an
  endomorphism `φ : Module.End R M` of a finite-length `R`-module `M`;
- `core/canonical`: `CompositionSeries (Submodule R[X] M)` after endowing `M` with the
  `R[X]`-module structure coming from `aeval φ`;
- `bridge/view`: the residue-field base change of the `X`-action on each simple `R[X]`-module
  factor, together with the short-exact-sequence comparison lemmas for determinant, trace, and
  characteristic polynomial.
-/

variable {R : Type u} [CommRing R]

namespace Module.End

variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem isNoetherian_of_isFiniteLength (hM : IsFiniteLength R M) :
    IsNoetherian R M :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1

private theorem isArtinian_of_isFiniteLength (hM : IsFiniteLength R M) :
    IsArtinian R M :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).2

namespace CompositionSeries

/-- Helper for Lemma 15.121.1: Jordan-Hölder for submodule composition series, repackaged directly
as factorwise linear equivalences. -/
theorem jordan_holder_factors_linearEquiv
    {A : Type u} [CommRing A] {N : Type v} [AddCommGroup N] [Module A N]
    (F G : CompositionSeries (Submodule A N))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤) (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤) :
    ∃ σ : Fin F.length ≃ Fin G.length,
        ∀ i : Fin F.length,
          Nonempty (F.factor i ≃ₗ[A] G.factor (σ i)) := by
  -- Route correction: use the owner theorem on the module lattice directly, avoiding the
  -- categorical wrapper that caused the earlier import/interface drift.
  obtain ⟨σ, hσ⟩ := F.jordan_holder G (hF₀.trans hG₀.symm) (hF₁.trans hG₁.symm)
  refine ⟨σ, fun i ↦ ?_⟩
  -- The Jordan-Hölder `Equivalent` relation already records linear equivalences of the factors.
  simpa [CompositionSeries.factor] using hσ i

end CompositionSeries

/-- View `(M, φ)` as an `R[X]`-module via the algebra map sending `X` to `φ`. -/
abbrev toPolynomialModule (φ : Module.End R M) : Module R[X] M :=
  Module.compHom M (aeval φ).toRingHom

/-- A `φ`-stable composition series of submodules of `M` from `⊥` to `⊤`, implemented canonically
as a composition series of `R[X]`-submodules of `M`. -/
abbrev StableCompositionSeries (φ : Module.End R M) :=
  let _ : Module R[X] M := φ.toPolynomialModule
  { s : CompositionSeries (Submodule R[X] M) // s.head = ⊥ ∧ s.last = ⊤ }

namespace StableCompositionSeries

variable {φ : Module.End R M}

@[simp] theorem head_eq_bot (s : StableCompositionSeries φ) : s.1.head = ⊥ :=
  s.2.1

@[simp] theorem last_eq_top (s : StableCompositionSeries φ) : s.1.last = ⊤ :=
  s.2.2

/-- The endomorphism induced on the `i`-th simple factor by the `X`-action on the canonical
`R[X]`-module attached to `(M, φ)`. -/
private noncomputable def factorMap (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    s.1.factor i →ₗ[R] s.1.factor i :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  { toFun := fun x ↦ X • x
    map_add' := by
      intro x y
      exact smul_add (X : R[X]) x y
    map_smul' := by
      intro a x
      change
        (X : R[X]) • (((C : R →+* R[X]) a) • x) =
          ((C : R →+* R[X]) a) • ((X : R[X]) • x)
      rw [smul_smul, smul_smul, mul_comm] }

section LocalRing

variable [IsLocalRing R]

local notation "κ" => ResidueField R

/-- Helper for Lemma 15.121.1: the maximal-ideal residue field of a local ring identifies with the
canonical local residue field. -/
private noncomputable abbrev maximalIdeal_residueField_equiv :
    (maximalIdeal R).ResidueField ≃+* κ :=
  (RingEquiv.ofBijective
    (algebraMap κ (maximalIdeal R).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))).symm

/-- Helper for Lemma 15.121.1: under the maximal-ideal residue-field identification, the ideal
quotient class of `a` is the usual local residue class. -/
private theorem maximalIdeal_residueField_equiv_apply_algebraMap
    (a : R) :
    maximalIdeal_residueField_equiv (algebraMap R (maximalIdeal R).ResidueField a) =
      IsLocalRing.residue R a := by
  -- Both residue-field models receive the same class of `a`.
  rw [show algebraMap R (maximalIdeal R).ResidueField a =
      algebraMap κ (maximalIdeal R).ResidueField (IsLocalRing.residue R a) by rfl]
  exact maximalIdeal_residueField_equiv.apply_symm_apply (IsLocalRing.residue R a)

/-- Helper for Lemma 15.121.1: the zero ideal is not maximal in `K[X]` over any field `K`. -/
private theorem polynomial_bot_not_isMaximal_field
    (K : Type*) [Field K] :
    ¬ (⊥ : Ideal K[X]).IsMaximal := by
  intro hbot
  have hspan_ne_top : Ideal.span ({(X : K[X])} : Set K[X]) ≠ ⊤ := by
    intro htop
    have hmem : (1 : K[X]) ∈ Ideal.span ({(X : K[X])} : Set K[X]) := by
      simpa [htop]
    have hXunit : IsUnit (X : K[X]) := by
      exact isUnit_of_dvd_one (Ideal.mem_span_singleton.mp hmem)
    have hdeg : ((X : K[X]).degree = 0) := Polynomial.isUnit_iff_degree_eq_zero.mp hXunit
    simpa using hdeg
  have hspan_eq_bot :
      Ideal.span ({(X : K[X])} : Set K[X]) = (⊥ : Ideal K[X]) :=
    (hbot.eq_of_le hspan_ne_top bot_le).symm
  have hXmem : (X : K[X]) ∈ (⊥ : Ideal K[X]) := by
    rw [← hspan_eq_bot]
    exact Ideal.mem_span_singleton_self (X : K[X])
  simpa using hXmem

/-- Helper for Lemma 15.121.1: the zero ideal is not maximal in `κ[X]`, witnessed by the
nontrivial principal ideal generated by `X`. -/
private theorem polynomial_bot_not_isMaximal :
    ¬ (⊥ : Ideal κ[X]).IsMaximal := by
  -- Specialize the generic field argument to the local residue field.
  exact polynomial_bot_not_isMaximal_field κ

/-- Helper for Lemma 15.121.1: the standard `R`-module structure on `R[X] ⧸ J` agrees with the
explicit one obtained by restricting scalars along `R → R[X] → R[X] ⧸ J`. -/
private noncomputable abbrev polynomial_quotient_compHom_linearEquiv
    (J : Ideal R[X]) :
    let _ : Module R (R[X] ⧸ J) :=
      Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
    (R[X] ⧸ J) ≃ₗ[R] (R[X] ⧸ J) :=
  let _ : Module R (R[X] ⧸ J) :=
    Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
  { toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro a x
      rfl }

/-- Helper for Lemma 15.121.1: the algebra-module structure on `κ ⊗[R] N` agrees with the usual
left tensor action by `κ`. -/
private noncomputable abbrev residueFieldTensor_algebra_linearEquiv
    (N : Type*) [AddCommGroup N] [Module R N] [CommRing N] [Algebra R N] :
    let _ : Module κ (κ ⊗[R] N) := Algebra.toModule
    (κ ⊗[R] N) ≃ₗ[κ] (κ ⊗[R] N) :=
  let _ : Module κ (κ ⊗[R] N) := Algebra.toModule
  { toFun := id
    invFun := id
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := by
      intro a x
      rfl }

/-- Helper for Lemma 15.121.1: tensoring the quotient identity equivalence upgrades the standard
right-factor `R`-module structure on `R[X] ⧸ J` to the explicit `Module.compHom` structure used in
the theorem statement. -/
private noncomputable abbrev residueFieldTensor_polynomialQuotient_compHom_linearEquiv
    (J : Ideal R[X]) :
    let _ : Module R (R[X] ⧸ J) :=
      Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
    (κ ⊗[R] (R[X] ⧸ J)) ≃ₗ[κ] (κ ⊗[R] (R[X] ⧸ J)) :=
  let _ : Module R (R[X] ⧸ J) :=
    Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
  -- Base change preserves the identity quotient equivalence, so only the scalar-action wrapper
  -- changes here.
  LinearEquiv.baseChange R κ (R[X] ⧸ J) (R[X] ⧸ J)
    (polynomial_quotient_compHom_linearEquiv (R := R) J)

/-- Helper for Lemma 15.121.1: transport finite dimensionality on the fiber across the residue-field
ring equivalence before comparing the fiber with the tensor model. -/
private theorem finiteDimensional_fiber_compHom_of_residueField_equiv
    (J : Ideal R[X])
    (eκ : (maximalIdeal R).ResidueField ≃ₐ[R] κ)
    (hfiber : FiniteDimensional (maximalIdeal R).ResidueField
      ((maximalIdeal R).Fiber (R[X] ⧸ J))) :
    let _ : Module κ ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
      Module.compHom _ eκ.symm.toRingHom
    FiniteDimensional κ ((maximalIdeal R).Fiber (R[X] ⧸ J)) := by
  let _ : Module κ ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
    Module.compHom _ eκ.symm.toRingHom
  let b :
      Module.Basis
        (Basis.ofVectorSpaceIndex (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J)))
        (maximalIdeal R).ResidueField
        ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
    Basis.ofVectorSpace (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J))
  -- Route correction: transport the basis coefficients first, so the field change is handled
  -- independently of the later tensor-model comparison.
  let bκ :
      Module.Basis
        (Basis.ofVectorSpaceIndex (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J)))
        κ
        ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
    b.mapCoeffs eκ.toRingEquiv fun c x => by
      change (eκ.symm (eκ c)) • x = c • x
      simp
  -- A transported basis over the equivalent field gives the desired finite-dimensional structure.
  exact Module.Basis.finiteDimensional_of_finite bκ

/-- Helper for Lemma 15.121.1: package the canonical fiber/tensor comparison as a `κ`-linear
equivalence after freezing the pulled-back scalar action on the fiber. -/
private noncomputable abbrev fiber_to_residueFieldTensor_linearEquiv
    (J : Ideal R[X])
    (eκ : (maximalIdeal R).ResidueField ≃ₐ[R] κ) :
    let _ : Module κ ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
      Module.compHom _ eκ.symm.toRingHom
    ((maximalIdeal R).Fiber (R[X] ⧸ J)) ≃ₗ[κ] (κ ⊗[R] (R[X] ⧸ J)) :=
  let _ : Module κ ((maximalIdeal R).Fiber (R[X] ⧸ J)) :=
    Module.compHom _ eκ.symm.toRingHom
  let eTensor :
      (maximalIdeal R).Fiber (R[X] ⧸ J) ≃ₐ[R] (κ ⊗[R] (R[X] ⧸ J)) :=
    Algebra.TensorProduct.congr eκ (AlgEquiv.refl : (R[X] ⧸ J) ≃ₐ[R] (R[X] ⧸ J))
  -- `Ideal.Fiber` is already a tensor product, so the comparison is the tensor congruence on the
  -- residue-field factor, viewed as a `κ`-linear equivalence via the pulled-back scalar action.
  { toFun := eTensor
    invFun := eTensor.symm
    left_inv := eTensor.left_inv
    right_inv := eTensor.right_inv
    map_add' := eTensor.map_add
    map_smul' := by
      intro a x
      change eTensor ((eκ.symm a) • x) = a • eTensor x
      rw [Algebra.smul_def, Algebra.smul_def]
      have hmul :
          eTensor
              ((algebraMap (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J)))
                  (eκ.symm a) * x) =
            eTensor
                ((algebraMap (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J)))
                  (eκ.symm a)) * eTensor x := by
        simpa using
          eTensor.map_mul
            ((algebraMap (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J)))
              (eκ.symm a)) x
      rw [hmul]
      have hscalar :
          eTensor (algebraMap (maximalIdeal R).ResidueField ((maximalIdeal R).Fiber (R[X] ⧸ J))
            (eκ.symm a)) =
            algebraMap κ (κ ⊗[R] (R[X] ⧸ J)) a := by
        simp [eTensor]
      rw [hscalar] }

/-- Helper for Lemma 15.121.1: once the fiber is finite-dimensional, the canonical residue-field
tensor model is finite-dimensional for the exact module structures used later in the proof. -/
private theorem finiteDimensional_residueFieldTensor_of_fiber_equiv
    (J : Ideal R[X])
    (eκ : (maximalIdeal R).ResidueField ≃ₐ[R] κ)
    (hfiber : FiniteDimensional (maximalIdeal R).ResidueField
      ((maximalIdeal R).Fiber (R[X] ⧸ J))) :
    let _ : Module R (R[X] ⧸ J) :=
      Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
    FiniteDimensional κ (κ ⊗[R] (R[X] ⧸ J)) := by
  -- TODO: finish the last transport from the tensor model to the explicit `Module.compHom`
  -- structure without triggering instance search on the target module structure.
  sorry

/-- Helper for Lemma 15.121.1: after base change to the residue field, the quotient of `R[X]` by a
maximal ideal becomes a finite-dimensional `κ`-vector space. -/
private theorem residueFieldTensor_polynomialQuotientByMaximal_finiteDimensional
    (J : Ideal R[X]) (hJ : J.IsMaximal) :
    let _ : Module R (R[X] ⧸ J) :=
      Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
    FiniteDimensional κ (κ ⊗[R] (R[X] ⧸ J)) := by
  let k₀ := (maximalIdeal R).ResidueField
  let φ : R[X] →ₐ[R] (R[X] ⧸ J) := Ideal.Quotient.mkₐ R J
  have hφ : Function.Surjective φ := Ideal.Quotient.mkₐ_surjective R J
  let eFiber :
      (maximalIdeal R).Fiber (R[X] ⧸ J) ≃ₐ[k₀]
        k₀[X] ⧸ ((RingHom.ker (φ : R[X] →+* R[X] ⧸ J)).map
          (mapRingHom (algebraMap R k₀))) :=
    Polynomial.fiberEquivQuotient φ hφ (maximalIdeal R)
  obtain ⟨p, hpJ, hpSpan⟩ :=
    Ideal.exists_mem_span_singleton_map_residueField_eq (maximalIdeal R) J
  have hp_ne_zero : p.map (algebraMap R k₀) ≠ 0 := by
    intro hp_zero
    have hmap_eq_bot :
        J.map (mapRingHom (algebraMap R k₀)) = (⊥ : Ideal k₀[X]) := by
      rw [← hpSpan, hp_zero]
      simp
    have hmap_ne_top : J.map (mapRingHom (algebraMap R k₀)) ≠ (⊤ : Ideal k₀[X]) := by
      rw [hmap_eq_bot]
      exact bot_ne_top
    have hmap_max :
        (J.map (mapRingHom (algebraMap R k₀))).IsMaximal :=
      (Ideal.map_eq_top_or_isMaximal_of_surjective
        (f := mapRingHom (algebraMap R k₀))
        (hf := Polynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective (maximalIdeal R)))
        hJ).resolve_left hmap_ne_top
    exact polynomial_bot_not_isMaximal_field k₀ (hmap_eq_bot ▸ hmap_max)
  have hquot :
      FiniteDimensional k₀
        (k₀[X] ⧸ ((RingHom.ker (φ : R[X] →+* R[X] ⧸ J)).map
          (mapRingHom (algebraMap R k₀)))) := by
    -- Replace the mapped ideal by a principal generator and then use the canonical power basis of
    -- the polynomial quotient.
    rw [Ideal.Quotient.mkₐ_ker, ← hpSpan]
    let _ : Module.Finite k₀ (AdjoinRoot (p.map (algebraMap R k₀))) :=
      (AdjoinRoot.powerBasis hp_ne_zero).finite
    simpa [AdjoinRoot] using
      (inferInstance : FiniteDimensional k₀ (AdjoinRoot (p.map (algebraMap R k₀))))
  have hfiber :
      FiniteDimensional k₀ ((maximalIdeal R).Fiber (R[X] ⧸ J)) := by
    -- Transport finite dimensionality across the owner fiber/quotient equivalence.
    simpa using eFiber.symm.toLinearEquiv.finiteDimensional
  let eκ :
      k₀ ≃ₐ[R] κ :=
    AlgEquiv.ofRingEquiv (f := maximalIdeal_residueField_equiv)
      maximalIdeal_residueField_equiv_apply_algebraMap
  let eTensor :
      (maximalIdeal R).Fiber (R[X] ⧸ J) ≃ₐ[R] (κ ⊗[R] (R[X] ⧸ J)) :=
    Algebra.TensorProduct.congr eκ (AlgEquiv.refl : (R[X] ⧸ J) ≃ₐ[R] (R[X] ⧸ J))
  let _ : Module R (R[X] ⧸ J) :=
    Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
  -- Route correction: the scalar-change transport on the fiber is handled separately from the
  -- tensor-model comparison, so the final proof is a flat assembly of the named adapters.
  exact finiteDimensional_residueFieldTensor_of_fiber_equiv (R := R) J eκ hfiber

/-- Each simple `R[X]`-factor contributes a finite-dimensional residue-field vector space after
base change along `R → κ`. -/
private noncomputable instance factorFiniteDimensional
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    FiniteDimensional κ (κ ⊗[R] s.1.factor i) := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  let J : Ideal R[X] := Module.annihilator R[X] (s.1.factor i)
  -- The simple factor is an `R[X]`-quotient by its maximal annihilator ideal.
  have hJ : J.IsMaximal := by
    simpa [J] using
      CompositionSeries.factor_annihilator_isMaximal (R := R[X]) (M := M) s.1 i
  let _ : Module R (R[X] ⧸ J) :=
    Module.compHom (R[X] ⧸ J) ((Ideal.Quotient.mk J).comp (C : R →+* R[X]))
  have hquot :
      FiniteDimensional κ (κ ⊗[R] (R[X] ⧸ J)) :=
    by
      simpa using
        residueFieldTensor_polynomialQuotientByMaximal_finiteDimensional (R := R) J hJ
  obtain ⟨e⟩ :=
    CompositionSeries.factor_isomorphic_quotient_annihilator (R := R[X]) (M := M) s.1 i
  let eR : s.1.factor i ≃ₗ[R] R[X] ⧸ J :=
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := by
        intro a x
        change e (((C : R →+* R[X]) a) • x) =
          (((Ideal.Quotient.mk J).comp (C : R →+* R[X])) a) • e x
        exact e.map_smulₛₗ ((C : R →+* R[X]) a) x }
  let eκ : κ ⊗[R] s.1.factor i ≃ₗ[κ] κ ⊗[R] (R[X] ⧸ J) :=
    LinearEquiv.baseChange R κ (s.1.factor i) (R[X] ⧸ J) eR
  -- Transport the finite-dimensional structure once across the base-change equivalence.
  let _ : FiniteDimensional κ (κ ⊗[R] (R[X] ⧸ J)) := hquot
  simpa using eκ.symm.finiteDimensional

/- Bridge/view: the endomorphism induced on the residue-field tensor module of the `i`-th simple
`R[X]`-factor. -/
private noncomputable abbrev factorResidueFieldMap
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
    κ ⊗[R] s.1.factor i →ₗ[κ] κ ⊗[R] s.1.factor i :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  (factorMap s i).baseChange κ

/-- Helper for Lemma 15.121.1: view an `R[X]`-linear factor equivalence as an `R`-linear
equivalence via the coefficient map `R → R[X]`. -/
private noncomputable def factor_restrictScalars_linearEquiv
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    s₀.1.factor i ≃ₗ[R] s₁.1.factor j :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro a x
      change e (((C : R →+* R[X]) a) • x) = ((C : R →+* R[X]) a) • e x
      exact e.map_smulₛₗ ((C : R →+* R[X]) a) x }

/-- Helper for Lemma 15.121.1: an `R[X]`-linear equivalence of composition factors conjugates the
raw `X`-action after restricting scalars to `R`. -/
theorem factorMap_conj_of_linearEquiv
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factorMap s₁ j =
      (factor_restrictScalars_linearEquiv e).toLinearMap ∘ₗ factorMap s₀ i ∘ₗ
        (factor_restrictScalars_linearEquiv e).symm.toLinearMap := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- Compare both linear maps on an arbitrary factor element and move the `X`-action across `e`.
  apply LinearMap.ext
  intro x
  change (X : R[X]) • x = e ((X : R[X]) • e.symm x)
  rw [e.map_smulₛₗ]
  simp

/-- Helper for Lemma 15.121.1: the factor comparison equivalence after residue-field base change. -/
private noncomputable def factor_baseChange_linearEquiv
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    κ ⊗[R] s₀.1.factor i ≃ₗ[κ] κ ⊗[R] s₁.1.factor j :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  LinearEquiv.baseChange R κ (s₀.1.factor i) (s₁.1.factor j)
    (factor_restrictScalars_linearEquiv (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e)

/-- Helper for Lemma 15.121.1: the base-changed factor equivalence sends pure tensors to pure
tensors. -/
theorem factor_baseChange_linearEquiv_apply_tmul
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) (a : κ)
    (x :
      let _ : Module R[X] M := φ.toPolynomialModule
      let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
      s₀.1.factor i) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factor_baseChange_linearEquiv e (a ⊗ₜ[R] x) = a ⊗ₜ[R] e x := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- The canonical base-change equivalence preserves pure tensors by the owner theorem.
  simpa [factor_baseChange_linearEquiv, factor_restrictScalars_linearEquiv] using
    (LinearEquiv.baseChange_tmul (R := R) (A := κ) (M := s₀.1.factor i) (N := s₁.1.factor j)
      (e := factor_restrictScalars_linearEquiv
        (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e) a x)

/-- Helper for Lemma 15.121.1: the residue-field endomorphisms on Jordan-Hölder matched factors
are linearly conjugate under the named base-change equivalence. -/
private theorem factorResidueFieldMap_conj_on_tmul
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j)
    (a : κ)
    (x :
      let _ : Module R[X] M := φ.toPolynomialModule
      let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
      s₀.1.factor i) :
    let _ : Module R[X] M := φ.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factorResidueFieldMap s₁ j (factor_baseChange_linearEquiv e (a ⊗ₜ[R] x)) =
      factor_baseChange_linearEquiv e (factorResidueFieldMap s₀ i (a ⊗ₜ[R] x)) := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- Normalize both sides on pure tensors so only the factor-level `X`-action remains.
  rw [factor_baseChange_linearEquiv_apply_tmul, factorResidueFieldMap,
    LinearMap.baseChange_tmul, factorResidueFieldMap, LinearMap.baseChange_tmul,
    factor_baseChange_linearEquiv_apply_tmul]
  -- Move the `X`-action across the `R[X]`-linear equivalence on the simple factors.
  let eR :
      s₀.1.factor i ≃ₗ[R] s₁.1.factor j :=
    factor_restrictScalars_linearEquiv
      (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e
  change a ⊗ₜ[R] factorMap s₁ j (eR x) = a ⊗ₜ[R] eR (factorMap s₀ i x)
  have hfactor : factorMap s₁ j (eR x) = eR (factorMap s₀ i x) := by
    rw [factorMap_conj_of_linearEquiv (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e]
    simp [eR]
  simpa using congrArg (fun y ↦ a ⊗ₜ[R] y) hfactor

/-- Helper for Lemma 15.121.1: the residue-field endomorphisms on Jordan-Hölder matched factors
are linearly conjugate under the named base-change equivalence. -/
private theorem factorResidueFieldMap_conj_of_factor_baseChange_linearEquiv
    {s₀ s₁ : StableCompositionSeries φ}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M := φ.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    factorResidueFieldMap s₁ j =
      (factor_baseChange_linearEquiv e).toLinearMap ∘ₗ factorResidueFieldMap s₀ i ∘ₗ
        (factor_baseChange_linearEquiv e).symm.toLinearMap := by
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  let eκ := factor_baseChange_linearEquiv
    (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e
  let map₀ := factorResidueFieldMap s₀ i
  let map₁ := factorResidueFieldMap s₁ j
  let lhs : κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j :=
    map₁ ∘ₗ eκ.toLinearMap
  let rhs : κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j :=
    eκ.toLinearMap ∘ₗ map₀
  -- Route correction: first record the tensor-level intertwining equality on pure tensors, and
  -- only then isolate the conjugacy statement by evaluating at `eκ.symm y`.
  have hintertwine : lhs = rhs := by
    -- Both tensor-product endomorphisms are determined by their values on pure tensors.
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [lhs, rhs]
    · intro a x
      simpa [lhs, rhs, map₀, map₁, eκ, LinearMap.comp_apply] using
        factorResidueFieldMap_conj_on_tmul
          (φ := φ) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e a x
    · intro z₁ z₂ hz₁ hz₂
      calc
        lhs (z₁ + z₂) = lhs z₁ + lhs z₂ := by simp [lhs]
        _ = rhs z₁ + rhs z₂ := by rw [hz₁, hz₂]
        _ = rhs (z₁ + z₂) := by simp [rhs]
  -- Evaluate the intertwining equality on `eκ.symm y` to rewrite the left-hand endomorphism.
  apply LinearMap.ext
  intro y
  have hy :=
    congrArg
      (fun f :
        κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j =>
          f (eκ.symm y))
      hintertwine
  simpa [lhs, rhs, map₀, map₁, eκ, LinearMap.comp_apply] using hy

/-- Helper for Lemma 15.121.1: view an `R[X]`-linear factor equivalence between two different
ambient endomorphisms as an `R`-linear equivalence via the coefficient map `R → R[X]`. -/
private noncomputable def factor_restrictScalars_linearEquiv_between
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M₀ := φ₀.toPolynomialModule
    let _ : Module R[X] M₁ := φ₁.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    s₀.1.factor i ≃ₗ[R] s₁.1.factor j :=
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  { toFun := e
    invFun := e.symm
    left_inv := e.left_inv
    right_inv := e.right_inv
    map_add' := e.map_add
    map_smul' := by
      intro a x
      change e (((C : R →+* R[X]) a) • x) = ((C : R →+* R[X]) a) • e x
      exact e.map_smulₛₗ ((C : R →+* R[X]) a) x }

/-- Helper for Lemma 15.121.1: an `R[X]`-linear equivalence between factors of two different
ambient endomorphisms conjugates the raw `X`-action after restricting scalars to `R`. -/
private theorem factorMap_conj_of_linearEquiv_between
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M₀ := φ₀.toPolynomialModule
    let _ : Module R[X] M₁ := φ₁.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factorMap (φ := φ₁) s₁ j =
      (factor_restrictScalars_linearEquiv_between (R := R) e).toLinearMap ∘ₗ
        factorMap (φ := φ₀) s₀ i ∘ₗ
        (factor_restrictScalars_linearEquiv_between (R := R) e).symm.toLinearMap := by
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- Compare both linear maps on an arbitrary factor element and move the `X`-action across `e`.
  apply LinearMap.ext
  intro x
  change (X : R[X]) • x = e ((X : R[X]) • e.symm x)
  rw [e.map_smulₛₗ]
  simp

/-- Helper for Lemma 15.121.1: base change the cross-ambient factor equivalence from `R` to the
residue field `κ`. -/
private noncomputable def factor_baseChange_linearEquiv_between
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    let _ : Module R[X] M₀ := φ₀.toPolynomialModule
    let _ : Module R[X] M₁ := φ₁.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    κ ⊗[R] s₀.1.factor i ≃ₗ[κ] κ ⊗[R] s₁.1.factor j :=
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  LinearEquiv.baseChange R κ (s₀.1.factor i) (s₁.1.factor j)
    (factor_restrictScalars_linearEquiv_between (R := R) e)

/-- Helper for Lemma 15.121.1: the cross-ambient base-changed factor equivalence sends pure
tensors to pure tensors. -/
private theorem factor_baseChange_linearEquiv_between_apply_tmul
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j)
    (a : κ)
    (x :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
      s₀.1.factor i) :
    let _ : Module R[X] M₀ := φ₀.toPolynomialModule
    let _ : Module R[X] M₁ := φ₁.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factor_baseChange_linearEquiv_between (R := R) e (a ⊗ₜ[R] x) = a ⊗ₜ[R] e x := by
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- The canonical base-change equivalence preserves pure tensors by the owner theorem.
  simpa [factor_baseChange_linearEquiv_between, factor_restrictScalars_linearEquiv_between] using
    (LinearEquiv.baseChange_tmul (R := R) (A := κ) (M := s₀.1.factor i) (N := s₁.1.factor j)
      (e := factor_restrictScalars_linearEquiv_between (R := R) e) a x)

/-- Helper for Lemma 15.121.1: the residue-field endomorphisms on cross-ambient matched factors
intertwine on pure tensors under the named base-change equivalence. -/
private theorem factorResidueFieldMap_conj_on_tmul_between
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j)
    (a : κ)
    (x :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
      s₀.1.factor i) :
    let _ : Module R[X] M₀ := φ₀.toPolynomialModule
    let _ : Module R[X] M₁ := φ₁.toPolynomialModule
    let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
    let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
    factorResidueFieldMap (φ := φ₁) s₁ j
        (factor_baseChange_linearEquiv_between (R := R) e (a ⊗ₜ[R] x)) =
      factor_baseChange_linearEquiv_between (R := R) e
        (factorResidueFieldMap (φ := φ₀) s₀ i (a ⊗ₜ[R] x)) := by
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  -- Normalize both sides on pure tensors so only the factor-level `X`-action remains.
  rw [factor_baseChange_linearEquiv_between_apply_tmul, factorResidueFieldMap,
    LinearMap.baseChange_tmul, factorResidueFieldMap, LinearMap.baseChange_tmul,
    factor_baseChange_linearEquiv_between_apply_tmul]
  -- Move the `X`-action across the cross-ambient `R[X]`-linear equivalence on the simple factors.
  let eR :
      s₀.1.factor i ≃ₗ[R] s₁.1.factor j :=
    factor_restrictScalars_linearEquiv_between (R := R) e
  change a ⊗ₜ[R] factorMap (φ := φ₁) s₁ j (eR x) =
    a ⊗ₜ[R] eR (factorMap (φ := φ₀) s₀ i x)
  have hfactor :
      factorMap (φ := φ₁) s₁ j (eR x) = eR (factorMap (φ := φ₀) s₀ i x) := by
    rw [factorMap_conj_of_linearEquiv_between (R := R) (φ₀ := φ₀) (φ₁ := φ₁)
      (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e]
    simp [eR]
  simpa using congrArg (fun y ↦ a ⊗ₜ[R] y) hfactor

/-- Helper for Lemma 15.121.1: the residue-field endomorphisms on cross-ambient matched factors
are linearly conjugate under the named base-change equivalence. -/
private theorem factorResidueFieldMap_conj_of_factor_baseChange_linearEquiv_between
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁]
    {φ₀ : Module.End R M₀} {φ₁ : Module.End R M₁}
    {s₀ : StableCompositionSeries φ₀} {s₁ : StableCompositionSeries φ₁}
    {i : Fin s₀.1.length} {j : Fin s₁.1.length}
    (e :
      let _ : Module R[X] M₀ := φ₀.toPolynomialModule
      let _ : Module R[X] M₁ := φ₁.toPolynomialModule
      s₀.1.factor i ≃ₗ[R[X]] s₁.1.factor j) :
    factorResidueFieldMap (φ := φ₁) s₁ j =
      (factor_baseChange_linearEquiv_between (R := R) e).toLinearMap ∘ₗ
        factorResidueFieldMap (φ := φ₀) s₀ i ∘ₗ
        (factor_baseChange_linearEquiv_between (R := R) e).symm.toLinearMap := by
  let _ : Module R[X] M₀ := φ₀.toPolynomialModule
  let _ : Module R[X] M₁ := φ₁.toPolynomialModule
  let _ : Module R (s₀.1.factor i) := Module.compHom (s₀.1.factor i) (C : R →+* R[X])
  let _ : Module R (s₁.1.factor j) := Module.compHom (s₁.1.factor j) (C : R →+* R[X])
  let eκ := factor_baseChange_linearEquiv_between (R := R) e
  let map₀ := factorResidueFieldMap (φ := φ₀) s₀ i
  let map₁ := factorResidueFieldMap (φ := φ₁) s₁ j
  let lhs : κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j :=
    map₁ ∘ₗ eκ.toLinearMap
  let rhs : κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j :=
    eκ.toLinearMap ∘ₗ map₀
  -- Route correction: establish the tensor-level intertwining equality first, then solve the
  -- conjugacy statement by evaluating at `eκ.symm y`.
  have hintertwine : lhs = rhs := by
    -- Both tensor-product endomorphisms are determined by their values on pure tensors.
    apply LinearMap.ext
    intro z
    refine TensorProduct.induction_on z ?_ ?_ ?_
    · simp [lhs, rhs]
    · intro a x
      simpa [lhs, rhs, map₀, map₁, eκ, LinearMap.comp_apply] using
        factorResidueFieldMap_conj_on_tmul_between
          (R := R) (φ₀ := φ₀) (φ₁ := φ₁) (s₀ := s₀) (s₁ := s₁) (i := i) (j := j) e a x
    · intro z₁ z₂ hz₁ hz₂
      calc
        lhs (z₁ + z₂) = lhs z₁ + lhs z₂ := by simp [lhs]
        _ = rhs z₁ + rhs z₂ := by rw [hz₁, hz₂]
        _ = rhs (z₁ + z₂) := by simp [rhs]
  -- Evaluate the intertwining equality on `eκ.symm y` to rewrite the left-hand endomorphism.
  apply LinearMap.ext
  intro y
  have hy :=
    congrArg
      (fun f :
        κ ⊗[R] s₀.1.factor i →ₗ[κ] κ ⊗[R] s₁.1.factor j =>
          f (eκ.symm y))
      hintertwine
  simpa [lhs, rhs, map₀, map₁, eκ, LinearMap.comp_apply] using hy

/-- The determinant contributed by the `i`-th simple `R[X]`-factor in a composition series. -/
private noncomputable def factorDet (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  (factorResidueFieldMap s i).det

/-- The trace contributed by the `i`-th simple `R[X]`-factor in a composition series. -/
private noncomputable def factorTrace (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  let _ : FiniteDimensional κ (κ ⊗[R] s.1.factor i) :=
    factorFiniteDimensional s i
  (LinearMap.trace κ (κ ⊗[R] s.1.factor i)) (factorResidueFieldMap s i)

/-- The characteristic polynomial contributed by the `i`-th simple `R[X]`-factor in a composition
series. -/
private noncomputable def factorCharpoly
    (s : StableCompositionSeries φ) (i : Fin s.1.length) :
    Polynomial κ :=
  let _ : Module R[X] M := φ.toPolynomialModule
  let _ : Module R (s.1.factor i) := Module.compHom (s.1.factor i) (C : R →+* R[X])
  let _ : FiniteDimensional κ (κ ⊗[R] s.1.factor i) :=
    factorFiniteDimensional s i
  (factorResidueFieldMap s i).charpoly

/-- The determinant attached to a chosen composition series is the product of the simple-factor
determinants. -/
noncomputable def det (s : StableCompositionSeries φ) :
    κ :=
  ∏ i : Fin s.1.length, factorDet s i

/-- The trace attached to a chosen composition series is the sum of the simple-factor traces. -/
noncomputable def trace (s : StableCompositionSeries φ) :
    κ :=
  ∑ i : Fin s.1.length, factorTrace s i

/-- The characteristic polynomial attached to a chosen composition series is the product of the
simple-factor characteristic polynomials. -/
noncomputable def charpoly (s : StableCompositionSeries φ) :
    Polynomial κ :=
  ∏ i : Fin s.1.length, factorCharpoly s i

end LocalRing

end StableCompositionSeries

section LocalRing

variable [IsLocalRing R]

local notation "κ" => ResidueField R

/-- Helper for Lemma 15.121.1: transported bases identify linearly conjugate endomorphisms with
the same trace. -/
private theorem det_eq_of_linearEquiv_conj
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    [AddCommGroup W] [Module κ W] [FiniteDimensional κ W]
    (f : V →ₗ[κ] V) (g : W →ₗ[κ] W) (e : V ≃ₗ[κ] W)
    (hconj : g = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) :
    LinearMap.det g = LinearMap.det f := by
  classical
  let ι := Module.Free.ChooseBasisIndex κ V
  let b : Module.Basis ι κ V := Module.Free.chooseBasis κ V
  -- Transport a basis of `V` across `e` so that the conjugate endomorphism has the same matrix.
  have hmatrix : LinearMap.toMatrix (b.map e) (b.map e) g = LinearMap.toMatrix b b f := by
    rw [hconj]
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.map_apply]
  -- Equal matrices in transported bases give equal determinants.
  rw [← LinearMap.det_toMatrix (b.map e) g, hmatrix, LinearMap.det_toMatrix b f]

/-- Helper for Lemma 15.121.1: transported bases identify linearly conjugate endomorphisms with
the same trace. -/
private theorem trace_eq_of_linearEquiv_conj
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    [AddCommGroup W] [Module κ W] [FiniteDimensional κ W]
    (f : V →ₗ[κ] V) (g : W →ₗ[κ] W) (e : V ≃ₗ[κ] W)
    (hconj : g = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) :
    LinearMap.trace κ W g = LinearMap.trace κ V f := by
  classical
  let ι := Module.Free.ChooseBasisIndex κ V
  let b : Module.Basis ι κ V := Module.Free.chooseBasis κ V
  -- Transport a basis of `V` across `e` so that the conjugate endomorphism has the same matrix.
  have hmatrix : LinearMap.toMatrix (b.map e) (b.map e) g = LinearMap.toMatrix b b f := by
    rw [hconj]
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.map_apply]
  -- Equal matrices in transported bases give equal traces.
  rw [LinearMap.trace_eq_matrix_trace κ (b.map e) g, hmatrix,
    LinearMap.trace_eq_matrix_trace κ b f]

/-- Helper for Lemma 15.121.1: transported bases identify linearly conjugate endomorphisms with
the same characteristic polynomial. -/
private theorem charpoly_eq_of_linearEquiv_conj
    {V : Type v} {W : Type w}
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
    [AddCommGroup W] [Module κ W] [FiniteDimensional κ W]
    (f : V →ₗ[κ] V) (g : W →ₗ[κ] W) (e : V ≃ₗ[κ] W)
    (hconj : g = e.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearMap) :
    g.charpoly = f.charpoly := by
  classical
  let ι := Module.Free.ChooseBasisIndex κ V
  let b : Module.Basis ι κ V := Module.Free.chooseBasis κ V
  -- Transport a basis of `V` across `e` so that the conjugate endomorphism has the same matrix.
  have hmatrix : LinearMap.toMatrix (b.map e) (b.map e) g = LinearMap.toMatrix b b f := by
    rw [hconj]
    ext i j
    simp [LinearMap.toMatrix_apply, Module.Basis.map_apply]
  -- Equal matrices in transported bases give equal characteristic polynomials.
  rw [← LinearMap.charpoly_toMatrix g (b.map e), hmatrix, LinearMap.charpoly_toMatrix f b]

variable {φ : Module.End R M}
section FiniteLength

variable [IsNoetherian R M] [IsArtinian R M]

/- Proof sketch: view `(M, φ)` as an `R[X]`-module. Since every `R[X]`-submodule is in particular
an `R`-submodule, finite length over `R` gives both noetherianity and artinianity after
restriction of scalars, so `isFiniteLength_iff_exists_compositionSeries` supplies a composition
series from `⊥` to `⊤`. -/
/-- A finite-length `R`-module with endomorphism admits a `φ`-stable composition series. -/
private theorem nonempty_stableCompositionSeries
    (φ : Module.End R M) :
    Nonempty (StableCompositionSeries φ) := by
  let _ : Module R[X] M := φ.toPolynomialModule
  -- Coefficients act through `Polynomial.C`, so the induced `R`-action matches the original one.
  letI : IsScalarTower R R[X] M := IsScalarTower.of_algebraMap_smul fun r m ↦ by
    change ((((aeval φ).toRingHom) ((C : R →+* R[X]) r)) : Module.End R M) m = r • m
    simp
  -- Restrict scalars from `R[X]` to `R` to inherit the finite-length hypotheses.
  letI : IsNoetherian R[X] M := isNoetherian_of_tower R (inferInstance : IsNoetherian R M)
  letI : IsArtinian R[X] M := isArtinian_of_tower R (inferInstance : IsArtinian R M)
  have hfinite : IsFiniteLength R[X] M := by
    exact (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)
  -- The canonical composition-series existence theorem now applies in the `R[X]`-submodule lattice.
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfinite
  exact ⟨⟨s, h₀, h₁⟩⟩

-- Proof sketch: any two composition series in the `R[X]`-submodule lattice of the polynomial
-- module attached to `(M, φ)` are Jordan-Hölder equivalent, and isomorphic simple factors
-- contribute equal residue-field determinants. Hence the product over the factors is independent of
-- the chosen series.
/-- The filtration-defined determinant of `(M, φ)` is independent of the chosen `φ`-stable
composition series. -/
theorem existsUnique_det
    (φ : Module.End R M) :
    ∃! a : κ,
      ∀ s : StableCompositionSeries φ, a = s.det := by
  let _ : Module R[X] M := φ.toPolynomialModule
  obtain ⟨s₀⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s₀.det, ?_, ?_⟩
  · intro s
    -- Compare the two stable composition series factorwise using Jordan-Hölder in the `R[X]`
    -- submodule lattice.
    obtain ⟨σ, hσ⟩ := CompositionSeries.jordan_holder_factors_linearEquiv
      s₀.1 s.1 s₀.head_eq_bot s₀.last_eq_top s.head_eq_bot s.last_eq_top
    -- Once determinant is invariant on corresponding simple factors, the global product agrees by
    -- reindexing along the Jordan-Hölder permutation `σ`.
    have hdet_factor :
        ∀ i : Fin s₀.1.length,
          StableCompositionSeries.factorDet s₀ i = StableCompositionSeries.factorDet s (σ i) := by
      intro i
      obtain ⟨e⟩ := hσ i
      -- Jordan-Hölder matched factors become conjugate after residue-field base change.
      have hconj :=
        StableCompositionSeries.factorResidueFieldMap_conj_of_factor_baseChange_linearEquiv
          (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e
      simpa [StableCompositionSeries.factorDet] using
        det_eq_of_linearEquiv_conj
          (f := StableCompositionSeries.factorResidueFieldMap s₀ i)
          (g := StableCompositionSeries.factorResidueFieldMap s (σ i))
          (e := StableCompositionSeries.factor_baseChange_linearEquiv
            (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e)
          hconj |>.symm
    have hdet := Fintype.prod_equiv σ
      (fun i : Fin s₀.1.length ↦ StableCompositionSeries.factorDet s₀ i)
      (fun j : Fin s.1.length ↦ StableCompositionSeries.factorDet s j)
      hdet_factor
    simpa [StableCompositionSeries.det] using hdet
  · intro a ha
    -- The universal value is determined by evaluating the defining property on one fixed series.
    simpa using ha s₀

-- Proof sketch: the same Jordan-Hölder argument applies, now using additivity of trace on the
-- simple `R[X]`-factor residue-field vector spaces and invariance under isomorphism of factors.
/-- The filtration-defined trace of `(M, φ)` is independent of the chosen `φ`-stable composition
series. -/
theorem existsUnique_trace
    (φ : Module.End R M) :
    ∃! a : κ,
      ∀ s : StableCompositionSeries φ, a = s.trace := by
  let _ : Module R[X] M := φ.toPolynomialModule
  obtain ⟨s₀⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s₀.trace, ?_, ?_⟩
  · intro s
    -- Compare the two stable composition series factorwise using Jordan-Hölder in the `R[X]`
    -- submodule lattice.
    obtain ⟨σ, hσ⟩ := CompositionSeries.jordan_holder_factors_linearEquiv
      s₀.1 s.1 s₀.head_eq_bot s₀.last_eq_top s.head_eq_bot s.last_eq_top
    -- Once trace is invariant on corresponding simple factors, the global sum agrees by
    -- reindexing along `σ`.
    have htrace_factor :
        ∀ i : Fin s₀.1.length,
          StableCompositionSeries.factorTrace s₀ i = StableCompositionSeries.factorTrace s (σ i) := by
      intro i
      obtain ⟨e⟩ := hσ i
      -- Jordan-Hölder matched factors become conjugate after residue-field base change.
      have hconj :=
        StableCompositionSeries.factorResidueFieldMap_conj_of_factor_baseChange_linearEquiv
          (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e
      simpa [StableCompositionSeries.factorTrace] using
        trace_eq_of_linearEquiv_conj
          (f := StableCompositionSeries.factorResidueFieldMap s₀ i)
          (g := StableCompositionSeries.factorResidueFieldMap s (σ i))
          (e := StableCompositionSeries.factor_baseChange_linearEquiv
            (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e)
          hconj |>.symm
    have htrace := Fintype.sum_equiv σ
      (fun i : Fin s₀.1.length ↦ StableCompositionSeries.factorTrace s₀ i)
      (fun j : Fin s.1.length ↦ StableCompositionSeries.factorTrace s j)
      htrace_factor
    simpa [StableCompositionSeries.trace] using htrace
  · intro a ha
    -- The universal value is determined by evaluating the defining property on one fixed series.
    simpa using ha s₀

-- Proof sketch: again Jordan-Hölder gives the same multiset of simple `R[X]`-factors, and the
-- characteristic polynomial of each factor is invariant under isomorphism, so the product is
-- independent of the chosen series.
/-- The filtration-defined characteristic polynomial of `(M, φ)` is independent of the chosen
`φ`-stable composition series. -/
theorem existsUnique_charpoly
    (φ : Module.End R M) :
    ∃! p : Polynomial κ,
      ∀ s : StableCompositionSeries φ, p = s.charpoly := by
  let _ : Module R[X] M := φ.toPolynomialModule
  obtain ⟨s₀⟩ := nonempty_stableCompositionSeries φ
  refine ⟨s₀.charpoly, ?_, ?_⟩
  · intro s
    -- Compare the two stable composition series factorwise using Jordan-Hölder in the `R[X]`
    -- submodule lattice.
    obtain ⟨σ, hσ⟩ := CompositionSeries.jordan_holder_factors_linearEquiv
      s₀.1 s.1 s₀.head_eq_bot s₀.last_eq_top s.head_eq_bot s.last_eq_top
    -- Once characteristic polynomial is invariant on corresponding simple factors, the global
    -- product agrees by reindexing along `σ`.
    have hcharpoly_factor :
        ∀ i : Fin s₀.1.length,
          StableCompositionSeries.factorCharpoly s₀ i =
            StableCompositionSeries.factorCharpoly s (σ i) := by
      intro i
      obtain ⟨e⟩ := hσ i
      -- Jordan-Hölder matched factors become conjugate after residue-field base change.
      have hconj :=
        StableCompositionSeries.factorResidueFieldMap_conj_of_factor_baseChange_linearEquiv
          (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e
      simpa [StableCompositionSeries.factorCharpoly] using
        charpoly_eq_of_linearEquiv_conj
          (f := StableCompositionSeries.factorResidueFieldMap s₀ i)
          (g := StableCompositionSeries.factorResidueFieldMap s (σ i))
          (e := StableCompositionSeries.factor_baseChange_linearEquiv
            (φ := φ) (s₀ := s₀) (s₁ := s) (i := i) (j := σ i) e)
          hconj |>.symm
    have hcharpoly := Fintype.prod_equiv σ
      (fun i : Fin s₀.1.length ↦ StableCompositionSeries.factorCharpoly s₀ i)
      (fun j : Fin s.1.length ↦ StableCompositionSeries.factorCharpoly s j)
      hcharpoly_factor
    simpa [StableCompositionSeries.charpoly] using hcharpoly
  · intro p hp
    -- The universal value is determined by evaluating the defining property on one fixed series.
    simpa using hp s₀

end FiniteLength

/-- The determinant of `(M, φ)` defined as the common value computed from any finite filtration by
simple `(M, φ)`-factors. -/
noncomputable def finiteLengthDeterminant
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_det φ).choose

/-- The trace of `(M, φ)` defined as the common value computed from any finite filtration by simple
`(M, φ)`-factors. -/
noncomputable def finiteLengthTrace
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_trace φ).choose

/-- The characteristic polynomial of `(M, φ)` defined as the common value computed from any finite
filtration by simple `(M, φ)`-factors. -/
noncomputable def finiteLengthCharpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) :
    Polynomial κ :=
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  (existsUnique_charpoly φ).choose

/-- The canonical finite-length determinant is computed by any `φ`-stable composition series of
submodules of `M`. -/
theorem finiteLengthDeterminant_eq_det
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthDeterminant hM = s.det := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_det φ).choose_spec.1 s

/-- The canonical finite-length trace is computed by any `φ`-stable composition series of
submodules of `M`. -/
theorem finiteLengthTrace_eq_trace
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthTrace hM = s.trace := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_trace φ).choose_spec.1 s

/-- The canonical finite-length characteristic polynomial is computed by any `φ`-stable
composition series of submodules of `M`. -/
theorem finiteLengthCharpoly_eq_charpoly
    (φ : Module.End R M) (hM : IsFiniteLength R M) (s : StableCompositionSeries φ) :
    φ.finiteLengthCharpoly hM = s.charpoly := by
  letI : IsNoetherian R M := isNoetherian_of_isFiniteLength hM
  letI : IsArtinian R M := isArtinian_of_isFiniteLength hM
  exact (existsUnique_charpoly φ).choose_spec.1 s

end LocalRing

end Module.End

variable [IsLocalRing R]

section ShortExact

variable {S : ShortComplex (ModuleCat R)}
variable (φ₁ : Module.End R S.X₁) (φ₂ : Module.End R S.X₂) (φ₃ : Module.End R S.X₃)
variable (hX₁ : IsFiniteLength R S.X₁) (hX₂ : IsFiniteLength R S.X₂) (hX₃ : IsFiniteLength R S.X₃)

local notation "fS" => S.f.hom
local notation "gS" => S.g.hom

-- Proof sketch: pass the commuting short exact sequence of `R`-modules with endomorphism to the
-- associated `R[X]`-modules, refine compatible composition series, identify the factors for the
-- middle term with the factors for the outer terms, and reassemble the filtration-defined
-- invariants using multiplicativity of determinant and characteristic polynomial and additivity of
-- trace on simple factors.

namespace Module.End

/-- Helper for Lemma 15.121.1: an intertwining `R`-linear map commutes with every polynomial in
the two endomorphisms. -/
private theorem polynomial_intertwiner_commutes_pow
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φM : Module.End R M) (φN : Module.End R N)
    (u : M →ₗ[R] N)
    (hu : u.comp φM = φN.comp u) (n : ℕ) :
    u.comp (φM ^ n) = (φN ^ n).comp u := by
  induction n with
  | zero =>
    -- Both sides reduce to `u` because the zeroth power is the identity endomorphism.
    ext x
    rfl
  | succ n ihn =>
    -- Push the last copy of the endomorphism across `u` using the intertwining hypothesis.
    calc
      u.comp (φM ^ n.succ) = (u.comp (φM ^ n)).comp φM := by
        simpa [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
      _ = ((φN ^ n).comp u).comp φM := by
        rw [ihn]
      _ = (φN ^ n).comp (u.comp φM) := by
        simp [LinearMap.comp_assoc]
      _ = (φN ^ n).comp (φN.comp u) := by
        rw [hu]
      _ = (φN ^ n.succ).comp u := by
        simpa [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- Helper for Lemma 15.121.1: an intertwining map commutes with polynomial evaluation in the two
endomorphisms. -/
private theorem polynomial_intertwiner_commutes_aeval
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φM : Module.End R M) (φN : Module.End R N)
    (u : M →ₗ[R] N)
    (hu : u.comp φM = φN.comp u) (p : R[X]) :
    u.comp ((aeval φM) p) = ((aeval φN) p).comp u := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    -- Polynomial additivity reduces the claim to the two induction hypotheses.
    calc
      u.comp ((aeval φM) (p + q))
          = u.comp ((aeval φM) p + (aeval φM) q) := by
              rw [aeval_add]
      _ = u.comp ((aeval φM) p) + u.comp ((aeval φM) q) := by
            rw [LinearMap.comp_add]
      _ = ((aeval φN) p).comp u + ((aeval φN) q).comp u := by
            rw [hp, hq]
      _ = ((aeval φN) p + (aeval φN) q).comp u := by
            rw [LinearMap.add_comp]
      _ = ((aeval φN) (p + q)).comp u := by
            rw [aeval_add]
  · intro n a
    -- A monomial evaluates to a scalar multiple of a power, so only the power intertwining
    -- lemma is needed here.
    calc
      u.comp ((aeval φM) (Polynomial.monomial n a))
          = u.comp (a • φM ^ n) := by
            simp [Polynomial.aeval_monomial, Algebra.smul_def]
      _ = a • (u.comp (φM ^ n)) := by
            simp [LinearMap.comp_smul]
      _ = a • ((φN ^ n).comp u) := by
            rw [polynomial_intertwiner_commutes_pow (φM := φM) (φN := φN) (u := u) hu n]
      _ = (a • (φN ^ n)).comp u := by
            simp [LinearMap.smul_comp]
      _ = ((aeval φN) (Polynomial.monomial n a)).comp u := by
            simp [Polynomial.aeval_monomial, Algebra.smul_def]

/-- Helper for Lemma 15.121.1: an intertwining `R`-linear map becomes `R[X]`-linear for the
canonical polynomial-module structures attached to the two endomorphisms. -/
private theorem polynomial_intertwiner_map_smul
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φM : Module.End R M) (φN : Module.End R N)
    (u : M →ₗ[R] N)
    (hu : u.comp φM = φN.comp u)
    (p : R[X]) (x : M) :
    let _ : Module R[X] M := Module.End.toPolynomialModule φM
    let _ : Module R[X] N := Module.End.toPolynomialModule φN
    u (p • x) = p • u x := by
  -- Evaluate the polynomial intertwining identity at `x` and then read both sides as module
  -- actions coming from `aeval`.
  have hpoly :=
    congrArg (fun f : M →ₗ[R] N ↦ f x)
      (polynomial_intertwiner_commutes_aeval (φM := φM) (φN := φN) (u := u) hu p)
  change u (((aeval φM) p) x) = (((aeval φN) p) (u x)) at hpoly
  simpa [Module.End.toPolynomialModule, Algebra.smul_def] using hpoly

/-- Helper for Lemma 15.121.1: an intertwining map in the short exact sequence may be viewed as an
`R[X]`-linear map for the canonical polynomial-module structures. -/
private noncomputable def polynomialLinearMap_of_commSq
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (φM : Module.End R M) (φN : Module.End R N)
    (u : M →ₗ[R] N)
    (hu : u.comp φM = φN.comp u) :
    let _ : Module R[X] M := Module.End.toPolynomialModule φM
    let _ : Module R[X] N := Module.End.toPolynomialModule φN
    M →ₗ[R[X]] N :=
  let _ : Module R[X] M := Module.End.toPolynomialModule φM
  let _ : Module R[X] N := Module.End.toPolynomialModule φN
  { toFun := u
    map_add' := u.map_add
    map_smul' := polynomial_intertwiner_map_smul φM φN u hu }

/-- Helper for Lemma 15.121.1: the left square of the short exact sequence gives an intertwining
identity for the underlying `R`-linear maps. -/
private theorem shortExact_left_intertwines
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂)) :
    (fS : S.X₁ →ₗ[R] S.X₂).comp φ₁ = φ₂.comp (fS : S.X₁ →ₗ[R] S.X₂) :=
  ModuleCat.hom_ext_iff.mp hf.w

/-- Helper for Lemma 15.121.1: the right square of the short exact sequence gives an intertwining
identity for the underlying `R`-linear maps. -/
private theorem shortExact_right_intertwines
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃)) :
    (gS : S.X₂ →ₗ[R] S.X₃).comp φ₂ = φ₃.comp (gS : S.X₂ →ₗ[R] S.X₃) :=
  ModuleCat.hom_ext_iff.mp hg.w

/-- Helper for Lemma 15.121.1: the left map in the short exact row, viewed as an `R[X]`-linear
map after passing to the canonical polynomial-module structures. -/
private noncomputable abbrev shortExactPolynomialMapLeft
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    S.X₁ →ₗ[R[X]] S.X₂ :=
  polynomialLinearMap_of_commSq φ₁ φ₂ fS (shortExact_left_intertwines (φ₁ := φ₁) (φ₂ := φ₂) hf)

/-- Helper for Lemma 15.121.1: the right map in the short exact row, viewed as an `R[X]`-linear
map after passing to the canonical polynomial-module structures. -/
private noncomputable abbrev shortExactPolynomialMapRight
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃)) :
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    S.X₂ →ₗ[R[X]] S.X₃ :=
  polynomialLinearMap_of_commSq φ₂ φ₃ gS (shortExact_right_intertwines (φ₂ := φ₂) (φ₃ := φ₃) hg)

/-- Helper for Lemma 15.121.1: package the induced `R[X]`-linear short exact row once, so later
splice lemmas can work entirely inside the submodule lattice of the middle polynomial module. -/
private theorem polynomialLinearMap_shortExact_data
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) ∧
      Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) ∧
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) := by
  let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
  -- The polynomial-module maps have the same underlying functions as the original short exact row,
  -- so mono/epi and exactness transport directly from the `ModuleCat` statement.
  have hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) := by
    simpa [shortExactPolynomialMapLeft, polynomialLinearMap_of_commSq] using
      (ModuleCat.mono_iff_injective _).1 hS.mono_f
  have hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) := by
    simpa [shortExactPolynomialMapRight, polynomialLinearMap_of_commSq] using
      (ModuleCat.epi_iff_surjective _).1 hS.epi_g
  have hExact :
      Function.Exact (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
        (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) := by
    simpa [shortExactPolynomialMapLeft, shortExactPolynomialMapRight,
      polynomialLinearMap_of_commSq] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  have hRangeKer :
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) := by
    -- Once exactness is recorded for the polynomial-linear maps themselves, `LinearMap.exact_iff`
    -- gives the seam as `range = ker`.
    simpa using (LinearMap.exact_iff.mp hExact).symm
  exact ⟨hfSX, hgSX, hRangeKer⟩

/-- Helper for Lemma 15.121.1: map the left stable composition series stagewise along the
injective `R[X]`-linear map into the middle polynomial module. -/
private noncomputable abbrev imageCompositionSeriesOfInjective
    (s₁ : StableCompositionSeries φ₁)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    CompositionSeries (Submodule R[X] S.X₂) :=
  let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  s₁.1.map
    { toFun := fun P ↦ P.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
      map_rel' := fun {_ _} hPQ ↦ Submodule.map_covBy_of_injective hfSX hPQ }

/-- Helper for Lemma 15.121.1: the mapped left series runs from `⊥` to the image/range of the
left `R[X]`-linear map in the middle module. -/
private theorem imageCompositionSeriesOfInjective_head_last
    (s₁ : StableCompositionSeries φ₁)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    (imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX).head = ⊥ ∧
      (imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX).last =
        LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) := by
  let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  -- Route correction: `CompositionSeries` is a `RelSeries`, so endpoint normalization comes
  -- directly from the owner `RelSeries.head_map`/`RelSeries.last_map` lemmas.
  constructor
  · -- The mapped series starts at the image of `⊥`, hence still at `⊥`.
    rw [imageCompositionSeriesOfInjective, RelSeries.head_map, s₁.2.1]
    change
      Submodule.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) ⊥ = ⊥
    rw [Submodule.map_bot]
  · -- The mapped series ends at the image of `⊤`, namely the range of the injective map.
    rw [imageCompositionSeriesOfInjective, RelSeries.last_map, s₁.2.2]
    change
      Submodule.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) ⊤ =
        LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
    rw [Submodule.map_top]

/-- Helper for Lemma 15.121.1: pull the quotient-side stable composition series back stagewise
along the surjective `R[X]`-linear map into the middle polynomial module. -/
private noncomputable abbrev preimageCompositionSeriesOfSurjective
    (s₃ : StableCompositionSeries φ₃)
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    CompositionSeries (Submodule R[X] S.X₂) :=
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
  s₃.1.map
    { toFun := fun P ↦ P.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)
      map_rel' := fun {_ _} hPQ ↦ Submodule.comap_covBy_of_surjective hgSX hPQ }

/-- Helper for Lemma 15.121.1: the pulled-back quotient-side series runs from the kernel of the
right map to `⊤` in the middle polynomial module. -/
private theorem preimageCompositionSeriesOfSurjective_head_last
    (s₃ : StableCompositionSeries φ₃)
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    (preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX).head =
      LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) ∧
      (preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX).last = ⊤ := by
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
  -- Route correction: the pulled-back endpoints are also owner `RelSeries.map` endpoints, so the
  -- goal reduces immediately to `Submodule.comap_bot` and `Submodule.comap_top`.
  constructor
  · -- Pulling back the bottom stage is exactly the kernel of the surjective map.
    rw [preimageCompositionSeriesOfSurjective, RelSeries.head_map, s₃.2.1]
    change
      Submodule.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) ⊥ =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)
    rw [Submodule.comap_bot]
  · -- Pulling back the top stage stays top.
    rw [preimageCompositionSeriesOfSurjective, RelSeries.last_map, s₃.2.2]
    change
      Submodule.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg) ⊤ = ⊤
    rw [Submodule.comap_top]

/-- Helper for Lemma 15.121.1: the mapped left series and pulled-back right series meet along the
exact seam `range = ker`, so `RelSeries.smash` applies to them in the middle module. -/
private theorem middleStableCompositionSeriesOfShortExact_connect
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    (imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX).last =
      (preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX).head := by
  -- The endpoint computations reduce the seam to the exactness equality `range = ker`.
  rw [imageCompositionSeriesOfInjective_head_last (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX |>.2,
    preimageCompositionSeriesOfSurjective_head_last (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX |>.1]
  exact hRangeKer

/-- Helper for Lemma 15.121.1: smashing the mapped left series with the pulled-back right series
along the exact seam produces a stable composition series from `⊥` to `⊤` in the middle module. -/
private theorem middleStableCompositionSeriesOfShortExact_head_last
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    let sLeft := imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX
    let sRight := preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX
    let hConnect :=
      middleStableCompositionSeriesOfShortExact_connect
        (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) s₁ s₃ hf hg hfSX hgSX hRangeKer
    (sLeft.smash sRight hConnect).head = ⊥ ∧ (sLeft.smash sRight hConnect).last = ⊤ := by
  let sLeft := imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX
  let sRight := preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX
  let hConnect :=
    middleStableCompositionSeriesOfShortExact_connect
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) s₁ s₃ hf hg hfSX hgSX hRangeKer
  -- The smashed chain inherits `⊥` from the left series and `⊤` from the right series.
  constructor
  · calc
      (sLeft.smash sRight hConnect).head = sLeft.head := RelSeries.head_smash hConnect
      _ = ⊥ := (imageCompositionSeriesOfInjective_head_last (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX).1
  · calc
      (sLeft.smash sRight hConnect).last = sRight.last := RelSeries.last_smash hConnect
      _ = ⊤ := (preimageCompositionSeriesOfSurjective_head_last
        (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX).2

/-- Helper for Lemma 15.121.1: splice the image-side and quotient-side chains into a single stable
composition series for the middle term. -/
private noncomputable abbrev middleStableCompositionSeriesOfShortExact
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    StableCompositionSeries φ₂ :=
  let sLeft := imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX
  let sRight := preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX
  let hConnect :=
    middleStableCompositionSeriesOfShortExact_connect
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) s₁ s₃ hf hg hfSX hgSX hRangeKer
  ⟨sLeft.smash sRight hConnect,
    middleStableCompositionSeriesOfShortExact_head_last
      (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) s₁ s₃ hf hg hfSX hgSX hRangeKer⟩

/-- Helper for Lemma 15.121.1: for nested submodules `K ≤ L`, the quotient `L / K` is naturally
the image of `L` inside the ambient quotient `F / K`. This packages the first-isomorphism step
needed for the mapped-factor comparison. -/
private noncomputable def quotient_submoduleOf_equiv_image
    {A : Type*} [CommRing A] {F : Type*} [AddCommGroup F] [Module A F]
    (K L : Submodule A F) :
    (L ⧸ K.submoduleOf L) ≃ₗ[A] L.map K.mkQ := by
  let f : L →ₗ[A] F ⧸ K := K.mkQ.comp L.subtype
  have hk : f.ker = K.submoduleOf L := by
    -- An element of `L` maps to zero in `F / K` exactly when it already lies in `K`.
    ext x
    simp [f, Submodule.submoduleOf]
  have hr : f.range = L.map K.mkQ := by
    -- The range of the restricted quotient map is the visible image of `L` in `F ⧸ K`.
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- Route correction: isolate the quotient-image comparison once, instead of transporting
  -- `CompositionSeries.factor` definitionally inside the main short exact proof.
  exact
    (Submodule.quotEquivOfEq _ _ hk.symm).trans
      (f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hr))

/-- Helper for Lemma 15.121.1: the successive quotient of the mapped left chain is linearly
equivalent to the corresponding successive quotient of the original left chain. -/
private theorem imageCompositionSeriesOfInjective_factor_quotient_model
    (s₁ : StableCompositionSeries φ₁)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (i : Fin s₁.1.length) :
    let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    (imageCompositionSeriesOfInjective (φ₁ := φ₁) (φ₂ := φ₂) s₁ hf hfSX).factor i =
      ((Submodule.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
          (s₁.1.toFun i.succ)) ⧸
        Submodule.comap
          (Submodule.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
            (s₁.1.toFun i.succ)).subtype
          (Submodule.map (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf)
            (s₁.1.toFun i.castSucc))) := by
  let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  -- Unfold the mapped series once so the factor is expressed with the concrete mapped stages.
  rfl

/-- Helper for Lemma 15.121.1: the successive quotient of the pulled-back quotient-side chain is
the quotient of the concrete pulled-back stages in the middle term. -/
private theorem preimageCompositionSeriesOfSurjective_factor_quotient_model
    (s₃ : StableCompositionSeries φ₃)
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (i : Fin s₃.1.length) :
    let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
    let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
    (preimageCompositionSeriesOfSurjective (φ₂ := φ₂) (φ₃ := φ₃) s₃ hg hgSX).factor i =
      ((Submodule.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)
          (s₃.1.toFun i.succ)) ⧸
        Submodule.comap
          (Submodule.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)
            (s₃.1.toFun i.succ)).subtype
          (Submodule.comap (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)
            (s₃.1.toFun i.castSucc))) := by
  let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
  let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
  -- Unfold the pulled-back series once so the factor is expressed with the concrete comapped
  -- stages.
  rfl

/-- Helper for Lemma 15.121.1: placeholder frontier for the mapped-factor quotient comparison while
the quotient-model API is being stabilized. -/
private theorem imageCompositionSeriesOfInjective_factor_quotient_congr
    (s₁ : StableCompositionSeries φ₁)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (i : Fin s₁.1.length) :
    True := by
  -- TODO: restore the intended quotient comparison once the mapped-factor quotient model
  -- elaborates without typeclass timeout.
  trivial

/-- Helper for Lemma 15.121.1: placeholder frontier for the pulled-back-factor quotient comparison
while the quotient-model API is being stabilized. -/
private theorem preimageCompositionSeriesOfSurjective_factor_quotient_congr
    (s₃ : StableCompositionSeries φ₃)
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (i : Fin s₃.1.length) :
    True := by
  -- TODO: restore the intended quotient comparison once the pulled-back-factor quotient model
  -- elaborates without typeclass timeout.
  trivial

/-- Helper for Lemma 15.121.1: placeholder frontier for the mapped-factor linear equivalence. -/
private theorem imageCompositionSeriesOfInjective_factor_linearEquiv
    (s₁ : StableCompositionSeries φ₁)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (i : Fin s₁.1.length) :
    True := by
  -- TODO: recover this factor equivalence from the quotient comparison once that API is stable.
  trivial

/-- Helper for Lemma 15.121.1: placeholder frontier for the pulled-back-factor linear
equivalence. -/
private theorem preimageCompositionSeriesOfSurjective_factor_linearEquiv
    (s₃ : StableCompositionSeries φ₃)
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (i : Fin s₃.1.length) :
    True := by
  -- TODO: recover this factor equivalence from the quotient comparison once that API is stable.
  trivial

/-- Helper for Lemma 15.121.1: the spliced middle series has one factor for each left block factor
and one factor for each right block factor. -/
private theorem middleStableCompositionSeriesOfShortExact_length
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg)) :
    s₁.1.length + s₃.1.length =
      (middleStableCompositionSeriesOfShortExact
        (φ₁ := φ₁) (φ₂ := φ₂) (φ₃ := φ₃) s₁ s₃ hf hg hfSX hgSX hRangeKer).1.length := by
  -- After defining the middle chain by `RelSeries.smash`, the length is the visible sum of the
  -- two outer lengths.
  simp [middleStableCompositionSeriesOfShortExact, RelSeries.smash]

/-- Helper for Lemma 15.121.1: placeholder frontier for the left-block factor identification in the
spliced middle series. -/
private theorem middleStableCompositionSeries_factor_left_linearEquiv
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (i : Fin s₁.1.length) :
    True := by
  -- TODO: identify the left smash block with the mapped left composition factor.
  trivial

/-- Helper for Lemma 15.121.1: placeholder frontier for the right-block factor identification in
the spliced middle series. -/
private theorem middleStableCompositionSeries_factor_right_linearEquiv
    (s₁ : StableCompositionSeries φ₁)
    (s₃ : StableCompositionSeries φ₃)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    (hfSX : Function.Injective (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf))
    (hgSX : Function.Surjective (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (hRangeKer :
      let _ : Module R[X] S.X₁ := Module.End.toPolynomialModule φ₁
      let _ : Module R[X] S.X₂ := Module.End.toPolynomialModule φ₂
      let _ : Module R[X] S.X₃ := Module.End.toPolynomialModule φ₃
      LinearMap.range (shortExactPolynomialMapLeft (φ₁ := φ₁) (φ₂ := φ₂) hf) =
        LinearMap.ker (shortExactPolynomialMapRight (φ₂ := φ₂) (φ₃ := φ₃) hg))
    (i : Fin s₃.1.length) :
    True := by
  -- TODO: identify the right smash block with the pulled-back quotient-side composition factor.
  trivial

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
determinant over `κ` is multiplicative. -/
@[stacks 0GSY]
theorem finiteLengthDeterminant_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthDeterminant hX₂ =
        φ₁.finiteLengthDeterminant hX₁ * φ₃.finiteLengthDeterminant hX₃ := by
  -- TODO: complete the splice endgame by transporting the left and right factor invariants across
  -- `middleStableCompositionSeries_factor_left_linearEquiv/right_linearEquiv` and then splitting
  -- the middle `Fin` product by the length identity.
  sorry

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
trace over `κ` is additive. -/
@[stacks 0GSY]
theorem finiteLengthTrace_eq_add_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthTrace hX₂ = φ₁.finiteLengthTrace hX₁ + φ₃.finiteLengthTrace hX₃ := by
  -- TODO: reuse the determinant proof skeleton with `Fin.sum_univ_add` after the factorwise
  -- cross-ambient trace identities are transported through the spliced middle series.
  sorry

/-- Lemma 15.121.1: for a short exact sequence
`0 → (M, φ) → (M', φ') → (M'', φ'') → 0` of finite-length `R`-modules with endomorphism, the
characteristic polynomial over `κ` of `φ'` is the product of those of `φ` and `φ''`. -/
@[stacks 0GSY]
theorem finiteLengthCharpoly_eq_mul_of_shortExact
    (hS : S.ShortExact)
    (hf : CommSq (ofHom φ₁) (ofHom fS) (ofHom fS) (ofHom φ₂))
    (hg : CommSq (ofHom φ₂) (ofHom gS) (ofHom gS) (ofHom φ₃))
    : φ₂.finiteLengthCharpoly hX₂ =
        φ₁.finiteLengthCharpoly hX₁ * φ₃.finiteLengthCharpoly hX₃ := by
  -- TODO: reuse the determinant proof skeleton with `Fin.prod_univ_add` after the factorwise
  -- cross-ambient characteristic-polynomial identities are transported through the spliced middle
  -- series.
  sorry

end Module.End

end ShortExact

section LinearAlgebraBridge

variable {κ : Type u} {V : Type v}
variable [Field κ] [AddCommGroup V] [Module κ V] [FiniteDimensional κ V]
variable (W : Submodule κ V) (φ : Module.End κ V) (hW : W ≤ W.comap φ)

namespace LinearMap

/-- Helper for Lemma 15.121.1: the `inr` basis vectors of `Module.Basis.sumQuot` project to the
chosen quotient basis. -/
private theorem sumQuot_mkQ_inr
    {m n : Type*}
    (bW : Module.Basis m κ W) (bQ : Module.Basis n κ (V ⧸ W)) (j : n) :
    W.mkQ ((bW.sumQuot bQ) (Sum.inr j)) = bQ j := by
  -- Compare quotient coordinates against the chosen quotient basis.
  apply (bQ.repr).injective
  ext i
  simpa using
    (Module.Basis.sumQuot_repr_inr bW bQ ((bW.sumQuot bQ) (Sum.inr j)) i)

/-- Helper for Lemma 15.121.1: an invariant basis vector from `W` has no quotient coordinates in
the `sumQuot` basis. -/
private theorem sumQuot_repr_inr_apply_inl_eq_zero
    {m n : Type*}
    (bW : Module.Basis m κ W) (bQ : Module.Basis n κ (V ⧸ W))
    (hW : W ≤ W.comap φ) (j : m) (i : n) :
    ((bW.sumQuot bQ).repr (φ ↑(bW j))) (Sum.inr i) = 0 := by
  -- Invariance of `W` forces the quotient image to vanish.
  have hzero : W.mkQ (φ ↑(bW j)) = 0 := by
    apply (LinearMap.mem_ker).1
    rw [Submodule.ker_mkQ]
    exact hW (bW j).property
  rw [Module.Basis.sumQuot_repr_inr]
  simpa using congrArg (fun x ↦ (bQ.repr x) i) hzero

-- Proof sketch: choose a basis of `W` and a basis of `V ⧸ W`, combine them into a basis of `V`,
-- and identify the matrix of `φ` with an upper block-triangular matrix; the characteristic
-- polynomial is then the product of the diagonal block characteristic polynomials.
/-- Bridge/view: for an invariant subspace decomposition, the characteristic polynomial is the
product of the characteristic polynomials of the restriction and quotient endomorphisms. -/
theorem charpoly_eq_mul_restrict_mapQ :
    φ.charpoly = (φ.restrict hW).charpoly * (W.mapQ W φ hW).charpoly := by
  classical
  let m := Module.Free.ChooseBasisIndex κ W
  let bW : Module.Basis m κ W := Module.Free.chooseBasis κ W
  let n := Module.Free.ChooseBasisIndex κ (V ⧸ W)
  let bQ : Module.Basis n κ (V ⧸ W) := Module.Free.chooseBasis κ (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m κ := LinearMap.toMatrix bW bW (φ.restrict hW)
  let B : Matrix m n κ := Matrix.of fun i l ↦
    ((Module.Basis.sumQuot bW bQ).repr
      (φ ((Module.Basis.sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n κ := LinearMap.toMatrix bQ bQ (W.mapQ W φ hW)
  -- An adapted basis turns `φ` into an upper block-triangular matrix.
  have hmatrix : LinearMap.toMatrix b b φ = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply Module.Basis.sumQuot_repr_inl_of_mem
      | inr l =>
        simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        have hzero : W.mkQ (φ (bW k)) = 0 := by
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact hW (Submodule.coe_mem (bW k))
        simp [LinearMap.toMatrix_apply, b, hzero, Matrix.fromBlocks_apply₂₁]
      | inr l =>
        simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  -- The matrix-level block formula translates back to the linear-map characteristic polynomial.
  rw [← LinearMap.charpoly_toMatrix φ b, hmatrix, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix (φ.restrict hW) bW,
    LinearMap.charpoly_toMatrix (W.mapQ W φ hW) bQ]

/- Bridge/view: the determinant statement in the same situation is already the canonical mathlib
owner theorem. -/
recall LinearMap.det_eq_det_mul_det

-- Proof sketch: after choosing a basis adapted to `W`, the matrix of `φ` becomes block upper
-- triangular, so its trace is the sum of the traces of the diagonal blocks.
/-- Bridge/view: for an invariant subspace decomposition, the trace is the sum of the traces of
the restriction and quotient endomorphisms. -/
theorem trace_eq_add_restrict_mapQ :
    trace κ V φ = trace κ W (φ.restrict hW) + trace κ (V ⧸ W) (W.mapQ W φ hW) := by
  classical
  let m := Module.Free.ChooseBasisIndex κ W
  let bW : Module.Basis m κ W := Module.Free.chooseBasis κ W
  let n := Module.Free.ChooseBasisIndex κ (V ⧸ W)
  let bQ : Module.Basis n κ (V ⧸ W) := Module.Free.chooseBasis κ (V ⧸ W)
  let b := Module.Basis.sumQuot bW bQ
  let A : Matrix m m κ := LinearMap.toMatrix bW bW (φ.restrict hW)
  let B : Matrix m n κ := Matrix.of fun i l ↦
    ((Module.Basis.sumQuot bW bQ).repr
      (φ ((Module.Basis.sumQuot bW bQ) (Sum.inr l)))) (Sum.inl i)
  let D : Matrix n n κ := LinearMap.toMatrix bQ bQ (W.mapQ W φ hW)
  -- The same adapted basis exhibits the off-diagonal block without affecting the trace.
  have hmatrix : LinearMap.toMatrix b b φ = Matrix.fromBlocks A B 0 D := by
    ext u v
    cases u with
    | inl i =>
      cases v with
      | inl k =>
        simp only [b, Module.Basis.sumQuot_inl, Matrix.fromBlocks_apply₁₁, A,
          LinearMap.toMatrix_apply]
        apply Module.Basis.sumQuot_repr_inl_of_mem
      | inr l =>
        simp [b, LinearMap.toMatrix_apply, Matrix.fromBlocks_apply₁₂, B]
    | inr j =>
      cases v with
      | inl k =>
        have hzero : W.mkQ (φ (bW k)) = 0 := by
          rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
          exact hW (Submodule.coe_mem (bW k))
        simp [LinearMap.toMatrix_apply, b, hzero, Matrix.fromBlocks_apply₂₁]
      | inr l =>
        simp only [LinearMap.toMatrix_apply, Module.Basis.sumQuot_repr_inr,
          Matrix.fromBlocks_apply₂₂, b, D]
        rw [← Module.Basis.sumQuot_inr bW bQ l, W.mapQ_apply]
        simp
  -- Matrix trace on an upper block-triangular matrix is the sum of the diagonal block traces.
  rw [LinearMap.trace_eq_matrix_trace κ b φ, hmatrix,
    LinearMap.trace_eq_matrix_trace κ bW (φ.restrict hW),
    LinearMap.trace_eq_matrix_trace κ bQ (W.mapQ W φ hW)]
  simp [Matrix.trace, A, D]

end LinearMap

end LinearAlgebraBridge
