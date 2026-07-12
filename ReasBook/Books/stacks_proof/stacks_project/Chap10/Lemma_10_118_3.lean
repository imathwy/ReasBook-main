import StacksProject_2024.Chap10.Lemma_10_118_3.Index

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {R : Type u} [CommRing R] [IsDomain R]
variable {S : Type v} [CommRing S] [Algebra R S] [Algebra.FiniteType R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module.Finite S M]

open GenericFlatness

omit [IsDomain R] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 118 3: a polynomial presentation map over `R` makes the target
algebra compatible with the coefficient inclusion `R → R[x_1, ..., x_n]`. -/
lemma mvPolynomialPresentation_isScalarTower
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) :
    letI : Algebra (MvPolynomial (Fin n) R) S := π.toRingHom.toAlgebra
    IsScalarTower R (MvPolynomial (Fin n) R) S := by
  letI : Algebra (MvPolynomial (Fin n) R) S := π.toRingHom.toAlgebra
  -- Proof comment: the scalar-tower condition is exactly the `R`-linearity compatibility stored
  -- in the algebra homomorphism `π`.
  refine IsScalarTower.of_algebraMap_eq ?_
  intro r
  exact (π.commutes r).symm

/-- Helper for Chap10 Lemma 10 118 3: localized polynomial model data over one coefficient
denominator formally gives the owner localization condition. -/
private lemma exists_nonzero_localizationCondition_of_localized_mvPolynomial_model_data
    {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M]
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M']
    (hdata : ∃ f : R, f ≠ 0 ∧
        ∃ (_ : Algebra (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))),
        ∃ (_ : Module (MvPolynomial (Fin n) (Localization.Away f))
            (LocalizedModule.Away (algebraMap R S f) M)),
        ∃ (_ : IsScalarTower (Localization.Away f)
            (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))),
        ∃ (_ : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))
            (LocalizedModule.Away (algebraMap R S f) M)),
        ∃ (_ : Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S')),
        ∃ (_ : Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M')),
        ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S' ≃ₗ[MvPolynomial
            (Fin n) (Localization.Away f)]
            Localization.Away (algebraMap R S f)),
        ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M' ≃ₗ[MvPolynomial
            (Fin n) (Localization.Away f)]
            LocalizedModule.Away (algebraMap R S f) M),
        True) :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := by
  -- Proof comment: unpack the one-denominator model data and install exactly the instances used
  -- by the existing localized polynomial-model packager.
  obtain ⟨f, hf, hAlg, hMod, hTowerS, hTowerM, hFreeS, hFreeM, eSloc, eMloc, _⟩ := hdata
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) := hAlg
  letI : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) := hMod
  letI : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) := hTowerS
  letI : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) := hTowerM
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') := hFreeS
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') := hFreeM
  -- Proof comment: the packager turns the two localized polynomial-linear equivalences into the
  -- finite-presentation and freeness fields required by `LocalizationCondition`.
  exact ⟨f, hf,
    localizationCondition_of_localized_mvPolynomial_model_linearEquivs
      (R := R) (S := S) (M := M) (n := n) f eSloc eMloc⟩

/-- Helper for Chap10 Lemma 10 118 3: the remaining source-facing generic-freeness/descent
statement needed to produce one coefficient denominator and the localized polynomial model
equivalences from the supplied generic-fiber equivalences. -/
private lemma exists_localized_mvPolynomial_model_data_of_genericFiber_linearEquivs
    {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M]
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M']
    (φS : S' →ₗ[MvPolynomial (Fin n) R] S) (_hφS : Function.Surjective φS)
    (eS : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S)
    (_heS : eS.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φS)
    (φM : M' →ₗ[MvPolynomial (Fin n) R] M) (_hφM : Function.Surjective φM)
    (eM : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M)
    (_heM : eM.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φM) :
      ∃ f : R, f ≠ 0 ∧
        ∃ (_ : Algebra (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))),
        ∃ (_ : Module (MvPolynomial (Fin n) (Localization.Away f))
            (LocalizedModule.Away (algebraMap R S f) M)),
        ∃ (_ : IsScalarTower (Localization.Away f)
            (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))),
        ∃ (_ : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
            (Localization.Away (algebraMap R S f))
            (LocalizedModule.Away (algebraMap R S f) M)),
        ∃ (_ : Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S')),
        ∃ (_ : Module.Free (Localization.Away f)
            (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M')),
        ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S' ≃ₗ[MvPolynomial
            (Fin n) (Localization.Away f)]
            Localization.Away (algebraMap R S f)),
      ∃ (_ : LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M' ≃ₗ[MvPolynomial
            (Fin n) (Localization.Away f)]
            LocalizedModule.Away (algebraMap R S f) M),
        True := by
  -- Route correction: the repeated monolithic coefficient-denominator hole is now split into the
  -- source generic-freeness input and two fixed-denominator descent bridges.
  obtain ⟨f, hf, hFreeS, hFreeM⟩ :=
    exists_common_nonzero_coeffAway_free_of_finitelyPresented_mvPolynomialModules
      (R := R) (n := n) (S' := S') (M' := M')
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) S') := hFreeS
  letI : Module.Free (Localization.Away f)
      (LocalizedModule.Away (MvPolynomial.C (σ := Fin n) f) M') := hFreeM
  -- Proof comment: the algebra presentation descends first, giving the localized polynomial
  -- algebra structure and its scalar-tower bridge on `S_f`.
  let hAlg : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra (R := R) (S := S) (n := n) f
  letI : Algebra (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) := hAlg
  let hTowerS : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) :=
    localizedCoeffAwayOwnerAlgebra_isScalarTower (R := R) (S := S) (n := n) f
  letI : IsScalarTower (Localization.Away f)
      (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f)) := hTowerS
  obtain ⟨eSloc, _⟩ :=
    localized_algebra_model_linearEquiv_of_genericFiber_linearEquiv
      (R := R) (S := S) (n := n) (f := f) hf
      φS _hφS eS _heS
  -- Proof comment: with the target algebra structure fixed, the same descent bridge gives the
  -- localized polynomial-module structure and the comparison for `M_f`.
  let hMod : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule (R := R) (S := S) (M := M) (n := n) f
  letI : Module (MvPolynomial (Fin n) (Localization.Away f))
      (LocalizedModule.Away (algebraMap R S f) M) := hMod
  let hTowerM : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) :=
    localizedCoeffAwayOwnerModule_isScalarTower (R := R) (S := S) (M := M) (n := n) f
  letI : IsScalarTower (MvPolynomial (Fin n) (Localization.Away f))
      (Localization.Away (algebraMap R S f))
      (LocalizedModule.Away (algebraMap R S f) M) := hTowerM
  obtain ⟨eMloc, _⟩ :=
    localized_module_model_linearEquiv_of_genericFiber_linearEquiv
      (R := R) (S := S) (M := M) (n := n) (f := f) hf
      φM _hφM eM _heM
  exact ⟨f, hf, hAlg, hMod, hTowerS, hTowerM, hFreeS, hFreeM, eSloc, eMloc, True.intro⟩

/-- Helper for Chap10 Lemma 10 118 3: finitely presented polynomial models that agree with the
target modules on the coefficient generic fiber spread out to one coefficient denominator giving
the owner localization condition. -/
lemma exists_nonzero_localizationCondition_of_polynomial_genericFiber_models
    {n : ℕ}
    [Algebra (MvPolynomial (Fin n) R) S]
    [IsScalarTower R (MvPolynomial (Fin n) R) S]
    [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower (MvPolynomial (Fin n) R) S M]
    {S' : Type*} [AddCommGroup S'] [Module (MvPolynomial (Fin n) R) S']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) S']
    {M' : Type*} [AddCommGroup M'] [Module (MvPolynomial (Fin n) R) M']
    [Module.FinitePresentation (MvPolynomial (Fin n) R) M']
    (φS : S' →ₗ[MvPolynomial (Fin n) R] S) (_hφS : Function.Surjective φS)
    (eS : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) S)
    (_heS : eS.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φS)
    (φM : M' →ₗ[MvPolynomial (Fin n) R] M) (_hφM : Function.Surjective φM)
    (eM : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M' ≃ₗ[Localization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R))]
          LocalizedModule
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) M)
    (_heM : eM.toLinearMap = LocalizedModule.map
      (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) (nonZeroDivisors R)) φM) :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := by
  -- Proof comment: all formal packaging has been isolated in the previous helper; the only
  -- remaining mathematical input is the coefficient-generic-freeness/descent data.
  exact exists_nonzero_localizationCondition_of_localized_mvPolynomial_model_data
    (R := R) (S := S) (M := M) (n := n)
    (exists_localized_mvPolynomial_model_data_of_genericFiber_linearEquivs
      (R := R) (S := S) (M := M) (n := n)
      φS _hφS eS _heS
      φM _hφM eM _heM)

/-- Helper for Lemma 10.118.3: after fixing a surjective polynomial presentation of `S`, the
remaining source-faithful work is to spread out one common coefficient for the polynomial modules
`S` and `M` and then descend those localized polynomial conditions to `LocalizationCondition`. -/
lemma exists_nonzero_localizationCondition_of_surjective_mvPolynomial_presentation
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π) :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toRingHom.toAlgebra
  letI : IsScalarTower R P S :=
    mvPolynomialPresentation_isScalarTower (R := R) (S := S) π
  letI : Module P M := Module.compHom M π.toRingHom
  letI : IsScalarTower P S M := IsScalarTower.of_compHom P S M
  have hSfinite : Module.Finite P S :=
    mvPolynomial_module_finite_of_surjective_presentation (R := R) (S := S) π hπ
  have hMfinite : Module.Finite P M :=
    mvPolynomial_module_finite_of_surjective_presentation_on_module
      (R := R) (S := S) (N := M) π hπ
  obtain ⟨S', _hS'_add, _hS'_module, _hS'_fp, fS, hfS, eS, heS⟩ :=
    exists_finitely_presented_polynomial_surjective_model_with_generic_fiber_linearEquiv
      (R := R) (n := n) (N := S)
  obtain ⟨M', _hM'_add, _hM'_module, _hM'_fp, fM, hfM, eM, heM⟩ :=
    exists_finitely_presented_polynomial_surjective_model_with_generic_fiber_linearEquiv
      (R := R) (n := n) (N := M)
  -- Route correction: the arbitrary-polynomial denominator route has been removed. The source proof
  -- needs one denominator from `R`, so we pass the stabilized finitely presented models and their
  -- generic-fiber comparisons to the coefficient-denominator descent helper.
  exact
    exists_nonzero_localizationCondition_of_polynomial_genericFiber_models
      (R := R) (S := S) (M := M) (n := n)
      fS hfS eS heS
      fM hfM eM heM

/-- Helper for Chap10 Lemma 10 118 3: a finite-type polynomial presentation package gives the
generic-freeness localization condition by applying the already proved surjective-presentation
case. -/
lemma exists_nonzero_localizationCondition_of_mvPolynomial_presentation
    (hpres : ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] S, Function.Surjective π) :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := by
  -- Proof comment: unpack the finite-type presentation and pass the chosen surjective polynomial
  -- algebra map to the source-faithful surjective-presentation helper.
  obtain ⟨n, π, hπ⟩ := hpres
  exact exists_nonzero_localizationCondition_of_surjective_mvPolynomial_presentation
    (R := R) (S := S) (M := M) π hπ

-- Proof sketch: choose a finite presentation of `S` as a quotient of a polynomial ring over `R`
-- and first treat that polynomial case by replacing `M` with a finitely presented approximation
-- having the same generic fiber. Apply Lemma `10.118.2` to obtain a nonzero `f` making that
-- approximation free over `R_f`; then identify it with `M_f`. Finite presentation of `S_f` and
-- `M_f` follows from finite type after localizing away the same `f`.
/-- Lemma 10.118.3: if `R` is a domain, `R → S` is of finite type, and `M` is a finite `S`-module,
then there exists a nonzero `f ∈ R` such that `S_f` and `M_f` are free as `R_f`-modules, `S_f` is
a finitely presented `R_f`-algebra, and `M_f` is a finitely presented `S_f`-module. -/
@[stacks 051T]
lemma exists_nonzero_localization_away_free_and_finitePresentation_of_finiteType :
    ∃ f : R, f ≠ 0 ∧ LocalizationCondition R S M f := by
  -- Proof comment: finite type gives a finite-variable polynomial presentation, and the previous
  -- helper packages the whole polynomial spreading-out route for that presentation.
  exact exists_nonzero_localizationCondition_of_mvPolynomial_presentation
    (R := R) (S := S) (M := M)
    (exists_surjective_mvPolynomial_presentation (R := R) (S := S))

end
