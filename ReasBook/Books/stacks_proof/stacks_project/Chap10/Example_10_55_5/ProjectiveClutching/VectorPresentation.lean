import stacks_proof.stacks_project.Chap10.Example_10_55_5.ProjectiveClutching.RankKernelCoordinates

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: explicit vector-clutching presentation data for a
finite-projective module over the equal-endpoint ring. -/
structure EqualEndpointVectorClutchingPresentation
    (M : FiniteProjectiveModuleCat.{u, u} R) where
  ι : Type u
  [finite : Fintype ι]
  [decidableEq : DecidableEq ι]
  A : Matrix ι ι k
  det_ne_zero : A.det ≠ 0
  projective : Module.Projective R (equalEndpointVectorClutchingModule (k := k) A)
  equiv : M.obj ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) A
  rank_eq : (Fintype.card ι : ℤ) = equalEndpointProjectiveRank k M

/-- Helper for Chap10 Example 10 55 5: an invertible vector-clutching module gives its own
vector-clutching presentation. -/
theorem equalEndpointVectorClutchingPresentation_self
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hdet : A.det ≠ 0)
    (hA : Module.Projective R (equalEndpointVectorClutchingModule (k := k) A)) :
    Nonempty
      (EqualEndpointVectorClutchingPresentation k
        (equalEndpointVectorClutchingProjectiveModule k A hA)) := by
  -- The self-equivalence supplies the transport field; the rank field is the named rank
  -- computation above, so no definitional reduction of the presentation package is needed here.
  let P : EqualEndpointVectorClutchingPresentation k
      (equalEndpointVectorClutchingProjectiveModule k A hA) :=
    { ι := ι
      finite := inferInstance
      decidableEq := inferInstance
      A := A
      det_ne_zero := hdet
      projective := hA
      equiv := LinearEquiv.refl R (equalEndpointVectorClutchingModule (k := k) A)
      rank_eq := (equalEndpointVectorClutchingProjectiveRank_eq_card k A hdet hA).symm }
  exact ⟨P⟩

/-- Helper for Chap10 Example 10 55 5: projective generic rank is invariant under an
`R`-linear equivalence of finite-projective modules. -/
theorem equalEndpointProjectiveRank_eq_of_linearEquiv
    (M N : FiniteProjectiveModuleCat.{u, u} R)
    (e : M.obj ≃ₗ[R] N.obj) :
    equalEndpointProjectiveRank k M = equalEndpointProjectiveRank k N := by
  -- Move the linear equivalence to an isomorphism in the finite-projective category and compare
  -- the two generator classes after applying the rank homomorphism.
  have hclass :
      projectiveGrothendieckGroupOf R M = projectiveGrothendieckGroupOf R N := by
    have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
      exact ⟨inferInstance, inferInstance⟩
    let eIso : M ≅ N :=
      CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
        e.toModuleIso
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0 M N eIso)
  have hrank :=
    congrArg (equalEndpointProjectiveRankMap.{u, u} k) hclass
  simpa [equalEndpointProjectiveRankMap_apply_of] using hrank

/-- Helper for Chap10 Example 10 55 5: a finite-projective module linearly equivalent to an
invertible vector-clutching module has a vector-clutching presentation. -/
theorem equalEndpointVectorClutchingPresentation_of_linearEquiv
    (M : FiniteProjectiveModuleCat.{u, u} R)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι k) (hdet : A.det ≠ 0)
    (hA : Module.Projective R (equalEndpointVectorClutchingModule (k := k) A))
    (e : M.obj ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) A) :
    Nonempty (EqualEndpointVectorClutchingPresentation k M) := by
  -- The supplied equivalence is the presentation equivalence; the rank field follows from
  -- rank invariance and the determinant normal-form rank computation for the clutching module.
  have hrank :
      equalEndpointProjectiveRank k M = (Fintype.card ι : ℤ) := by
    calc
      equalEndpointProjectiveRank k M =
          equalEndpointProjectiveRank k
            (equalEndpointVectorClutchingProjectiveModule k A hA) := by
            exact equalEndpointProjectiveRank_eq_of_linearEquiv k M
              (equalEndpointVectorClutchingProjectiveModule k A hA) e
      _ = (Fintype.card ι : ℤ) := by
            exact equalEndpointVectorClutchingProjectiveRank_eq_card k A hdet hA
  let P : EqualEndpointVectorClutchingPresentation k M :=
    { ι := ι
      finite := inferInstance
      decidableEq := inferInstance
      A := A
      det_ne_zero := hdet
      projective := hA
      equiv := e
      rank_eq := hrank.symm }
  exact ⟨P⟩

/-- Helper for Chap10 Example 10 55 5: a finite product of Milnor lines has its diagonal
vector-clutching presentation. -/
theorem equalEndpointLineProductProjectiveModule_vectorClutchingPresentation
    {ι : Type u} [Finite ι] (D : ι → kˣ) :
    Nonempty
      (EqualEndpointVectorClutchingPresentation k
        (equalEndpointLineProductProjectiveModule k D)) := by
  classical
  -- Use the diagonal matrix with endpoint units `D`; the existing diagonal-linear-equivalence
  -- API identifies its clutching module with the product of the corresponding Milnor lines.
  let _ : Fintype ι := Fintype.ofFinite ι
  let A : Matrix ι ι k := Matrix.diagonal fun i : ι => (D i : k)
  have hdet : A.det ≠ 0 := by
    simpa [A, Matrix.det_diagonal] using
      (Finset.prod_ne_zero_iff.mpr (fun i _ => Units.ne_zero (D i)) :
        (∏ i, (D i : k)) ≠ 0)
  have hprojective :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) A) := by
    simpa [A] using equalEndpointVectorClutchingModule_diagonal_projective k D
  let e :
      (equalEndpointLineProductProjectiveModule k D).obj ≃ₗ[R]
        equalEndpointVectorClutchingModule (k := k) A := by
    simpa [A] using equalEndpointVectorClutchingModule_diagonal_linearEquiv k D
  exact equalEndpointVectorClutchingPresentation_of_linearEquiv (k := k)
    (equalEndpointLineProductProjectiveModule k D) A hdet hprojective e

/-- Helper for Chap10 Example 10 55 5: a line-product normal form converts formally to the
explicit vector-clutching module required by the Milnor presentation. -/
theorem equalEndpointFiniteProjective_clutchingLinearEquiv_exists_of_lineProduct
    (M : FiniteProjectiveModuleCat.{u, u} R)
    (hlineProduct :
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : ι → kˣ),
        Nonempty (M.obj ≃ₗ[R] (equalEndpointLineProductProjectiveModule k D).obj)) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (A : Matrix ι ι k),
      A.det ≠ 0 ∧
        Nonempty (M.obj ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) A) := by
  rcases hlineProduct with ⟨ι, hfinite, hdecidable, D, hlineEquiv⟩
  letI : Fintype ι := hfinite
  letI : DecidableEq ι := hdecidable
  let A : Matrix ι ι k := Matrix.diagonal fun i : ι => (D i : k)
  refine ⟨ι, hfinite, hdecidable, A, ?_, ?_⟩
  · -- The chosen diagonal matrix has determinant a product of units, hence is nonzero.
    simpa [A] using equalEndpointVectorClutching_diagonalUnits_det_ne_zero k D
  · -- Compose the source line-product equivalence with the existing diagonal-clutching
    -- equivalence from the line product to the vector-clutching module.
    rcases hlineEquiv with ⟨eLine⟩
    let eDiagonal :
        (equalEndpointLineProductProjectiveModule k D).obj ≃ₗ[R]
          equalEndpointVectorClutchingModule (k := k) A := by
      simpa [A] using equalEndpointVectorClutchingModule_diagonal_linearEquiv k D
    exact ⟨eLine.trans eDiagonal⟩

/-- Helper for Chap10 Example 10 55 5: a vector-clutching presentation gives the
generator-level line-rank normal form. -/
theorem equalEndpointGeneratorNormalForm_of_vectorClutchingPresentation
    (M : FiniteProjectiveModuleCat.{u, u} R)
    (P : EqualEndpointVectorClutchingPresentation k M) :
    ∃ unitRatio : kˣ,
      projectiveGrothendieckGroupOf R M =
        equalEndpointLineRankClassMap k
          (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M) := by
  letI := P.finite
  letI := P.decidableEq
  refine ⟨Units.mk0 P.A.det P.det_ne_zero, ?_⟩
  -- Transport the `K₀` generator across the presentation equivalence.
  have hclass :
      projectiveGrothendieckGroupOf R M =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k P.A P.projective) := by
    have h0 : finiteProjectiveModuleProperty R (ModuleCat.of R PUnit) := by
      exact ⟨inferInstance, inferInstance⟩
    let eIso : M ≅ equalEndpointVectorClutchingProjectiveModule k P.A P.projective :=
      CategoryTheory.ObjectProperty.isoMk (P := finiteProjectiveModuleProperty R)
        P.equiv.toModuleIso
    exact (@ModulePropertyK0.of_iso R _ (finiteProjectiveModuleProperty R) h0
      M (equalEndpointVectorClutchingProjectiveModule k P.A P.projective) eIso)
  -- The already-proved determinant normal form evaluates the explicit clutching module.
  calc
    projectiveGrothendieckGroupOf R M =
        projectiveGrothendieckGroupOf R
          (equalEndpointVectorClutchingProjectiveModule k P.A P.projective) := hclass
    _ = equalEndpointLineRankClassMap k
          (Additive.ofMul (Units.mk0 P.A.det P.det_ne_zero), (Fintype.card P.ι : ℤ)) := by
          exact equalEndpointVectorClutchingClass_det_lineRank (k := k) P.A
            P.det_ne_zero P.projective
    _ = equalEndpointLineRankClassMap k
          (Additive.ofMul (Units.mk0 P.A.det P.det_ne_zero),
            equalEndpointProjectiveRank k M) := by
          rw [P.rank_eq]

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations for all generators give
the line-rank normal form for all finite-projective generators. -/
theorem equalEndpointGeneratorNormalForm_of_vectorClutchingPresentations
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M)) :
    ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M) := by
  intro M
  -- Choose the presentation for this generator and consume the presentation normal form.
  rcases hpresent M with ⟨P⟩
  exact equalEndpointGeneratorNormalForm_of_vectorClutchingPresentation (k := k) M P

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations and residual-line
injectivity give the source clauses needed for determinant-rank data. -/
theorem equalEndpointSourceClauses_of_vectorClutchingPresentations_and_residual_injective
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M))
    (hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) :
    (∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  -- Vector-clutching presentations supply the generator normal form; the residual injectivity
  -- premise is exactly the second source clause.
  exact ⟨equalEndpointGeneratorNormalForm_of_vectorClutchingPresentations k hpresent,
    hresidual_injective⟩

/-- Helper for Chap10 Example 10 55 5: the two source clauses imply the determinant-rank
coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_sourceClauses
    (hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Convert the source normal-form clauses into bijectivity of the line-rank class map, then
  -- read off the determinant coordinate from the inverse product equivalence.
  have hbijective : Function.Bijective (equalEndpointLineRankClassMap k) :=
    equalEndpointLineRankClassMap_bijective_of_sourceClauses (k := k) hsource
  exact equalEndpointProjectiveDetRankData_exists_of_lineRankClassMap_bijective k hbijective

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations and residual-line
injectivity produce the determinant-rank coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_residual_injective
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M))
    (hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Package the two geometric inputs as source clauses, then consume the formal determinant-rank
  -- bridge already proved above.
  have hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    equalEndpointSourceClauses_of_vectorClutchingPresentations_and_residual_injective k
      hpresent hresidual_injective
  exact equalEndpointProjectiveDetRankData_exists_of_sourceClauses k hsource

/-- Helper for Chap10 Example 10 55 5: a normalized residual-line equivalence makes the
line-plus-rank class map bijective. -/
theorem equalEndpointLineRankClassMap_bijective_of_lineResidualEquiv
    (e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker)
    (he : ∀ unitRatio : Additive kˣ,
      e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul) :
    Function.Bijective (equalEndpointLineRankClassMap k) := by
  -- The normalized forward map identifies equality of residual classes with equality of
  -- endpoint-unit ratios.
  have hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
    intro u v hresidual
    have htag : Additive.ofMul u = Additive.ofMul v := by
      apply e.injective
      calc
        e (Additive.ofMul u) = equalEndpointLineResidualClass k u := by
          simpa using he (Additive.ofMul u)
        _ = equalEndpointLineResidualClass k v := hresidual
        _ = e (Additive.ofMul v) := by
          simpa using (he (Additive.ofMul v)).symm
    simpa using congrArg Additive.toMul htag
  -- Surjectivity onto the rank kernel is the inverse direction of the same equivalence.
  have hresidual_surjective : ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
    intro z
    refine ⟨(e.symm z).toMul, ?_⟩
    calc
      equalEndpointLineResidualClass k (e.symm z).toMul = e (e.symm z) := by
        exact (he (e.symm z)).symm
      _ = z := e.apply_symm_apply z
  -- The formal line-rank map lemmas then give bijectivity.
  exact ⟨
    equalEndpointLineRankClassMap_injective_of_residual_injective (k := k)
      hresidual_injective,
    equalEndpointLineRankClassMap_surjective_of_residual_surjective (k := k)
      hresidual_surjective⟩

/-- Helper for Chap10 Example 10 55 5: a normalized residual-line equivalence supplies the
determinant-rank coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_lineResidualEquiv
    (e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker)
    (he : ∀ unitRatio : Additive kˣ,
      e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Reduce determinant-rank data to bijectivity of the explicit line-plus-rank class map.
  have hbijective : Function.Bijective (equalEndpointLineRankClassMap k) :=
    equalEndpointLineRankClassMap_bijective_of_lineResidualEquiv (k := k) e he
  exact equalEndpointProjectiveDetRankData_exists_of_lineRankClassMap_bijective k hbijective

/-- Helper for Chap10 Example 10 55 5: an existential normalized residual-line equivalence is
enough to construct the determinant-rank coordinate package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_normalizedKernelEquiv
    (hresidualEquiv :
      ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∀ unitRatio : Additive kˣ,
          e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Unpack the normalized equivalence and use the existing line-residual formal bridge.
  rcases hresidualEquiv with ⟨e, he⟩
  exact equalEndpointProjectiveDetRankData_exists_of_lineResidualEquiv k e he

/-- Helper for Chap10 Example 10 55 5: the Picard map from invertible submodules of the
polynomial normalization. -/
noncomputable def equalEndpointUnitsToPic :
    (Submodule R (equalEndpointPolynomialMulModule k))ˣ →* CommRing.Pic R :=
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)

/-- Helper for Chap10 Example 10 55 5: every Picard class of the equal-endpoint ring is the
Picard class of some invertible submodule of the polynomial normalization. -/
theorem equalEndpointUnitsToPic_surjective :
    Function.Surjective (equalEndpointUnitsToPic k) := by
  intro pic
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  letI : IsDomain (equalEndpointPolynomialMulModule k) :=
    inferInstanceAs (IsDomain (Polynomial k))
  letI : Nonempty (NormalizedGCDMonoid (equalEndpointPolynomialMulModule k)) :=
    inferInstanceAs (Nonempty (NormalizedGCDMonoid (Polynomial k)))
  have hmem : pic ∈ (Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)).range := by
    -- The normalization has trivial Picard group, so the relative Picard subgroup is all of
    -- `Pic R`; mathlib identifies that relative subgroup with the image of `unitsToPic`.
    rw [Submodule.range_unitsToPic R (equalEndpointPolynomialMulModule k)]
    have htop : CommRing.relPic R (equalEndpointPolynomialMulModule k) = ⊤ := by
      exact CommRing.relPic_eq_top R (equalEndpointPolynomialMulModule k)
    rw [htop]
    trivial
  -- Repackage the range witness through the local named `unitsToPic` homomorphism.
  rcases hmem with ⟨I, hI⟩
  exact ⟨I, hI⟩

/-- Helper for Chap10 Example 10 55 5: a principal-times-Milnor-line factorization computes the
Picard image of an invertible submodule unit. -/
theorem equalEndpointUnitsToPic_eq_linePicHom_of_unit_eq_principal_mul
    (I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ)
    (unitRatio : kˣ)
    (x : (equalEndpointPolynomialMulModule k)ˣ)
    (hI : I = Units.map (Submodule.spanSingleton R).toMonoidHom x *
        equalEndpointLineSubmoduleUnit k unitRatio) :
    equalEndpointUnitsToPic k I = equalEndpointLinePicHom k unitRatio := by
  letI : FaithfulSMul R (equalEndpointPolynomialMulModule k) :=
    equalEndpointPolynomialMulModule_faithfulSMul k
  -- Principal ambient-unit submodules lie in the kernel of `unitsToPic`.
  have hprincipal_mem :
      Units.map (Submodule.spanSingleton R).toMonoidHom x ∈
        (Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)).ker := by
    rw [Submodule.ker_unitsToPic R (equalEndpointPolynomialMulModule k)]
    exact ⟨x, rfl⟩
  have hprincipal :
      Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)
        (Units.map (Submodule.spanSingleton R).toMonoidHom x) = 1 := by
    exact hprincipal_mem
  calc
    equalEndpointUnitsToPic k I =
        Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)
          (Units.map (Submodule.spanSingleton R).toMonoidHom x *
            equalEndpointLineSubmoduleUnit k unitRatio) := by
          rw [hI]
          rfl
    _ = Submodule.unitsToPic R (equalEndpointPolynomialMulModule k)
          (equalEndpointLineSubmoduleUnit k unitRatio) := by
          rw [map_mul, hprincipal, one_mul]
    _ = equalEndpointLinePicHom k unitRatio := rfl

/-- Helper for Chap10 Example 10 55 5: a normal form for invertible submodule units implies
that every Picard class is represented by a Milnor line. -/
theorem equalEndpointLinePicHom_surjective_of_unit_factorization
    (hfactor :
      ∀ I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ,
        ∃ (unitRatio : kˣ) (x : (equalEndpointPolynomialMulModule k)ˣ),
          I = Units.map (Submodule.spanSingleton R).toMonoidHom x *
            equalEndpointLineSubmoduleUnit k unitRatio) :
    Function.Surjective (equalEndpointLinePicHom k) := by
  intro pic
  -- Lift the Picard class to an arbitrary invertible submodule, then replace that submodule by
  -- its principal-times-line normal form.
  rcases equalEndpointUnitsToPic_surjective k pic with ⟨I, hIpic⟩
  rcases hfactor I with ⟨unitRatio, x, hI⟩
  refine ⟨unitRatio, ?_⟩
  calc
    equalEndpointLinePicHom k unitRatio = equalEndpointUnitsToPic k I := by
      exact (equalEndpointUnitsToPic_eq_linePicHom_of_unit_eq_principal_mul
        (k := k) I unitRatio x hI).symm
    _ = pic := hIpic

/-- Helper for Chap10 Example 10 55 5: if every invertible submodule unit is one of the Milnor
line units, then every Picard class is represented by a Milnor line. -/
theorem equalEndpointLinePicHom_surjective_of_unit_line_cover
    (hcover :
      ∀ I : (Submodule R (equalEndpointPolynomialMulModule k))ˣ,
        ∃ unitRatio : kˣ, I = equalEndpointLineSubmoduleUnit k unitRatio) :
    Function.Surjective (equalEndpointLinePicHom k) := by
  intro pic
  -- Lift a Picard class to an invertible submodule, then use the line-cover normal form.
  rcases equalEndpointUnitsToPic_surjective k pic with ⟨I, hIpic⟩
  rcases hcover I with ⟨unitRatio, hI⟩
  refine ⟨unitRatio, ?_⟩
  calc
    equalEndpointLinePicHom k unitRatio = equalEndpointUnitsToPic k I := by
      rw [hI]
      rfl
    _ = pic := hIpic

end
