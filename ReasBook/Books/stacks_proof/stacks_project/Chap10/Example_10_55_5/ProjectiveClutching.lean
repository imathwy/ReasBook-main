import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.Index

noncomputable section

universe u

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations together with a
Picard-valued determinant coordinate produce the determinant-rank package needed by the final
wrapper theorem. -/
private theorem equalEndpointProjectiveDetRankData_exists_of_presentations_and_detPic
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M))
    (hdetPic :
      ∃ detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R),
        ∀ unitRatio : kˣ,
          detPic (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) =
            Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- The imported bridge theorem already packages these two source inputs into the required
  -- determinant-rank coordinates.
  exact
    equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_projectiveDetPic
      k hpresent hdetPic

/-- Helper for Chap10 Example 10 55 5: once determinant-rank coordinates are available, the
explicit line-plus-rank class map becomes bijective and yields the target product decomposition. -/
private theorem equalEndpointProjectiveRankProduct_exists_of_detRankData
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k := by
  -- Determinant-rank coordinates make the explicit line-plus-rank class map bijective.
  have hbijective : Function.Bijective (equalEndpointLineRankClassMap k) := by
    exact equalEndpointLineRankClassMap_bijective_of_detRankExists k hdetRank
  -- The normalized product theorem gives the desired equivalence; the target only keeps the
  -- rank-coordinate computation.
  rcases equalEndpointProjectiveRankProduct_exists_of_lineRankClassMap_bijective k hbijective with
    ⟨e, hrank, _hline⟩
  exact ⟨e, hrank⟩

/-- Helper for Chap10 Example 10 55 5: comparing the endpoint-pair Picard boundary with a
residual boundary produces the Picard-to-rank-kernel equivalence needed by the line-rank
classification. -/
private theorem equalEndpointPicRankKernelEquiv_exists_of_endpointResidualBoundaryExact
    (hresidualBoundary :
      ∃ boundary : Additive (kˣ × kˣ) →+
          (equalEndpointProjectiveRankMap.{u, u} k).ker,
        Function.Surjective boundary ∧
          boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
          ∀ p : kˣ × kˣ,
            boundary (Additive.ofMul p) =
              equalEndpointLineResidualClass k (p.2 * p.1⁻¹)) :
    ∃ ePic : Additive (CommRing.Pic R) ≃+
        (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : kˣ,
        ePic (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
          equalEndpointLineResidualClass k unitRatio := by
  -- Compare the Picard and residual endpoint boundaries through the common ratio-map kernel, then
  -- evaluate the resulting equivalence on the normalized pair `(1, unitRatio)`.
  rcases equalEndpointEndpointPicBoundaryExact k with
    ⟨picBoundary, hpicSurj, hpicKer, hpicEval⟩
  rcases hresidualBoundary with
    ⟨residualBoundary, hresidualSurj, hresidualKer, hresidualEval⟩
  have hsameKer : residualBoundary.ker = picBoundary.ker := by
    calc
      residualBoundary.ker = (equalEndpointEndpointUnitRatioHom k).ker := hresidualKer
      _ = picBoundary.ker := hpicKer.symm
  rcases addEquivOfSurjectiveWithSameKernel_apply_exists
      (q := picBoundary) (boundary := residualBoundary)
      hpicSurj hresidualSurj hsameKer with
    ⟨ePic, hePic⟩
  refine ⟨ePic, ?_⟩
  intro unitRatio
  let p : kˣ × kˣ := (1, unitRatio)
  calc
    ePic (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
        ePic (picBoundary (Additive.ofMul p)) := by
          rw [hpicEval p]
          simp [p]
    _ = residualBoundary (Additive.ofMul p) := hePic (Additive.ofMul p)
    _ = equalEndpointLineResidualClass k unitRatio := by
          rw [hresidualEval p]
          simp [p]

/-- Helper for Chap10 Example 10 55 5: Picard surjectivity and a Picard-to-rank-kernel
equivalence formally imply bijectivity of the explicit line-plus-rank class map. -/
private theorem equalEndpointLineRankClassMap_bijective_of_picRankKernelEquiv
    (hpicKernel :
      ∃ ePic : Additive (CommRing.Pic R) ≃+
          (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∀ unitRatio : kˣ,
          ePic (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
            equalEndpointLineResidualClass k unitRatio) :
    Function.Bijective (equalEndpointLineRankClassMap k) := by
  -- The imported Picard-surjectivity theorem turns the Picard-to-kernel comparison into the
  -- normalized residual-line equivalence, which is exactly the input expected by the bijectivity
  -- bridge.
  have hpicSurj : Function.Surjective (equalEndpointLinePicHom k) :=
    equalEndpointLinePicHom_surjective k
  rcases equalEndpointLineResidualEquiv_exists_of_picHom_surjective_and_picRankKernelEquiv
      k hpicSurj hpicKernel with
    ⟨e, he⟩
  exact equalEndpointLineRankClassMap_bijective_of_lineResidualEquiv k e he

/-- Helper for Chap10 Example 10 55 5: endpoint-pair residual boundary exactness and Milnor-line
Picard surjectivity formally produce the normalized residual-line equivalence used by the
determinant-rank bridge. -/
private theorem equalEndpointLineResidualEquiv_exists
    (hresidualBoundary :
      ∃ boundary : Additive (kˣ × kˣ) →+
          (equalEndpointProjectiveRankMap.{u, u} k).ker,
        Function.Surjective boundary ∧
          boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
          ∀ p : kˣ × kˣ,
            boundary (Additive.ofMul p) =
              equalEndpointLineResidualClass k (p.2 * p.1⁻¹)) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- First convert the endpoint-pair boundary exactness package into the Picard-to-rank-kernel
  -- equivalence already isolated above.
  have hpicKernel :
      ∃ ePic : Additive (CommRing.Pic R) ≃+
          (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∀ unitRatio : kˣ,
          ePic (Additive.ofMul (equalEndpointLinePicClass k unitRatio)) =
            equalEndpointLineResidualClass k unitRatio :=
    equalEndpointPicRankKernelEquiv_exists_of_endpointResidualBoundaryExact k hresidualBoundary
  -- The imported Picard-surjectivity bridge then normalizes endpoint units directly to the rank
  -- kernel via residual Milnor-line classes.
  have hpicSurj : Function.Surjective (equalEndpointLinePicHom k) :=
    equalEndpointLinePicHom_surjective k
  exact equalEndpointLineResidualEquiv_exists_of_picHom_surjective_and_picRankKernelEquiv
    k hpicSurj hpicKernel

/-- Helper for Chap10 Example 10 55 5: after removing the stale Picard-kernel wrapper, the
remaining owner-level input is just the normalized residual-line equivalence from endpoint units
to the projective-rank kernel. -/
private theorem equalEndpointRankKernelEquiv_exists_of_picardCartanExact
    (hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ e : Additive kˣ ≃+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      ∀ unitRatio : Additive kˣ,
        e unitRatio = equalEndpointLineResidualClass k unitRatio.toMul := by
  -- The imported residual-equivalence bridge consumes exactly the Picard/Cartan exactness
  -- package, so the local wrapper should expose that surface directly.
  rcases hexact with ⟨hzero_pic, hsurj⟩
  exact equalEndpointLineResidualEquiv_exists_of_picardCartanClauses k hzero_pic hsurj

/-- Helper for Chap10 Example 10 55 5: Picard/Cartan exactness already implies the two source
clauses used by the determinant-rank bridge. -/
private theorem equalEndpointSourceClauses_of_picardCartanExact
    (hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    (∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) := by
  -- Convert the Picard/Cartan exactness clauses into bijectivity of the explicit line-rank map,
  -- then unpack that bijectivity into the generator normal form and residual injectivity.
  have hbijective : Function.Bijective (equalEndpointLineRankClassMap k) := by
    rcases hexact with ⟨hzero_pic, hsurj⟩
    exact equalEndpointLineRankClassMap_bijective_of_residualExact k hzero_pic hsurj
  exact (equalEndpointLineRankClassMap_bijective_iff_sourceClauses (k := k)).mp hbijective

/-- Helper for Chap10 Example 10 55 5: Picard/Cartan exactness is already enough to build the
determinant-rank coordinates consumed by the final product theorem. -/
private theorem equalEndpointProjectiveDetRankData_exists_of_picardCartanExact
    (hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- Route correction: instead of re-proving the geometric source clauses directly, pass through
  -- the already isolated exactness-to-source-clauses formal bridge.
  have hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    equalEndpointSourceClauses_of_picardCartanExact k hexact
  exact equalEndpointProjectiveDetRankData_exists_of_sourceClauses k hsource

/-- Helper for Chap10 Example 10 55 5: the generator normal-form and residual injectivity
source clauses already assemble the final product decomposition. -/
private theorem equalEndpointProjectiveRankProduct_exists_of_sourceClauses
    (hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v)) :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k := by
  -- First package the two source clauses as determinant-rank coordinates on projective `K₀`.
  have hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
    exact equalEndpointProjectiveDetRankData_exists_of_sourceClauses k hsource
  -- The determinant-rank bridge already proved above turns those coordinates into the product
  -- decomposition whose second coordinate is rank.
  exact equalEndpointProjectiveRankProduct_exists_of_detRankData k hdetRank

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations together with a
Picard-valued determinant coordinate already imply the residual Picard/Cartan exactness package.
-/
private theorem equalEndpointLinePicardCartanExact_of_presentations_and_detPic
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M))
    (hdetPic :
      ∃ detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R),
        ∀ unitRatio : kˣ,
          detPic (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) =
            Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    (∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) ∧
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- First assemble the determinant-rank package from the two geometric source inputs.
  have hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x)) :=
    equalEndpointProjectiveDetRankData_exists_of_presentations_and_detPic k hpresent hdetPic
  -- The determinant-rank bridge already proved in the imported prefix converts that package to
  -- the desired exactness clauses.
  exact equalEndpointLinePicardCartanExact_of_detRankExists k hdetRank

/-- Helper for Chap10 Example 10 55 5: a direct clutching linear-equivalence classification for
finite-projective generators packages immediately as vector-clutching presentations. -/
private theorem equalEndpointVectorClutchingPresentations_of_clutchingLinearEquiv
    (hclutching :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (A : Matrix ι ι k),
          A.det ≠ 0 ∧
            Nonempty (M.obj ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) A)) :
    ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M) := by
  intro M
  -- Choose the direct clutching normal form and transport projectivity across the chosen
  -- equivalence from the finite-projective generator.
  rcases hclutching M with ⟨ι, hfinite, hdecidable, A, hdet, hclutchingM⟩
  letI : Fintype ι := hfinite
  letI : DecidableEq ι := hdecidable
  rcases hclutchingM with ⟨e⟩
  have hprojective :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) A) := by
    -- The target clutching module is linearly equivalent to the chosen finite-projective
    -- generator, so projectivity transports across that equivalence.
    let _ : Module.Projective R M.obj := inferInstance
    exact Module.Projective.of_equiv' e
  exact equalEndpointVectorClutchingPresentation_of_linearEquiv (k := k) M A hdet hprojective e

/-- Helper for Chap10 Example 10 55 5: once a direct clutching linear-equivalence theorem and
the residual-zero Picard detector are available, the determinant-rank package is formal. -/
private theorem equalEndpointProjectiveDetRankData_exists_of_clutchingLinearEquiv_and_zeroPicClass
    (hclutching :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (A : Matrix ι ι k),
          A.det ≠ 0 ∧
            Nonempty (M.obj ≃ₗ[R] equalEndpointVectorClutchingModule (k := k) A))
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- First convert the direct clutching classification to the presentation surface consumed by
  -- the imported determinant-rank bridge.
  have hpresent :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        Nonempty (EqualEndpointVectorClutchingPresentation k M) :=
    equalEndpointVectorClutchingPresentations_of_clutchingLinearEquiv k hclutching
  -- The imported zero-Picard bridge then finishes the determinant-rank assembly.
  exact
    equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_zeroPicClass
      k hpresent hzero_pic

/-- Helper for Chap10 Example 10 55 5: a geometric line-product classification can be fed through
the existing diagonal-clutching adapter to obtain vector-clutching presentations for all
finite-projective generators. -/
private theorem equalEndpointVectorClutchingPresentations_of_lineProduct
    (hlineProduct :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : ι → kˣ),
          Nonempty (M.obj ≃ₗ[R] (equalEndpointLineProductProjectiveModule k D).obj)) :
    ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M) := by
  intro M
  -- Choose the line-product normal form and convert it to a clutching matrix presentation.
  rcases equalEndpointFiniteProjective_clutchingLinearEquiv_exists_of_lineProduct
      (k := k) M (hlineProduct M) with
    ⟨ι, hfinite, hdecidable, A, hdet, hclutching⟩
  letI : Fintype ι := hfinite
  letI : DecidableEq ι := hdecidable
  rcases hclutching with ⟨e⟩
  have hprojective :
      Module.Projective R (equalEndpointVectorClutchingModule (k := k) A) := by
    -- Transport projectivity across the chosen equivalence from the finite-projective generator.
    let _ : Module.Projective R M.obj := inferInstance
    exact Module.Projective.of_equiv' e
  exact
    equalEndpointVectorClutchingPresentation_of_linearEquiv (k := k) M A hdet hprojective e

/-- Helper for Chap10 Example 10 55 5: once the source line-product normal form is available, the
remaining local input is only residual-zero Picard detection on Milnor lines. -/
private theorem equalEndpointProjectiveDetRankData_exists_of_lineProduct_and_zeroPicClass
    (hlineProduct :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (D : ι → kˣ),
          Nonempty (M.obj ≃ₗ[R] (equalEndpointLineProductProjectiveModule k D).obj))
    (hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- First convert the geometric line-product theorem to clutching presentations, then consume the
  -- imported zero-Picard bridge with no further wrapper work.
  have hpresent :
      ∀ M : FiniteProjectiveModuleCat.{u, u} R,
        Nonempty (EqualEndpointVectorClutchingPresentation k M) :=
    equalEndpointVectorClutchingPresentations_of_lineProduct k hlineProduct
  exact
    equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_zeroPicClass
      k hpresent hzero_pic

/-- Helper for Chap10 Example 10 55 5: the no-argument closure reduces to the source clauses
consumed by the imported determinant-rank bridge. -/
private theorem equalEndpointSourceClauses_noArgs :
    (∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      (∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) := by
  -- Route correction: the final theorem should consume the smaller source-clause interface,
  -- not reopen the stale clutching-plus-zero-Pic wrapper route.
  -- TODO: prove the source clauses directly by combining a generator normal form for arbitrary
  -- finite-projective modules with a rank-one comparison showing residual equality preserves the
  -- Picard coordinate, then feed those two facts through the existing source-clause bridge.
  sorry

/-- Helper for Chap10 Example 10 55 5: the remaining no-argument input for the final wrapper is
the source-clause package, and the determinant-rank data is then formal. -/
private theorem equalEndpointProjectiveDetRankData_exists_noArgs :
    ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x)) := by
  -- The imported determinant-rank bridge only needs the generator normal form and residual
  -- injectivity source clauses isolated above.
  exact equalEndpointProjectiveDetRankData_exists_of_sourceClauses k
    (equalEndpointSourceClauses_noArgs k)

/-- Helper for Chap10 Example 10 55 5: once the no-argument determinant-rank package is in hand,
the Picard/Cartan exactness clauses are purely formal. -/
private theorem equalEndpointLinePicardCartanExact_noArgs :
    (∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) ∧
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- Route correction: exactness is also formal from the same source clauses, so it should not
  -- carry an independent owner-level blocker.
  exact equalEndpointLinePicardCartanExact_of_sourceClauses k
    (equalEndpointSourceClauses_noArgs k)

/-- Chap10 Example 10 55 5 Projective Clutching: the projective Grothendieck group of the
equal-endpoint ring is `Additive kˣ × ℤ`, with second coordinate given by rank. -/
theorem equalEndpointProjectiveRankProduct_exists :
    ∃ e : projectiveGrothendieckGroup.{u, u} R ≃+ Additive kˣ × ℤ,
      (AddMonoidHom.snd (Additive kˣ) ℤ).comp e.toAddMonoidHom =
        equalEndpointProjectiveRankMap.{u, u} k := by
  -- Route correction: the stable closure uses determinant-rank data directly, because the local
  -- det-rank-to-product bridge already avoids the stale exactness packaging.
  have hdetRank := equalEndpointProjectiveDetRankData_exists_noArgs k
  exact equalEndpointProjectiveRankProduct_exists_of_detRankData k hdetRank

end
