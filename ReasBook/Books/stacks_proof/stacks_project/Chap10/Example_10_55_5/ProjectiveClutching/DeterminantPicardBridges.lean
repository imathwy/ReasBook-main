import StacksProject_2024.Chap10.Example_10_55_5.ProjectiveClutching.InvertibleSubmoduleBoundary

noncomputable section

universe u v w

section

variable (k : Type u) [Field k]

local notation "R" => equal_endpoint_poly_subring k

/-- Helper for Chap10 Example 10 55 5: determinant-rank data gives the source clauses
for the line-plus-rank class map. -/
theorem equalEndpointSourceClauses_of_detRank
    (det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ)
    (hline : ∀ unitRatio : kˣ,
      det (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio)
    (hinj : Function.Injective
      (fun x : projectiveGrothendieckGroup.{u, u} R =>
        (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    (∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  constructor
  · intro M
    -- Choose the line coordinate by subtracting the determinant of the rank section from the
    -- determinant of the generator.  Joint determinant-rank injectivity then identifies the
    -- generator with the corresponding line-plus-rank class.
    let x : projectiveGrothendieckGroup.{u, u} R := projectiveGrothendieckGroupOf R M
    let n : ℤ := equalEndpointProjectiveRank k M
    let rankSection : projectiveGrothendieckGroup.{u, u} R :=
      equalEndpointProjectiveRankSection k n
    let unitRatio : kˣ := (det x - det rankSection).toMul
    refine ⟨unitRatio, ?_⟩
    apply hinj
    apply Prod.ext
    · have htag : Additive.ofMul unitRatio = det x - det rankSection := by
        -- The chosen unit is just the multiplicative form of the additive determinant
        -- difference.
        dsimp [unitRatio]
      have hdet :
          det (equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, n)) = det x := by
        calc
          det (equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, n)) =
              det ((equalEndpointLineResidualClass k unitRatio :
                projectiveGrothendieckGroup.{u, u} R) + rankSection) := by
                rw [equalEndpointLineRankClassMap_apply]
                simp [rankSection]
          _ =
              det (equalEndpointLineResidualClass k unitRatio :
                projectiveGrothendieckGroup.{u, u} R) + det rankSection := by
                rw [map_add]
          _ = Additive.ofMul unitRatio + det rankSection := by
                rw [hline unitRatio]
          _ = (det x - det rankSection) + det rankSection := by
                rw [htag]
          _ = det x := sub_add_cancel (det x) (det rankSection)
      exact hdet.symm
    · have hxrank :
          equalEndpointProjectiveRankMap.{u, u} k x = n := by
        -- On projective generators, the generic-rank map is by definition the projective rank.
        simpa [x, n] using equalEndpointProjectiveRankMap_apply_of k M
      have hmaprank :
          equalEndpointProjectiveRankMap.{u, u} k
              (equalEndpointLineRankClassMap k (Additive.ofMul unitRatio, n)) = n := by
        have hrank :=
          DFunLike.congr_fun (equalEndpointLineRankClassMap_rank k)
            (Additive.ofMul unitRatio, n)
        simpa [AddMonoidHom.comp_apply] using hrank
      exact hxrank.trans hmaprank.symm
  · intro u v hresidual
    -- The determinant coordinate computes residual-line classes as endpoint-unit ratios, so
    -- equality of residual classes forces equality of the units.
    have htag : Additive.ofMul u = Additive.ofMul v := by
      calc
        Additive.ofMul u =
            det (equalEndpointLineResidualClass k u :
              projectiveGrothendieckGroup.{u, u} R) := (hline u).symm
        _ = det (equalEndpointLineResidualClass k v :
              projectiveGrothendieckGroup.{u, u} R) := by
            exact congrArg
              (fun z : (equalEndpointProjectiveRankMap.{u, u} k).ker => det z.1)
              hresidual
        _ = Additive.ofMul v := hline v
    simpa using congrArg Additive.toMul htag

/-- Helper for Chap10 Example 10 55 5: an existential determinant-rank package gives the
source clauses for the residual-boundary proof. -/
theorem equalEndpointSourceClauses_of_detRankExists
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    (∀ M : FiniteProjectiveModuleCat.{u, u} R,
      ∃ unitRatio : kˣ,
        projectiveGrothendieckGroupOf R M =
          equalEndpointLineRankClassMap k
            (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
      ∀ u v : kˣ,
        equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  -- Unpack the determinant-rank package and consume the pointwise source-clause adapter.
  rcases hdetRank with ⟨det, hline, hinj⟩
  exact equalEndpointSourceClauses_of_detRank k det hline hinj

/-- Helper for Chap10 Example 10 55 5: determinant-rank coordinates are equivalent to the
generator line-rank normal form together with residual-line injectivity. -/
theorem equalEndpointProjectiveDetRankData_exists_iff_sourceClauses :
    (∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x))) ↔
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  constructor
  · -- Determinant and rank separate projective classes, so they recover both source clauses.
    exact equalEndpointSourceClauses_of_detRankExists k
  · -- Conversely, the source clauses make the explicit line-rank map bijective and yield
    -- determinant-rank coordinates from its inverse.
    exact equalEndpointProjectiveDetRankData_exists_of_sourceClauses k

/-- Helper for Chap10 Example 10 55 5: determinant-rank data makes the explicit line-plus-rank
class map bijective. -/
theorem equalEndpointLineRankClassMap_bijective_of_detRankExists
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    Function.Bijective (equalEndpointLineRankClassMap k) := by
  -- Determinant-rank coordinates give the generator normal form and residual injectivity, which
  -- are exactly the two halves of bijectivity for the line-plus-rank map.
  exact equalEndpointLineRankClassMap_bijective_of_sourceClauses (k := k)
    (equalEndpointSourceClauses_of_detRankExists k hdetRank)

/-- Helper for Chap10 Example 10 55 5: determinant-rank data is equivalent to bijectivity of the
explicit line-plus-rank class map. -/
theorem equalEndpointProjectiveDetRankData_exists_iff_lineRankClassMap_bijective :
    (∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
      (∀ unitRatio : kˣ,
        det (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
        Function.Injective
          (fun x : projectiveGrothendieckGroup.{u, u} R =>
            (det x, equalEndpointProjectiveRankMap.{u, u} k x))) ↔
      Function.Bijective (equalEndpointLineRankClassMap k) := by
  constructor
  · -- The forward direction extracts the source clauses from determinant-rank data.
    exact equalEndpointLineRankClassMap_bijective_of_detRankExists k
  · -- The reverse direction reads determinant and rank from the inverse line-rank coordinates.
    exact equalEndpointProjectiveDetRankData_exists_of_lineRankClassMap_bijective k

/-- Helper for Chap10 Example 10 55 5: generator normal form and residual-line injectivity
imply the Picard/Cartan exactness package for residual Milnor-line classes. -/
theorem equalEndpointLinePicardCartanExact_of_sourceClauses
    (hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v) :
    (∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) ∧
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- The source clauses are exactly bijectivity of the line-plus-rank class map; the existing
  -- equivalence translates that bijectivity into the Picard/Cartan exactness package.
  have hbijective : Function.Bijective (equalEndpointLineRankClassMap k) :=
    equalEndpointLineRankClassMap_bijective_of_sourceClauses (k := k) hsource
  exact (equalEndpointLineRankClassMap_bijective_iff_residualExact (k := k)).mp hbijective

/-- Helper for Chap10 Example 10 55 5: determinant-rank data gives the Picard/Cartan exactness
package for residual Milnor-line classes. -/
theorem equalEndpointLinePicardCartanExact_of_detRankExists
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    (∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1) ∧
      ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
        ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z := by
  -- First turn the determinant-rank invariant into the source normal form and residual
  -- injectivity clauses.
  have hsource :
      (∀ M : FiniteProjectiveModuleCat.{u, u} R,
        ∃ unitRatio : kˣ,
          projectiveGrothendieckGroupOf R M =
            equalEndpointLineRankClassMap k
              (Additive.ofMul unitRatio, equalEndpointProjectiveRank k M)) ∧
        ∀ u v : kˣ,
          equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    equalEndpointSourceClauses_of_detRankExists k hdetRank
  -- The existing line-rank formal equivalence converts those source clauses into exactness.
  exact equalEndpointLinePicardCartanExact_of_sourceClauses k hsource

/-- Helper for Chap10 Example 10 55 5: determinant-rank data gives endpoint-pair residual
boundary exactness. -/
theorem equalEndpointEndpointResidualBoundaryExact_of_detRankExists
    (hdetRank :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        (∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) ∧
          Function.Injective
            (fun x : projectiveGrothendieckGroup.{u, u} R =>
              (det x, equalEndpointProjectiveRankMap.{u, u} k x))) :
    ∃ boundary :
        Additive (kˣ × kˣ) →+ (equalEndpointProjectiveRankMap.{u, u} k).ker,
      Function.Surjective boundary ∧
        boundary.ker = (equalEndpointEndpointUnitRatioHom k).ker ∧
        ∀ p : kˣ × kˣ,
          boundary (Additive.ofMul p) =
            equalEndpointLineResidualClass k (p.2 * p.1⁻¹) := by
  -- The determinant-rank invariant supplies the Picard/Cartan package, and the endpoint
  -- boundary adapter performs the quotient-level assembly.
  have hexact :
      (∀ unitRatio : kˣ,
        equalEndpointLineResidualClass k unitRatio = 0 →
          equalEndpointLinePicClass k unitRatio = 1) ∧
        ∀ z : (equalEndpointProjectiveRankMap.{u, u} k).ker,
          ∃ unitRatio : kˣ, equalEndpointLineResidualClass k unitRatio = z :=
    equalEndpointLinePicardCartanExact_of_detRankExists k hdetRank
  exact equalEndpointEndpointResidualBoundaryExact_of_picardCartanExact k hexact

/-- Helper for Chap10 Example 10 55 5: a Picard-valued determinant coordinate detects when a
residual Milnor-line class has trivial Picard class. -/
theorem equalEndpointLineResidualClass_zero_picClass_one_of_projectiveDetPic
    (detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R))
    (hdetPic : ∀ unitRatio : kˣ,
      detPic (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) =
        Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1 := by
  intro unitRatio hzero
  -- Apply the determinant coordinate to the residual-zero equality and read the additive Picard
  -- zero back as the multiplicative Picard identity.
  have hpicTag :
      Additive.ofMul (equalEndpointLinePicClass k unitRatio) = 0 := by
    calc
      Additive.ofMul (equalEndpointLinePicClass k unitRatio) =
          detPic (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) := (hdetPic unitRatio).symm
      _ = detPic ((0 : (equalEndpointProjectiveRankMap.{u, u} k).ker) :
            projectiveGrothendieckGroup.{u, u} R) := by
            exact congrArg
              (fun z : (equalEndpointProjectiveRankMap.{u, u} k).ker =>
                detPic (z : projectiveGrothendieckGroup.{u, u} R))
              hzero
      _ = 0 := by
            simp
  simpa using congrArg Additive.toMul hpicTag

/-- Helper for Chap10 Example 10 55 5: an existential Picard-valued determinant coordinate
detects residual-zero Milnor-line classes. -/
theorem equalEndpointLineResidualClass_zero_picClass_one_of_projectiveDetPic_exists
    (hdetPic :
      ∃ detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R),
        ∀ unitRatio : kˣ,
          detPic (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) =
            Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1 := by
  -- Choose the determinant coordinate once, then use the pointwise Picard detector above.
  rcases hdetPic with ⟨detPic, hdetPic⟩
  exact equalEndpointLineResidualClass_zero_picClass_one_of_projectiveDetPic k detPic hdetPic

/-- Helper for Chap10 Example 10 55 5: a Picard-valued determinant coordinate which computes
Milnor residual lines separates endpoint-unit ratios. -/
theorem equalEndpointLineResidualClass_injective_of_projectiveDetPic
    (detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R))
    (hdetPic : ∀ unitRatio : kˣ,
      detPic (equalEndpointLineResidualClass k unitRatio :
        projectiveGrothendieckGroup.{u, u} R) =
        Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  -- The determinant-to-Picard coordinate gives the residual-zero Picard detector; the established
  -- residual product law then converts equality to a quotient residual-zero statement.
  exact equalEndpointLineResidualClass_injective_of_zero_picClass (k := k)
    (equalEndpointLineResidualClass_mul k)
    (equalEndpointLineResidualClass_zero_picClass_one_of_projectiveDetPic k detPic hdetPic)

/-- Helper for Chap10 Example 10 55 5: an existential Picard-valued determinant coordinate
separates residual Milnor-line classes. -/
theorem equalEndpointLineResidualClass_injective_of_projectiveDetPic_exists
    (hdetPic :
      ∃ detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R),
        ∀ unitRatio : kˣ,
          detPic (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) =
            Additive.ofMul (equalEndpointLinePicClass k unitRatio)) :
    ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v := by
  -- Choose the determinant coordinate and reuse the pointwise Picard-coordinate detector.
  rcases hdetPic with ⟨detPic, hdetPic⟩
  exact equalEndpointLineResidualClass_injective_of_projectiveDetPic k detPic hdetPic

/-- Helper for Chap10 Example 10 55 5: a determinant coordinate normalized on residual
Milnor-line classes gives the Picard-valued residual coordinate and kills the free class after
projecting away the generic-rank section. -/
theorem equalEndpointProjectiveDetPic_residualData_exists_of_detCoordinate
    (hdet :
      ∃ det : projectiveGrothendieckGroup.{u, u} R →+ Additive kˣ,
        ∀ unitRatio : kˣ,
          det (equalEndpointLineResidualClass k unitRatio :
            projectiveGrothendieckGroup.{u, u} R) = Additive.ofMul unitRatio) :
    ∃ detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R),
      (∀ unitRatio : kˣ,
        detPic (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) =
          Additive.ofMul (equalEndpointLinePicClass k unitRatio)) ∧
        detPic (equalEndpointProjectiveFreeClass k) = 0 := by
  rcases hdet with ⟨det, hdet_line⟩
  let linePicAddHom : Additive kˣ →+ Additive (CommRing.Pic R) :=
    MonoidHom.toAdditive (equalEndpointLinePicHom k)
  let rankKernelProjection : projectiveGrothendieckGroup.{u, u} R →+
      projectiveGrothendieckGroup.{u, u} R :=
    AddMonoidHom.id _ -
      (equalEndpointProjectiveRankSection k).comp (equalEndpointProjectiveRankMap.{u, u} k)
  let detPic : projectiveGrothendieckGroup.{u, u} R →+ Additive (CommRing.Pic R) :=
    linePicAddHom.comp (det.comp rankKernelProjection)
  refine ⟨detPic, ?_, ?_⟩
  · intro unitRatio
    -- Residual line classes already have rank zero, so the rank-kernel projection fixes them and
    -- the determinant coordinate reads off the endpoint unit.
    have hrank :
        equalEndpointProjectiveRankMap.{u, u} k
            (equalEndpointLineResidualClass k unitRatio :
              projectiveGrothendieckGroup.{u, u} R) = 0 :=
      (equalEndpointLineResidualClass k unitRatio).2
    have hprojection :
        rankKernelProjection (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) =
            (equalEndpointLineResidualClass k unitRatio :
              projectiveGrothendieckGroup.{u, u} R) := by
      simp [rankKernelProjection, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply,
        equalEndpointProjectiveRankSection_apply, hrank]
    calc
      detPic (equalEndpointLineResidualClass k unitRatio :
          projectiveGrothendieckGroup.{u, u} R) =
          linePicAddHom
            (det (rankKernelProjection
              (equalEndpointLineResidualClass k unitRatio :
                projectiveGrothendieckGroup.{u, u} R))) := rfl
      _ = linePicAddHom
            (det (equalEndpointLineResidualClass k unitRatio :
              projectiveGrothendieckGroup.{u, u} R)) := by
          rw [hprojection]
      _ = linePicAddHom (Additive.ofMul unitRatio) := by
          rw [hdet_line unitRatio]
      _ = Additive.ofMul (equalEndpointLinePicClass k unitRatio) := by
          simp [linePicAddHom, equalEndpointLinePicHom_apply]
  · -- The free rank-one class is exactly the rank section at `1`, so projecting away the rank
    -- section sends it to zero before applying the determinant/Picard coordinate.
    have hrank :
        equalEndpointProjectiveRankMap.{u, u} k (equalEndpointProjectiveFreeClass k) = 1 :=
      equalEndpointProjectiveRankMap_freeClass k
    have hprojection :
        rankKernelProjection (equalEndpointProjectiveFreeClass k) = 0 := by
      dsimp [rankKernelProjection]
      change
        equalEndpointProjectiveFreeClass k -
            equalEndpointProjectiveRankSection k
              (equalEndpointProjectiveRankMap.{u, u} k (equalEndpointProjectiveFreeClass k)) =
          0
      rw [hrank, equalEndpointProjectiveRankSection_apply]
      simp
    calc
      detPic (equalEndpointProjectiveFreeClass k) =
          linePicAddHom (det (rankKernelProjection (equalEndpointProjectiveFreeClass k))) := rfl
      _ = linePicAddHom (det 0) := by rw [hprojection]
      _ = 0 := by simp [linePicAddHom]

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations and residual-zero
Picard detection already give the determinant-rank package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_zeroPicClass
    (hpresent : ∀ M : FiniteProjectiveModuleCat.{u, u} R,
      Nonempty (EqualEndpointVectorClutchingPresentation k M))
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
  -- The Picard detector turns residual equality into equality of endpoint ratios.
  have hresidual_injective : ∀ u v : kˣ,
      equalEndpointLineResidualClass k u = equalEndpointLineResidualClass k v → u = v :=
    equalEndpointLineResidualClass_injective_of_zero_picClass k
      (equalEndpointLineResidualClass_mul k) hzero_pic
  -- Once residual classes are injective, the existing vector-clutching adapter builds the
  -- determinant coordinate and proves joint injectivity with rank.
  exact equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_residual_injective
    k hpresent hresidual_injective

/-- Helper for Chap10 Example 10 55 5: vector-clutching presentations together with a
Picard-valued determinant coordinate give the determinant-rank package. -/
theorem equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_projectiveDetPic
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
  -- The Picard-valued determinant only needs to be consumed through its residual-zero detector.
  rcases hdetPic with ⟨detPic, hdetPic⟩
  have hzero_pic : ∀ unitRatio : kˣ,
      equalEndpointLineResidualClass k unitRatio = 0 →
        equalEndpointLinePicClass k unitRatio = 1 :=
    equalEndpointLineResidualClass_zero_picClass_one_of_projectiveDetPic k detPic hdetPic
  exact equalEndpointProjectiveDetRankData_exists_of_vectorClutchingPresentations_and_zeroPicClass
    k hpresent hzero_pic


end
