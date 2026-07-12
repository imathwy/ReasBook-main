import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Homotopy.Product
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_26.Corollary_4_43
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Exercise_4_10
import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Path.Homotopic

universe u𝕜 uE uH uG uGtilde

-- Semantic recall confirmed the canonical owners `LieGroup`,
-- `Manifold.IsUniversalSmoothCoveringMap`, and `ContMDiffMonoidMorphism` used below.

section UniversalCoveringGroup

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable [ConnectedSpace G]

omit [Group G] [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: products of simply connected spaces are simply connected. -/
theorem simplyConnectedSpace_prod {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A]
    {B : Type*} [TopologicalSpace B] [SimplyConnectedSpace B] :
    SimplyConnectedSpace (A × B) := by
  have hA :
      PathConnectedSpace A ∧
        ∀ {x y : A} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ :=
    (simply_connected_iff_paths_homotopic').mp (inferInstance : SimplyConnectedSpace A)
  have hB :
      PathConnectedSpace B ∧
        ∀ {x y : B} (p₁ p₂ : Path x y), Path.Homotopic p₁ p₂ :=
    (simply_connected_iff_paths_homotopic').mp (inferInstance : SimplyConnectedSpace B)
  have hPath : PathConnectedSpace (A × B) := by
    refine ⟨?_, ?_⟩
    · rcases hA.1.nonempty with ⟨a⟩
      rcases hB.1.nonempty with ⟨b⟩
      exact ⟨(a, b)⟩
    · intro x y
      -- Join the two coordinates separately, then take the product path.
      exact ⟨(hA.1.joined x.1 y.1).somePath.prod (hB.1.joined x.2 y.2).somePath⟩
  -- Detect simple connectivity by path connectedness and uniqueness of path classes.
  rw [simply_connected_iff_paths_homotopic']
  refine ⟨hPath, ?_⟩
  intro x y p q
  have hfst :
      projLeft (⟦p⟧ : Path.Homotopic.Quotient x y) =
        projLeft (⟦q⟧ : Path.Homotopic.Quotient x y) := by
    -- The left coordinate paths agree because the left factor is simply connected.
    simpa using Quotient.sound (hA.2 (p.map continuous_fst) (q.map continuous_fst))
  have hsnd :
      projRight (⟦p⟧ : Path.Homotopic.Quotient x y) =
        projRight (⟦q⟧ : Path.Homotopic.Quotient x y) := by
    -- The right coordinate paths agree for the same reason.
    simpa using Quotient.sound (hB.2 (p.map continuous_snd) (q.map continuous_snd))
  have hp :
      (⟦p⟧ : Path.Homotopic.Quotient x y) =
        prod (projLeft (⟦p⟧ : Path.Homotopic.Quotient x y))
          (projRight (⟦p⟧ : Path.Homotopic.Quotient x y)) := by
    -- Every path class in a product is reconstructed from its two projections.
    symm
    exact prod_projLeft_projRight (⟦p⟧ : Path.Homotopic.Quotient x y)
  have hq :
      prod (projLeft (⟦q⟧ : Path.Homotopic.Quotient x y))
          (projRight (⟦q⟧ : Path.Homotopic.Quotient x y)) =
        (⟦q⟧ : Path.Homotopic.Quotient x y) := by
    -- Apply the same reconstruction identity to `q`.
    exact prod_projLeft_projRight (⟦q⟧ : Path.Homotopic.Quotient x y)
  have hmid :
      prod (projLeft (⟦p⟧ : Path.Homotopic.Quotient x y))
          (projRight (⟦p⟧ : Path.Homotopic.Quotient x y)) =
        prod (projLeft (⟦q⟧ : Path.Homotopic.Quotient x y))
          (projRight (⟦q⟧ : Path.Homotopic.Quotient x y)) := by
    rw [hfst, hsnd]
  exact Quotient.exact (hp.trans (hmid.trans hq))

omit [Group G] [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: continuous lifts through a covering map are determined on a
preconnected domain by one point and the base composition. -/
theorem liftEqOfCompEqAtPoint {Gtilde : Type*} [TopologicalSpace Gtilde] [ChartedSpace H Gtilde]
    {π0 : Gtilde → G} (hπ0 : Manifold.IsSmoothCoveringMap I I π0) {A : Type*}
    [TopologicalSpace A] [PreconnectedSpace A] {F F' : A → Gtilde} (hF : Continuous F)
    (hF' : Continuous F') (hcomp : π0 ∘ F = π0 ∘ F') (a0 : A) (ha0 : F a0 = F' a0) :
    F = F' := by
  -- Reduce uniqueness of lifts to the covering-space uniqueness theorem.
  exact hπ0.isCoveringMap.eq_of_comp_eq hF hF' hcomp a0 ha0

omit [Group G] [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: smoothness of a lift is detected after composing with the covering
local diffeomorphism. -/
theorem contMDiff_ofCoverComp {Gtilde : Type*} [TopologicalSpace Gtilde] [ChartedSpace H Gtilde]
    {π0 : Gtilde → G} (hπ0 : Manifold.IsSmoothCoveringMap I I π0) {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners 𝕜 E' H'} {A : Type*} [TopologicalSpace A] [ChartedSpace H' A]
    {F : A → Gtilde} (hF : Continuous F) (hcomp : ContMDiff J I ∞ (π0 ∘ F)) :
    ContMDiff J I ∞ F := by
  -- Exercise 4.10 detects smoothness of a lift after composing with a smooth local diffeomorphism.
  exact (smooth_iff_comp_left_of_isLocalDiffeomorph hπ0.isLocalDiffeomorph hF).mpr hcomp

omit [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: the multiplication on `G` lifts to the universal cover after fixing a
point over `1`. -/
theorem existsLiftedMultiplicationAtIdentity {Gtilde : Type*} [TopologicalSpace Gtilde]
    [ChartedSpace H Gtilde] [SimplyConnectedSpace Gtilde] [LocPathConnectedSpace Gtilde]
    [LocPathConnectedSpace (Gtilde × Gtilde)]
    {π0 : Gtilde → G} (hπ0 : Manifold.IsUniversalSmoothCoveringMap I I π0)
    [IsTopologicalGroup G] (etilde : Gtilde) (h_etilde : π0 etilde = 1) :
    ∃ μ : C(Gtilde × Gtilde, Gtilde), μ (etilde, etilde) = etilde ∧
      ∀ p, π0 (μ p) = π0 p.1 * π0 p.2 := by
  let _ : SimplyConnectedSpace (Gtilde × Gtilde) := simplyConnectedSpace_prod
  have hπ0_cover : IsCoveringMap π0 := hπ0.isSmoothCoveringMap.isCoveringMap
  have hπ0_cont : Continuous π0 := hπ0_cover.continuous
  let πc : C(Gtilde, G) := ⟨π0, hπ0_cont⟩
  let mBase : C(Gtilde × Gtilde, G) := (πc.comp ContinuousMap.fst) * (πc.comp ContinuousMap.snd)
  have hmBase : π0 etilde = mBase (etilde, etilde) := by
    -- The chosen point over `1` normalizes the lifted multiplication at `(etilde, etilde)`.
    simp [mBase, πc, h_etilde]
  rcases hπ0_cover.existsUnique_continuousMap_lifts
      mBase (etilde, etilde) etilde hmBase with ⟨μ, hμ, -⟩
  refine ⟨μ, hμ.1, ?_⟩
  intro p
  -- The lift equation records that `μ` projects to the base multiplication.
  have hμ_comp' : π0 ∘ μ = fun q : Gtilde × Gtilde ↦ π0 q.1 * π0 q.2 := by
    simpa [mBase] using hμ.2
  exact congrFun hμ_comp' p

omit [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: inversion on `G` lifts to the universal cover after fixing a point
over `1`. -/
theorem existsLiftedInversionAtIdentity {Gtilde : Type*} [TopologicalSpace Gtilde]
    [ChartedSpace H Gtilde] [SimplyConnectedSpace Gtilde] [LocPathConnectedSpace Gtilde]
    {π0 : Gtilde → G} (hπ0 : Manifold.IsUniversalSmoothCoveringMap I I π0)
    [IsTopologicalGroup G] (etilde : Gtilde) (h_etilde : π0 etilde = 1) :
    ∃ ι : C(Gtilde, Gtilde), ι etilde = etilde ∧ ∀ x, π0 (ι x) = (π0 x)⁻¹ := by
  have hπ0_cover : IsCoveringMap π0 := hπ0.isSmoothCoveringMap.isCoveringMap
  have hπ0_cont : Continuous π0 := hπ0_cover.continuous
  let πc : C(Gtilde, G) := ⟨π0, hπ0_cont⟩
  let iBase : C(Gtilde, G) := πc⁻¹
  have hiBase : π0 etilde = iBase etilde := by
    -- The same normalization forces the lifted inverse to fix `etilde`.
    simp [iBase, πc, h_etilde]
  rcases hπ0_cover.existsUnique_continuousMap_lifts
      iBase etilde etilde hiBase with ⟨ι, hι, -⟩
  refine ⟨ι, hι.1, ?_⟩
  intro x
  -- The lift equation records that `ι` projects to inversion on the base.
  have hι_comp' : π0 ∘ ι = fun y : Gtilde ↦ (π0 y)⁻¹ := by
    simpa [iBase] using hι.2
  exact congrFun hι_comp' x

omit [ConnectedSpace G] in
/-- Helper for Theorem 7.7: once a universal smooth covering map `π0 : Gtilde → G` is given,
the Lie-group structure on `G` lifts to `Gtilde`, and `π0` becomes a smooth group homomorphism. -/
theorem existsLieGroupStructureOfUniversalSmoothCovering {Gtilde : Type uGtilde}
    [TopologicalSpace Gtilde] [ChartedSpace H Gtilde]
    [IsManifold I (⊤ : WithTop ℕ∞) Gtilde] [IsRCLikeNormedField 𝕜]
    [LocPathConnectedSpace Gtilde]
    [LocPathConnectedSpace (Gtilde × Gtilde)] {π0 : Gtilde → G}
    (hπ0 : Manifold.IsUniversalSmoothCoveringMap I I π0) :
    ∃ (_ : Group Gtilde) (_ : LieGroup I ∞ Gtilde)
      (π : ContMDiffMonoidMorphism I I ∞ Gtilde G),
      Manifold.IsUniversalSmoothCoveringMap I I π := by
  obtain ⟨etilde, h_etilde⟩ := hπ0.isSmoothCoveringMap.surjective 1
  let _ : SimplyConnectedSpace Gtilde := hπ0.simplyConnectedSpace
  let _ : IsManifold I ∞ Gtilde := IsManifold.of_le le_top
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  -- First lift multiplication and inversion with the chosen normalization over `1`.
  obtain ⟨μ, hμ_base, hμ_comp⟩ :=
    existsLiftedMultiplicationAtIdentity hπ0 etilde h_etilde
  obtain ⟨ι, hι_base, hι_comp⟩ :=
    existsLiftedInversionAtIdentity hπ0 etilde h_etilde
  let leftIdentityLift : C(Gtilde, Gtilde) :=
    μ.comp ((ContinuousMap.const Gtilde etilde).prodMk (ContinuousMap.id Gtilde))
  let _ : SimplyConnectedSpace (Gtilde × Gtilde) := simplyConnectedSpace_prod
  let _ : SimplyConnectedSpace ((Gtilde × Gtilde) × Gtilde) := simplyConnectedSpace_prod
  let leftAssocLift : C((Gtilde × Gtilde) × Gtilde, Gtilde) :=
    μ.comp ((μ.comp ContinuousMap.fst).prodMk ContinuousMap.snd)
  let rightAssocLift : C((Gtilde × Gtilde) × Gtilde, Gtilde) :=
    μ.comp ((ContinuousMap.fst.comp ContinuousMap.fst).prodMk
      (μ.comp ((ContinuousMap.snd.comp ContinuousMap.fst).prodMk ContinuousMap.snd)))
  let leftInverseLift : C(Gtilde, Gtilde) :=
    μ.comp (ι.prodMk (ContinuousMap.id Gtilde))
  let unitLift : C(Gtilde, Gtilde) := ContinuousMap.const Gtilde etilde
  have hπ0Smooth : Manifold.IsSmoothCoveringMap I I π0 := hπ0.isSmoothCoveringMap
  -- Covering uniqueness turns the lifted operations into the minimal group axioms.
  have hleftIdentity_comp : π0 ∘ leftIdentityLift = π0 ∘ ContinuousMap.id Gtilde := by
    funext x
    simpa [leftIdentityLift, h_etilde] using hμ_comp (etilde, x)
  have hleftIdentity_eq :
      (leftIdentityLift : Gtilde → Gtilde) = ContinuousMap.id Gtilde := by
    exact liftEqOfCompEqAtPoint hπ0Smooth leftIdentityLift.continuous
      (ContinuousMap.id Gtilde).continuous hleftIdentity_comp etilde
      (by simp [leftIdentityLift, hμ_base])
  have hleftAssoc_comp : π0 ∘ leftAssocLift = π0 ∘ rightAssocLift := by
    funext p
    rcases p with ⟨⟨x, y⟩, z⟩
    -- Both iterated lifts project to the same associative product on the base.
    simp [leftAssocLift, rightAssocLift, hμ_comp, mul_assoc]
  have hleftAssoc_eq :
      (leftAssocLift : ((Gtilde × Gtilde) × Gtilde) → Gtilde) = rightAssocLift := by
    exact liftEqOfCompEqAtPoint hπ0Smooth leftAssocLift.continuous
      rightAssocLift.continuous hleftAssoc_comp ((etilde, etilde), etilde)
      (by simp [leftAssocLift, rightAssocLift, hμ_base])
  have hleftInverse_comp : π0 ∘ leftInverseLift = π0 ∘ unitLift := by
    funext x
    -- The lifted inverse composes with the lifted multiplication to a lift of the constant `1`.
    simp [leftInverseLift, unitLift, hμ_comp, hι_comp, h_etilde]
  have hleftInverse_eq : (leftInverseLift : Gtilde → Gtilde) = unitLift := by
    exact liftEqOfCompEqAtPoint hπ0Smooth leftInverseLift.continuous
      unitLift.continuous hleftInverse_comp etilde
      (by simp [leftInverseLift, unitLift, hμ_base, hι_base])
  let _ : One Gtilde := ⟨etilde⟩
  let _ : Mul Gtilde := ⟨fun x y ↦ μ (x, y)⟩
  let _ : Inv Gtilde := ⟨ι⟩
  have h_one_mul : ∀ x : Gtilde, 1 * x = x := by
    intro x
    -- The left-identity lift is the identity map on the cover.
    simpa [leftIdentityLift] using congrFun hleftIdentity_eq x
  have h_mul_assoc : ∀ x y z : Gtilde, (x * y) * z = x * (y * z) := by
    intro x y z
    -- Associativity follows from equality of the two lifted triple products.
    simpa [leftAssocLift, rightAssocLift] using congrFun hleftAssoc_eq ((x, y), z)
  have h_inv_mul_cancel : ∀ x : Gtilde, x⁻¹ * x = 1 := by
    intro x
    -- The left-inverse lift is forced to be the constant map at the identity.
    simpa [leftInverseLift, unitLift] using congrFun hleftInverse_eq x
  let instGroup : Group Gtilde := Group.ofLeftAxioms h_mul_assoc h_one_mul h_inv_mul_cancel
  let _ : Group Gtilde := instGroup
  -- Next transport smoothness of the lifted operations through the covering local diffeomorphism.
  have hπ0ContMDiff : ContMDiff I I ∞ π0 := hπ0Smooth.isLocalDiffeomorph.contMDiff
  have hmulBaseContMDiff :
      ContMDiff (I.prod I) I ∞ (fun p : Gtilde × Gtilde ↦ π0 p.1 * π0 p.2) := by
    -- The base product is smooth because `π0` is smooth and multiplication is smooth on `G`.
    exact (hπ0ContMDiff.comp contMDiff_fst).mul (hπ0ContMDiff.comp contMDiff_snd)
  have hμCompEq :
      π0 ∘ (μ : Gtilde × Gtilde → Gtilde) = fun p : Gtilde × Gtilde ↦ π0 p.1 * π0 p.2 := by
    funext p
    exact hμ_comp p
  have hμCompContMDiff : ContMDiff (I.prod I) I ∞ (π0 ∘ μ) := by
    -- Rewrite the lifted multiplication into the already smooth base multiplication.
    simpa [hμCompEq] using hmulBaseContMDiff
  have hμContMDiff : ContMDiff (I.prod I) I ∞ μ :=
    contMDiff_ofCoverComp hπ0Smooth μ.continuous hμCompContMDiff
  have hinvBaseContMDiff : ContMDiff I I ∞ (fun x : Gtilde ↦ (π0 x)⁻¹) := by
    -- The base inverse is smooth because `π0` is smooth and inversion is smooth on `G`.
    exact hπ0ContMDiff.inv
  have hιCompEq : π0 ∘ (ι : Gtilde → Gtilde) = fun x : Gtilde ↦ (π0 x)⁻¹ := by
    funext x
    exact hι_comp x
  have hιCompContMDiff : ContMDiff I I ∞ (π0 ∘ ι) := by
    -- Rewrite the lifted inverse into the already smooth base inverse.
    simpa [hιCompEq] using hinvBaseContMDiff
  have hιContMDiff : ContMDiff I I ∞ ι :=
    contMDiff_ofCoverComp hπ0Smooth ι.continuous hιCompContMDiff
  have hcontMDiff_mul : ContMDiff (I.prod I) I ∞ fun p : Gtilde × Gtilde ↦ p.1 * p.2 := by
    -- The transported multiplication is definitionally the lifted map `μ`.
    simpa using hμContMDiff
  have hcontMDiff_inv : ContMDiff I I ∞ fun x : Gtilde ↦ x⁻¹ := by
    -- The transported inverse is definitionally the lifted map `ι`.
    simpa using hιContMDiff
  let instLieGroup : LieGroup I ∞ Gtilde :=
    { contMDiff_mul := hcontMDiff_mul
      contMDiff_inv := hcontMDiff_inv }
  let _ : LieGroup I ∞ Gtilde := instLieGroup
  have hπ_map_one : π0 (1 : Gtilde) = 1 := by
    -- The chosen basepoint `etilde` becomes the identity element on the cover.
    simpa using h_etilde
  have hπ_map_mul : ∀ x y : Gtilde, π0 (x * y) = π0 x * π0 y := by
    intro x y
    -- The lifted multiplication was defined to project to multiplication on `G`.
    simpa using hμ_comp (x, y)
  let π : ContMDiffMonoidMorphism I I ∞ Gtilde G :=
    { toMonoidHom :=
        { toFun := π0
          map_one' := hπ_map_one
          map_mul' := hπ_map_mul }
      contMDiff_toFun := hπ0ContMDiff }
  have hπ : Manifold.IsUniversalSmoothCoveringMap I I π := by
    -- Packaging `π0` as a smooth monoid morphism does not change the underlying covering map.
    simpa [π] using hπ0
  exact ⟨instGroup, instLieGroup, π, hπ⟩

omit [Group G] [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.7: a charted space modeled on a real-analytic manifold model is locally
path-connected. -/
theorem chartedSpaceLocPathConnectedSpace
    {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [IsRCLikeNormedField 𝕜']
    {ES : Type*} [NormedAddCommGroup ES] [NormedSpace 𝕜' ES]
    {HS : Type*} [TopologicalSpace HS] {J : ModelWithCorners 𝕜' ES HS}
    {S : Type*} [TopologicalSpace S] [ChartedSpace HS S] :
    LocPathConnectedSpace S := by
  -- First transport local path connectedness from the convex model range to the model space.
  letI : RCLike 𝕜' := IsRCLikeNormedField.rclike 𝕜'
  letI : NormedSpace ℝ ES := NormedSpace.restrictScalars ℝ 𝕜' ES
  letI : LocPathConnectedSpace HS := by
    letI : LocPathConnectedSpace (Set.range J) := J.convex_range.locPathConnectedSpace
    let e : HS ≃ₜ Set.range J := J.isClosedEmbedding.toHomeomorph
    exact e.isOpenEmbedding.locPathConnectedSpace
  -- Then the charted-space atlas propagates that local path connectedness to the manifold.
  exact ChartedSpace.locPathConnectedSpace HS S

-- Lee's theorem is stated for real Lie groups, so the public theorem is specialized to `ℝ`.
-- The later proof can combine the universal smooth covering manifold with the lifted group
-- structure constructed above.
/-- Theorem 7.7 (Existence of a Universal Covering Group). Every connected real Lie group `G`
admits a simply connected Lie group `Gtilde` together with a smooth covering map
`Gtilde → G` that is also a Lie group homomorphism. -/
theorem exists_universal_covering_group
    {EReal : Type uE} [NormedAddCommGroup EReal] [NormedSpace ℝ EReal]
    {HReal : Type uH} [TopologicalSpace HReal]
    {IReal : ModelWithCorners ℝ EReal HReal}
    {GReal : Type uG} [Group GReal] [TopologicalSpace GReal] [ChartedSpace HReal GReal]
    [IsManifold IReal (⊤ : WithTop ℕ∞) GReal] [LieGroup IReal ∞ GReal] [ConnectedSpace GReal] :
    ∃ (Gtilde : Type uGtilde) (_ : Group Gtilde) (_ : TopologicalSpace Gtilde)
      (_ : ChartedSpace HReal Gtilde) (_ : IsManifold IReal (⊤ : WithTop ℕ∞) Gtilde)
      (_ : LieGroup IReal ∞ Gtilde)
      (π : ContMDiffMonoidMorphism IReal IReal ∞ Gtilde GReal),
      Manifold.IsUniversalSmoothCoveringMap IReal IReal π := by
  -- Route correction: the public theorem is a wrapper around the universal covering manifold
  -- theorem and the already constructed lifted Lie-group structure.
  rcases
      (exists_universal_smooth_covering_manifold.{0, uE, uH, uG, uGtilde, uE, uH, uG}
        (I := IReal) (M := GReal)) with
    ⟨Gtilde, instTop, instCharted, instManifold, π0, hπ0, _⟩
  let _ : TopologicalSpace Gtilde := instTop
  let _ : ChartedSpace HReal Gtilde := instCharted
  let _ : IsManifold IReal (⊤ : WithTop ℕ∞) Gtilde := instManifold
  -- The lifting theorem needs local path connectedness on the cover and its product.
  let _ : LocPathConnectedSpace Gtilde := chartedSpaceLocPathConnectedSpace (J := IReal)
  let _ : LocPathConnectedSpace (Gtilde × Gtilde) :=
    chartedSpaceLocPathConnectedSpace (J := IReal.prod IReal)
  -- Apply the internal lifting theorem to endow the universal cover with the Lie-group structure.
  obtain ⟨instGroup, instLieGroup, π, hπ⟩ :=
    existsLieGroupStructureOfUniversalSmoothCovering
      (I := IReal) (G := GReal) (Gtilde := Gtilde) hπ0
  exact ⟨Gtilde, instGroup, instTop, instCharted, instManifold, instLieGroup, π, hπ⟩

end UniversalCoveringGroup
