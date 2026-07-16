import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_26.Definition_4_26_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap07.Sec07_47.Definition_7_47_extra_1
import Mathlib.Topology.Homotopy.Lifting

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uG uEtilde uHtilde uGtilde uEtilde' uHtilde' uGtilde'

-- Semantic recall: `lean_leansearch` points to
-- `IsCoveringMap.existsUnique_continuousMap_lifts` as the canonical covering-space uniqueness
-- owner behind the comparison map over the base; the source item strengthens that comparison to a
-- Lie group isomorphism over `G`.

section UniversalCoveringGroup

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
variable [ConnectedSpace G]
variable {Etilde : Type uEtilde} [NormedAddCommGroup Etilde] [NormedSpace 𝕜 Etilde]
variable {Htilde : Type uHtilde} [TopologicalSpace Htilde]
variable {Itilde : ModelWithCorners 𝕜 Etilde Htilde}
variable {Gtilde : Type uGtilde} [Group Gtilde] [TopologicalSpace Gtilde]
  [ChartedSpace Htilde Gtilde] [LieGroup Itilde ∞ Gtilde]
variable {Etilde' : Type uEtilde'} [NormedAddCommGroup Etilde'] [NormedSpace 𝕜 Etilde']
variable {Htilde' : Type uHtilde'} [TopologicalSpace Htilde']
variable {Itilde' : ModelWithCorners 𝕜 Etilde' Htilde'}
variable {Gtilde' : Type uGtilde'} [Group Gtilde'] [TopologicalSpace Gtilde']
  [ChartedSpace Htilde' Gtilde'] [LieGroup Itilde' ∞ Gtilde']

/-- Helper for Theorem 7.9: a charted space modeled on a real manifold model is locally
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
  -- Then the charted-space atlas propagates local path connectedness to the manifold itself.
  exact ChartedSpace.locPathConnectedSpace HS S

/-- Helper for Theorem 7.9: continuous lifts through a smooth covering map are determined on a
preconnected domain by one point and the base composition. -/
lemma liftEqOfCompEqAtPoint
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {H₀ : Type*} [TopologicalSpace H₀]
    {I₀ : ModelWithCorners 𝕜 E₀ H₀}
    {M₀ : Type*} [TopologicalSpace M₀] [ChartedSpace H₀ M₀]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {π₀ : M₀ → M₁} (hπ₀ : Manifold.IsSmoothCoveringMap I₀ I₁ π₀) {A : Type*}
    [TopologicalSpace A] [PreconnectedSpace A] {F F' : A → M₀} (hF : Continuous F)
    (hF' : Continuous F') (hcomp : π₀ ∘ F = π₀ ∘ F') (a₀ : A) (ha₀ : F a₀ = F' a₀) :
    F = F' := by
  -- Reduce uniqueness of lifts to the underlying covering-space uniqueness theorem.
  exact hπ₀.isCoveringMap.eq_of_comp_eq hF hF' hcomp a₀ ha₀

omit [LieGroup I ∞ G] [ConnectedSpace G] in
/-- Helper for Theorem 7.9: a universal smooth covering homomorphism over `G` admits a comparison
lift from any other universal smooth covering homomorphism, normalized at the identity. -/
lemma existsComparisonContinuousLift
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {G₁ : Type*} [Group G₁] [TopologicalSpace G₁] [ChartedSpace H₁ G₁] [LieGroup I₁ ∞ G₁]
    [LocPathConnectedSpace G₁]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {G₂ : Type*} [Group G₂] [TopologicalSpace G₂] [ChartedSpace H₂ G₂] [LieGroup I₂ ∞ G₂]
    (π₁ : ContMDiffMonoidMorphism I₁ I ∞ G₁ G)
    (hπ₁ : Manifold.IsUniversalSmoothCoveringMap I₁ I π₁)
    (π₂ : ContMDiffMonoidMorphism I₂ I ∞ G₂ G)
    (hπ₂ : Manifold.IsUniversalSmoothCoveringMap I₂ I π₂) :
    ∃ F : C(G₁, G₂), F 1 = 1 ∧ π₂ ∘ F = π₁ := by
  let _ : SimplyConnectedSpace G₁ := hπ₁.simplyConnectedSpace
  have hπ₂cover : IsCoveringMap π₂ := hπ₂.isSmoothCoveringMap.isCoveringMap
  let π₁c : C(G₁, G) := ⟨π₁, π₁.contMDiff_toFun.continuous⟩
  -- Lift `π₁` through the universal covering `π₂`, normalized at the identity.
  rcases hπ₂cover.existsUnique_continuousMap_lifts π₁c 1 (1 : G₂) (by simp [π₁c]) with
    ⟨F, hF, -⟩
  refine ⟨F, hF.1, ?_⟩
  -- The lifted map projects back to `π₁` by construction.
  simpa [π₁c] using hF.2

/-- Helper for Theorem 7.9: a continuous map that factors through a smooth local diffeomorphism
is smooth once the composite is smooth. -/
lemma contMDiff_of_comp_eq_of_isLocalDiffeomorph
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace 𝕜 E₀]
    {H₀ : Type*} [TopologicalSpace H₀]
    {I₀ : ModelWithCorners 𝕜 E₀ H₀}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H₀ M]
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    {H₁ : Type*} [TopologicalSpace H₁]
    {I₁ : ModelWithCorners 𝕜 E₁ H₁}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₁ N]
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    {I₂ : ModelWithCorners 𝕜 E₂ H₂}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H₂ P]
    {f : M → N} {g : N → P} {h : M → P}
    (hf : Continuous f) (hg : IsLocalDiffeomorph I₁ I₂ ∞ g)
    (hh : ContMDiff I₀ I₂ ∞ h) (hcomp : g ∘ f = h) :
    ContMDiff I₀ I₁ ∞ f := by
  -- Near each point, `f` is the local inverse branch of `g` applied to the smooth map `h`.
  intro x
  let hgx := hg (f x)
  have hcompx : g (f x) = h x := by
    simpa [Function.comp_apply] using congr_fun hcomp x
  have houter : ContMDiffAt I₂ I₁ ∞ hgx.localInverse (h x) := by
    simpa [hcompx] using hgx.localInverse_contMDiffAt
  have hlocal : hgx.localInverse ∘ h =ᶠ[nhds x] f := by
    have hleft : (hgx.localInverse ∘ g) ∘ f =ᶠ[nhds x] id ∘ f :=
      hgx.localInverse_eventuallyEq_left.comp_tendsto hf.continuousAt
    simpa [Function.comp_apply, Function.comp_assoc, hcomp] using hleft
  -- Near each point, `f` is the local inverse branch of `g` applied to the smooth map `h`.
  exact (houter.comp x (hh x)).congr_of_eventuallyEq hlocal.symm

-- Lee's theorem is stated for real Lie groups, so the public uniqueness theorem is
-- specialized to `ℝ`, matching the surrounding section precedent.
/-- Theorem 7.9 (Uniqueness of the Universal Covering Group). For a connected real Lie group `G`,
if `π : Gtilde → G` and `π' : Gtilde' → G` are universal smooth covering maps that are Lie group
homomorphisms, then there exists a Lie group isomorphism `Φ : Gtilde → Gtilde'` such that
`π' ∘ Φ = π`. -/
theorem exists_lieGroupIsomorphism_of_universal_covering_group
    {EReal : Type uE} [NormedAddCommGroup EReal] [NormedSpace ℝ EReal]
    {HReal : Type uH} [TopologicalSpace HReal]
    {IReal : ModelWithCorners ℝ EReal HReal}
    {GReal : Type uG} [Group GReal] [TopologicalSpace GReal] [ChartedSpace HReal GReal]
    [LieGroup IReal ∞ GReal] [ConnectedSpace GReal]
    {EtildeReal : Type uEtilde} [NormedAddCommGroup EtildeReal] [NormedSpace ℝ EtildeReal]
    {HtildeReal : Type uHtilde} [TopologicalSpace HtildeReal]
    {ItildeReal : ModelWithCorners ℝ EtildeReal HtildeReal}
    {GtildeReal : Type uGtilde} [Group GtildeReal] [TopologicalSpace GtildeReal]
    [ChartedSpace HtildeReal GtildeReal] [LieGroup ItildeReal ∞ GtildeReal]
    {EtildeReal' : Type uEtilde'} [NormedAddCommGroup EtildeReal'] [NormedSpace ℝ EtildeReal']
    {HtildeReal' : Type uHtilde'} [TopologicalSpace HtildeReal']
    {ItildeReal' : ModelWithCorners ℝ EtildeReal' HtildeReal'}
    {GtildeReal' : Type uGtilde'} [Group GtildeReal'] [TopologicalSpace GtildeReal']
    [ChartedSpace HtildeReal' GtildeReal'] [LieGroup ItildeReal' ∞ GtildeReal']
    (π : ContMDiffMonoidMorphism ItildeReal IReal ∞ GtildeReal GReal)
    (hπ : Manifold.IsUniversalSmoothCoveringMap ItildeReal IReal π)
    (π' : ContMDiffMonoidMorphism ItildeReal' IReal ∞ GtildeReal' GReal)
    (hπ' : Manifold.IsUniversalSmoothCoveringMap ItildeReal' IReal π') :
    ∃ Φ : LieGroupIsomorphism ItildeReal ItildeReal' GtildeReal GtildeReal',
      π'.comp Φ.toContMDiffMonoidMorphism = π := by
  let _ : LocPathConnectedSpace GtildeReal := chartedSpaceLocPathConnectedSpace (J := ItildeReal)
  let _ : LocPathConnectedSpace GtildeReal' := chartedSpaceLocPathConnectedSpace (J := ItildeReal')
  let _ : SimplyConnectedSpace GtildeReal := hπ.simplyConnectedSpace
  let _ : SimplyConnectedSpace GtildeReal' := hπ'.simplyConnectedSpace
  let _ : PathConnectedSpace GtildeReal := inferInstance
  let _ : PathConnectedSpace GtildeReal' := inferInstance
  let _ : IsTopologicalGroup GtildeReal := topologicalGroup_of_lieGroup ItildeReal ∞
  let _ : IsTopologicalGroup GtildeReal' := topologicalGroup_of_lieGroup ItildeReal' ∞
  -- Build the normalized comparison lift in each direction between the two covers.
  obtain ⟨F, hF_one, hF_comp⟩ := existsComparisonContinuousLift
    (G := GReal) (π₁ := π) hπ (π₂ := π') hπ'
  obtain ⟨F', hF'_one, hF'_comp⟩ := existsComparisonContinuousLift
    (G := GReal) (π₁ := π') hπ' (π₂ := π) hπ
  have hF'F_comp : π ∘ F'.comp F = π := by
    ext x
    -- Both composites project to `π x` on the base.
    calc
      π (F' (F x)) = π' (F x) := by
        simpa using congrFun hF'_comp (F x)
      _ = π x := by
        simpa using congrFun hF_comp x
  have hFF'_comp : π' ∘ F.comp F' = π' := by
    ext x
    -- The symmetric comparison shows the other composite also fixes the base projection.
    calc
      π' (F (F' x)) = π (F' x) := by
        simpa using congrFun hF_comp (F' x)
      _ = π' x := by
        simpa using congrFun hF'_comp x
  have hF'F_cont : Continuous ((F' : GtildeReal' → GtildeReal) ∘ F) := by
    exact F'.continuous.comp F.continuous
  have hFF'_cont : Continuous ((F : GtildeReal → GtildeReal') ∘ F') := by
    exact F.continuous.comp F'.continuous
  have hF'F_eq : (F' : GtildeReal' → GtildeReal) ∘ F = id := by
    -- Covering uniqueness forces the left composite to be the identity on `GtildeReal`.
    refine liftEqOfCompEqAtPoint hπ.isSmoothCoveringMap hF'F_cont continuous_id ?_ 1 ?_
    · simpa [ContinuousMap.comp_apply, Function.comp_assoc] using hF'F_comp
    · simp [Function.comp_apply, hF_one, hF'_one]
  have hFF'_eq : (F : GtildeReal → GtildeReal') ∘ F' = id := by
    -- The same argument works in the opposite direction.
    refine liftEqOfCompEqAtPoint hπ'.isSmoothCoveringMap hFF'_cont continuous_id ?_ 1 ?_
    · simpa [ContinuousMap.comp_apply, Function.comp_assoc] using hFF'_comp
    · simp [Function.comp_apply, hF_one, hF'_one]
  have hF_smooth : ContMDiff ItildeReal ItildeReal' ∞ F := by
    -- Smoothness of the lift is detected after composing with the smooth covering `π'`.
    refine contMDiff_of_comp_eq_of_isLocalDiffeomorph F.continuous
      hπ'.isSmoothCoveringMap.isLocalDiffeomorph π.contMDiff_toFun ?_
    simpa using hF_comp
  have hF'_smooth : ContMDiff ItildeReal' ItildeReal ∞ F' := by
    -- The reverse comparison lift is smooth for the same reason.
    refine contMDiff_of_comp_eq_of_isLocalDiffeomorph F'.continuous
      hπ.isSmoothCoveringMap.isLocalDiffeomorph π'.contMDiff_toFun ?_
    simpa using hF'_comp
  have hF_mul : ∀ x y : GtildeReal, F (x * y) = F x * F y := by
    let leftLift : GtildeReal × GtildeReal → GtildeReal' := fun p ↦ F (p.1 * p.2)
    let rightLift : GtildeReal × GtildeReal → GtildeReal' := fun p ↦ F p.1 * F p.2
    have hleftLift : Continuous leftLift := by
      -- The first comparison map follows multiplication in the source cover and then applies `F`.
      simpa [leftLift] using F.continuous.comp continuous_mul
    have hrightLift : Continuous rightLift := by
      -- The second comparison map multiplies the two lifted coordinates in the target cover.
      simpa [rightLift] using
        (F.continuous.comp continuous_fst).mul (F.continuous.comp continuous_snd)
    have hcomp :
        π' ∘ leftLift = π' ∘ rightLift := by
      funext p
      rcases p with ⟨x, y⟩
      -- Both product lifts project to `π x * π y` on the base.
      calc
        π' (F (x * y)) = π (x * y) := by
          simpa using congrFun hF_comp (x * y)
        _ = π x * π y := by
          simp
        _ = π' (F x) * π' (F y) := by
          simpa [Function.comp_apply] using
            congrArg₂ (fun a b ↦ a * b) (congrFun hF_comp x).symm (congrFun hF_comp y).symm
        _ = π' (F x * F y) := by
          simp
    have hmul_eq : leftLift = rightLift := by
      -- Covering uniqueness on the connected product domain identifies the two candidate lifts.
      refine liftEqOfCompEqAtPoint hπ'.isSmoothCoveringMap hleftLift hrightLift hcomp (1, 1) ?_
      simp [leftLift, rightLift, hF_one]
    intro x y
    exact congrFun hmul_eq (x, y)
  let Φ : Diffeomorph ItildeReal ItildeReal' GtildeReal GtildeReal' ∞ :=
    { toFun := F
      invFun := F'
      left_inv := by
        intro x
        exact congrFun hF'F_eq x
      right_inv := by
        intro x
        exact congrFun hFF'_eq x
      contMDiff_toFun := hF_smooth
      contMDiff_invFun := hF'_smooth }
  refine ⟨{ toDiffeomorph := Φ, map_mul' := hF_mul }, ?_⟩
  -- Package the pointwise comparison equation as an equality of smooth group homomorphisms.
  apply DFunLike.ext
  intro x
  simpa [Φ] using congrFun hF_comp x

end UniversalCoveringGroup
