import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_6
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Definition_7_46_extra_3
import SmoothManifolds_Lee_2012.Chap07.Sec07_47.Definition_7_47_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff
open Manifold

universe u𝕜 uEG uHG uG uEH uHH uH

-- `lean_leansearch` is unavailable in this environment; the statement shape was checked against
-- the local `Manifold.HasConstantRank` owner from `Exercise_4_4` and the section's
-- `ContMDiffMonoidMorphism` usage.

section LieGroupHomomorphisms

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable [FiniteDimensional 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable [LieGroup I ∞ G] [LieGroup J ∞ H]

namespace ContMDiffMonoidMorphism

omit [FiniteDimensional 𝕜 EH] in
/-- Helper for Theorem 7.5: a smooth Lie group homomorphism intertwines left translations. -/
lemma comp_leftTranslation_eq_leftTranslation_comp
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    F ∘ leftTranslation (I := I) g = leftTranslation (I := J) (F g) ∘ F := by
  -- Left multiplication commutes with a group homomorphism.
  funext x
  simp [Function.comp, map_mul]

omit [FiniteDimensional 𝕜 EH] in
/-- Helper for Theorem 7.5: precomposing a Lie-group homomorphism with a source left translation
does not change the rank measured at the identity. -/
lemma rankAt_comp_leftTranslation
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    rankAt I J (F ∘ leftTranslation (I := I) g) (1 : G) = rankAt I J F g := by
  -- Rewrite the source translation as a diffeomorphism so its derivative is a linear equivalence.
  let e :=
    (leftTranslationDiffeomorph (I := I) g).mfderivToContinuousLinearEquiv (by simp) (1 : G)
  have hLeftEq : leftTranslation (I := I) g = (leftTranslationDiffeomorph (I := I) g : G → G) := by
    funext x
    simp [leftTranslationDiffeomorph_apply]
  have hLeftSmooth : ContMDiff I I ∞ (leftTranslation (I := I) g) := by
    simpa [hLeftEq] using (leftTranslationDiffeomorph (I := I) g).contMDiff_toFun
  have hLeftRange :
      (mfderiv I I (leftTranslation (I := I) g) (1 : G)).range = ⊤ := by
    -- The derivative is the forward map of the left-translation diffeomorphism.
    rw [hLeftEq]
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (leftTranslationDiffeomorph (I := I) g) (by simp) (x := (1 : G))]
    have hRangeTop :
        (e :
          TangentSpace I (1 : G) →L[𝕜]
            TangentSpace I
              ((leftTranslationDiffeomorph (I := I) g) (1 : G))).range = ⊤ :=
      LinearMap.range_eq_top.2 e.surjective
    exact hRangeTop
  have hComp :
      mfderiv I J (F ∘ leftTranslation (I := I) g) (1 : G) =
        (mfderiv I J F (leftTranslation (I := I) g (1 : G))).comp
          (mfderiv I I (leftTranslation (I := I) g) (1 : G)) :=
    mfderiv_comp_of_smooth hLeftSmooth F.contMDiff_toFun
  have hRangeEq :
      (((mfderiv I J F (leftTranslation (I := I) g (1 : G))).toLinearMap.comp
        (mfderiv I I (leftTranslation (I := I) g) (1 : G)).toLinearMap).range) =
        (mfderiv I J F (leftTranslation (I := I) g (1 : G))).range := by
    simpa using LinearMap.range_comp_of_range_eq_top
      (mfderiv I J F (leftTranslation (I := I) g (1 : G))).toLinearMap
      (show (mfderiv I I (leftTranslation (I := I) g) (1 : G)).toLinearMap.range = ⊤ by
        simpa using hLeftRange)
  -- The chain rule expresses the derivative of the composite as postcomposition by this
  -- invertible derivative, and full range eliminates that extra factor from the rank.
  calc
    rankAt I J (F ∘ leftTranslation (I := I) g) (1 : G)
        = Module.finrank 𝕜 ((mfderiv I J (F ∘ leftTranslation (I := I) g) (1 : G)).range) := by
            rw [rankAt_eq_finrank_range_mfderiv]
    _ = Module.finrank 𝕜
          (((mfderiv I J F (leftTranslation (I := I) g (1 : G))).comp
            (mfderiv I I (leftTranslation (I := I) g) (1 : G))).range) := by
          simpa using congrArg
            (fun f : TangentSpace I (1 : G) →L[𝕜]
              TangentSpace J ((F ∘ leftTranslation (I := I) g) (1 : G)) =>
              Module.finrank 𝕜 f.range)
            hComp
    _ = Module.finrank 𝕜 ((mfderiv I J F (leftTranslation (I := I) g (1 : G))).range) := by
          simpa using congrArg
            (fun p : Submodule 𝕜 (TangentSpace J (F (leftTranslation (I := I) g (1 : G)))) =>
              Module.finrank 𝕜 p)
            hRangeEq
    _ = rankAt I J F g := by
          rw [← rankAt_eq_finrank_range_mfderiv]
          simp

omit [FiniteDimensional 𝕜 EH] in
/-- Helper for Theorem 7.5: postcomposing a Lie-group homomorphism with a target left
translation does not change the rank measured at the identity. -/
lemma rankAt_leftTranslation_comp
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    rankAt I J (leftTranslation (I := J) (F g) ∘ F) (1 : G) = rankAt I J F (1 : G) := by
  -- Rewrite the target translation as a diffeomorphism so its derivative acts by a linear
  -- equivalence on the derivative range of `F`.
  let e :=
    (leftTranslationDiffeomorph (I := J) (F g)).mfderivToContinuousLinearEquiv (by simp) (F (1 : G))
  have hLeftEq :
      leftTranslation (I := J) (F g) = (leftTranslationDiffeomorph (I := J) (F g) : H → H) := by
    funext x
    simp [leftTranslationDiffeomorph_apply]
  have hLeftSmooth : ContMDiff J J ∞ (leftTranslation (I := J) (F g)) := by
    simpa [hLeftEq] using (leftTranslationDiffeomorph (I := J) (F g)).contMDiff_toFun
  have hComp :
      mfderiv I J (leftTranslation (I := J) (F g) ∘ F) (1 : G) =
        (mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).comp (mfderiv I J F (1 : G)) :=
    mfderiv_comp_of_smooth F.contMDiff_toFun hLeftSmooth
  have hRangeComp :
      (((mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).comp
        (mfderiv I J F (1 : G))).range) =
        ((mfderiv I J F (1 : G)).range).map
          (mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).toLinearMap := by
    simpa using LinearMap.range_comp
      (mfderiv I J F (1 : G)).toLinearMap
      (mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).toLinearMap
  have hDerivEq :
      mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G)) =
        (e : TangentSpace J (F (1 : G)) →L[𝕜]
          TangentSpace J ((leftTranslationDiffeomorph (I := J) (F g)) (F (1 : G)))) := by
    rw [hLeftEq]
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (leftTranslationDiffeomorph (I := J) (F g)) (by simp) (x := F (1 : G))]
  have hDerivEqLinear :
      (mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).toLinearMap =
        (e : TangentSpace J (F (1 : G)) →L[𝕜]
          TangentSpace J
            ((leftTranslationDiffeomorph (I := J) (F g)) (F (1 : G)))).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hDerivEq
  -- Route correction: keep the natural chain-rule basepoint `F 1` until the final rank rewrite.
  calc
    rankAt I J (leftTranslation (I := J) (F g) ∘ F) (1 : G)
        = Module.finrank 𝕜
            ((mfderiv I J (leftTranslation (I := J) (F g) ∘ F) (1 : G)).range) := by
            rw [rankAt_eq_finrank_range_mfderiv]
    _ = Module.finrank 𝕜
          (((mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).comp
            (mfderiv I J F (1 : G))).range) := by
          simpa using congrArg
            (fun f : TangentSpace I (1 : G) →L[𝕜]
              TangentSpace J ((leftTranslation (I := J) (F g) ∘ F) (1 : G)) =>
              Module.finrank 𝕜 f.range)
            hComp
    _ = Module.finrank 𝕜
          (((mfderiv I J F (1 : G)).range).map
            (mfderiv J J (leftTranslation (I := J) (F g)) (F (1 : G))).toLinearMap) := by
          simpa using congrArg
            (fun p : Submodule 𝕜 (TangentSpace J (leftTranslation (I := J) (F g) (F (1 : G)))) =>
              Module.finrank 𝕜 p)
            hRangeComp
    _ = Module.finrank 𝕜
          (((mfderiv I J F (1 : G)).range).map
            ((e :
              TangentSpace J (F (1 : G)) →L[𝕜]
                TangentSpace J
                  ((leftTranslationDiffeomorph (I := J) (F g)) (F (1 : G)))).toLinearMap)) := by
          simpa using congrArg
            (fun f : TangentSpace J (F (1 : G)) →ₗ[𝕜]
              TangentSpace J ((leftTranslationDiffeomorph (I := J) (F g)) (F (1 : G))) =>
              Module.finrank 𝕜 (((mfderiv I J F (1 : G)).range).map f))
            hDerivEqLinear
    _ = Module.finrank 𝕜 ((mfderiv I J F (1 : G)).range) := by
          simpa [e] using LinearEquiv.finrank_map_eq e.toLinearEquiv
            ((mfderiv I J F (1 : G)).range)
    _ = rankAt I J F (1 : G) := by
          rw [← rankAt_eq_finrank_range_mfderiv]

omit [FiniteDimensional 𝕜 EH] in
/-- Theorem 7.5: every Lie group homomorphism has constant rank, equivalently `rankAt I J F g`
agrees with `rankAt I J F 1` for every `g : G`. -/
theorem rankAt_eq_rankAt_one
    (F : ContMDiffMonoidMorphism I J ∞ G H) (g : G) :
    rankAt I J F g = rankAt I J F (1 : G) := by
  -- Route correction: compare ranks through left-translation compositions, not through a raw
  -- differentiated equality whose endpoints normalize in different spelling worlds.
  calc
    rankAt I J F g = rankAt I J (F ∘ leftTranslation (I := I) g) (1 : G) := by
      symm
      exact rankAt_comp_leftTranslation (F := F) g
    _ = rankAt I J (leftTranslation (I := J) (F g) ∘ F) (1 : G) := by
      rw [comp_leftTranslation_eq_leftTranslation_comp (F := F) (g := g)]
    _ = rankAt I J F (1 : G) := rankAt_leftTranslation_comp (F := F) g

omit [FiniteDimensional 𝕜 EH] in
/-- Companion theorem for Theorem 7.5: the pointwise rank identity packages into
`HasConstantRank I J F (rankAt I J F (1 : G))`. -/
theorem hasConstantRank
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    HasConstantRank I J F (rankAt I J F (1 : G)) := by
  -- Constant rank is exactly smoothness together with the pointwise rank formula.
  refine ⟨?_, ?_⟩
  · simpa using F.contMDiff_toFun.mdifferentiable (by simp)
  · intro g
    exact rankAt_eq_rankAt_one F g

end ContMDiffMonoidMorphism

end LieGroupHomomorphisms
