import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_30.Theorem_5_12
import SmoothManifolds_Lee_2012.Chap05.Sec05_31.Definition_5_31_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Theorem_5_53
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Definition_7_46_extra_3
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Definition_7_49_extra_1
import SmoothManifolds_Lee_2012.Chap07.Sec07_49.Proposition_7_11
import SmoothManifolds_Lee_2012.Chap07.Sec07_50.Definition_7_50_extra_4

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open scoped ContDiff Manifold

universe u𝕜 uEG uHG uG uEM uHM uM

-- Domain sampling pass:
-- * primary domain: smooth Lie group actions, orbit maps, stabilizers, and immersed submanifolds;
-- * sampled owner declarations: `orbit_map` / `orbitMap_contMDiff` in §7.50,
--   `MulActionHom.hasConstantRank` in Theorem 7.25, and `LieSubgroup` together with
--   `LieSubgroup.toImmersedSubmanifold` in §7.49;
-- * owner abstraction used here: the canonical action-derived map `orbit_map G p`, the canonical
--   subgroup `MulAction.stabilizer G p`, and the chapter owner `LieSubgroup I` for Lie-subgroup
--   structure;
-- * source/core/bridge triage: this proposition stays source-facing; parts (2) and (5) reuse the
--   core constant-rank/immersion owners from Theorem 7.25, and part (6) exposes the orbit itself
--   through a source-facing carrier/existence theorem while keeping the canonical bridge
--   `IsImmersion.toImmersedSubmanifold` as its construction helper;
-- * primitive data: the point `p : M` and the ambient smooth action;
-- * derived API: constant-rank, proper-embedding, Lie-subgroup, injectivity, immersion, and
--   immersed-submanifold consequences for that canonical orbit/stabilizer data.

section OrbitMapProperties

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners 𝕜 EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {J : ModelWithCorners 𝕜 EM HM} [IsManifold J ∞ M]
variable [MulAction G M] [ContMDiffSMul I J ∞ G M]

/-- Proposition 7.26 (1): for each `p ∈ M`, the orbit map `g ↦ g • p` is smooth. -/
theorem orbitMap_smooth (p : M) :
    ContMDiff I J ∞ (orbit_map G p) :=
  orbitMap_contMDiff p

/-- Helper for Proposition 7.26: the orbit map intertwines left translation on `G` with the given
action on `M`. -/
lemma orbitMap_map_smul (p : M) (g x : G) :
    orbit_map G p (g • x) = g • orbit_map G p x := by
  -- Expand the orbit map and use associativity of the action.
  simp [orbit_map, smul_smul]

/-- Helper for Proposition 7.26: the orbit map at `p` packaged as the canonical equivariant map
from `G` with its left-regular action to `M`. -/
def orbitMapMulActionHom (p : M) : G →[G] M where
  toFun := orbit_map G p
  map_smul' := orbitMap_map_smul p

/-- Proposition 7.26 (2): for each `p ∈ M`, the orbit map `g ↦ g • p` has constant rank. This
uses the chapter-local equivariant rank theorem, whose target manifold is finite dimensional. -/
theorem orbitMap_hasConstantRank [FiniteDimensional 𝕜 EM] (p : M) :
    ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r := by
  -- Fixed multiplication by `g` on the target manifold is a diffeomorphism with inverse
  -- multiplication by `g⁻¹`.
  let smulDiffeomorph :
      ∀ g : G, M ≃ₘ⟮J, J⟯ M :=
    fun g ↦
      { toEquiv := MulAction.toPerm g
        contMDiff_toFun := by
          -- Freeze the group variable in the smooth action map.
          simpa using
            ((contMDiff_const : ContMDiff J I ∞ fun _ : M ↦ g).smul
              (contMDiff_id : ContMDiff J J ∞ fun x : M ↦ x))
        contMDiff_invFun := by
          -- The inverse branch is fixed multiplication by `g⁻¹`.
          simpa using
            ((contMDiff_const : ContMDiff J I ∞ fun _ : M ↦ g⁻¹).smul
              (contMDiff_id : ContMDiff J J ∞ fun x : M ↦ x)) }
  have rankAt_comp_leftTranslation :
      ∀ {f : G → M}, ContMDiff I J ∞ f → ∀ g : G,
        rankAt I J (f ∘ leftTranslation (I := I) g) (1 : G) = rankAt I J f g := by
    intro f hf g
    -- Precomposing by a diffeomorphic left translation only moves the basepoint.
    let e :=
      (leftTranslationDiffeomorph (I := I) g).mfderivToContinuousLinearEquiv (by simp) (1 : G)
    have hLeftEq :
        leftTranslation (I := I) g = (leftTranslationDiffeomorph (I := I) g : G → G) := by
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
      exact LinearMap.range_eq_top.2 e.surjective
    have hComp :
        mfderiv I J (f ∘ leftTranslation (I := I) g) (1 : G) =
          (mfderiv I J f (leftTranslation (I := I) g (1 : G))).comp
            (mfderiv I I (leftTranslation (I := I) g) (1 : G)) :=
      mfderiv_comp
        (x := (1 : G))
        (g := f)
        (f := leftTranslation (I := I) g)
        (hf.mdifferentiableAt (by simp))
        (hLeftSmooth.mdifferentiableAt (by simp))
    have hRangeEq :
        (((mfderiv I J f (leftTranslation (I := I) g (1 : G))).toLinearMap.comp
          (mfderiv I I (leftTranslation (I := I) g) (1 : G)).toLinearMap).range) =
          (mfderiv I J f (leftTranslation (I := I) g (1 : G))).range := by
      simpa using LinearMap.range_comp_of_range_eq_top
        (mfderiv I J f (leftTranslation (I := I) g (1 : G))).toLinearMap
        (show (mfderiv I I (leftTranslation (I := I) g) (1 : G)).toLinearMap.range = ⊤ by
          simpa using hLeftRange)
    calc
      rankAt I J (f ∘ leftTranslation (I := I) g) (1 : G)
          = Module.finrank 𝕜
              ((mfderiv I J (f ∘ leftTranslation (I := I) g) (1 : G)).range) := by
              rw [rankAt_eq_finrank_range_mfderiv]
      _ = Module.finrank 𝕜
            (((mfderiv I J f (leftTranslation (I := I) g (1 : G))).comp
              (mfderiv I I (leftTranslation (I := I) g) (1 : G))).range) := by
            simpa using congrArg
              (fun f' : TangentSpace I (1 : G) →L[𝕜]
                TangentSpace J ((f ∘ leftTranslation (I := I) g) (1 : G)) =>
                Module.finrank 𝕜 f'.range)
              hComp
      _ = Module.finrank 𝕜 ((mfderiv I J f (leftTranslation (I := I) g (1 : G))).range) := by
            simpa using congrArg
              (fun q :
                Submodule 𝕜 (TangentSpace J (f (leftTranslation (I := I) g (1 : G)))) =>
                Module.finrank 𝕜 q)
              hRangeEq
      _ = rankAt I J f g := by
            rw [← rankAt_eq_finrank_range_mfderiv]
            simp
  have rankAt_smul_comp :
      ∀ {f : G → M}, ContMDiff I J ∞ f → ∀ g : G,
        rankAt I J ((fun y : M ↦ g • y) ∘ f) (1 : G) = rankAt I J f (1 : G) := by
    intro f hf g
    -- Postcomposing by the target fixed-smul diffeomorphism only changes the derivative by a
    -- linear equivalence on the range.
    let e := (smulDiffeomorph g).mfderivToContinuousLinearEquiv (by simp) (f (1 : G))
    have hSmulEq :
        (fun y : M ↦ g • y) = (smulDiffeomorph g : M → M) := by
      funext y
      rfl
    have hSmulSmooth : ContMDiff J J ∞ (fun y : M ↦ g • y) := by
      simpa using
        ((contMDiff_const : ContMDiff J I ∞ fun _ : M ↦ g).smul
          (contMDiff_id : ContMDiff J J ∞ fun y : M ↦ y))
    have hComp :
        mfderiv I J (((fun y : M ↦ g • y) ∘ f)) (1 : G) =
          (mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).comp (mfderiv I J f (1 : G)) :=
      mfderiv_comp
        (x := (1 : G))
        (g := fun y : M ↦ g • y)
        (f := f)
        (hSmulSmooth.mdifferentiableAt (by simp))
        (hf.mdifferentiableAt (by simp))
    have hRangeComp :
        (((mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).comp
          (mfderiv I J f (1 : G))).range) =
          ((mfderiv I J f (1 : G)).range).map
            (mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).toLinearMap := by
      simpa using LinearMap.range_comp
        (mfderiv I J f (1 : G)).toLinearMap
        (mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).toLinearMap
    have hDerivEq :
        mfderiv J J (fun y : M ↦ g • y) (f (1 : G)) =
          (e : TangentSpace J (f (1 : G)) →L[𝕜]
            TangentSpace J ((smulDiffeomorph g) (f (1 : G)))) := by
      rw [hSmulEq]
      rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
        (smulDiffeomorph g) (by simp) (x := f (1 : G))]
    have hDerivEqLinear :
        (mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).toLinearMap =
          (e : TangentSpace J (f (1 : G)) →L[𝕜]
            TangentSpace J ((smulDiffeomorph g) (f (1 : G)))).toLinearMap := by
      simpa using congrArg ContinuousLinearMap.toLinearMap hDerivEq
    calc
      rankAt I J ((fun y : M ↦ g • y) ∘ f) (1 : G)
          = Module.finrank 𝕜
              ((mfderiv I J ((fun y : M ↦ g • y) ∘ f) (1 : G)).range) := by
              rw [rankAt_eq_finrank_range_mfderiv]
      _ = Module.finrank 𝕜
            (((mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).comp
              (mfderiv I J f (1 : G))).range) := by
            simpa using congrArg
              (fun f' : TangentSpace I (1 : G) →L[𝕜]
                TangentSpace J (((fun y : M ↦ g • y) ∘ f) (1 : G)) =>
                Module.finrank 𝕜 f'.range)
              hComp
      _ = Module.finrank 𝕜
            (((mfderiv I J f (1 : G)).range).map
              (mfderiv J J (fun y : M ↦ g • y) (f (1 : G))).toLinearMap) := by
            simpa using congrArg
              (fun q : Submodule 𝕜 (TangentSpace J ((fun y : M ↦ g • y) (f (1 : G)))) =>
                Module.finrank 𝕜 q)
              hRangeComp
      _ = Module.finrank 𝕜
            (((mfderiv I J f (1 : G)).range).map
              ((e : TangentSpace J (f (1 : G)) →L[𝕜]
                TangentSpace J ((smulDiffeomorph g) (f (1 : G)))).toLinearMap)) := by
            simpa using congrArg
              (fun f' : TangentSpace J (f (1 : G)) →ₗ[𝕜]
                TangentSpace J ((smulDiffeomorph g) (f (1 : G))) =>
                Module.finrank 𝕜 (((mfderiv I J f (1 : G)).range).map f'))
              hDerivEqLinear
      _ = Module.finrank 𝕜 ((mfderiv I J f (1 : G)).range) := by
            simpa [e] using LinearEquiv.finrank_map_eq e.toLinearEquiv
              ((mfderiv I J f (1 : G)).range)
      _ = rankAt I J f (1 : G) := by
            rw [← rankAt_eq_finrank_range_mfderiv]
  refine ⟨rankAt I J (orbit_map G p) (1 : G), ?_⟩
  constructor
  · exact (orbitMap_smooth (G := G) (I := I) (J := J) p).mdifferentiable (by simp)
  · intro g
    have hComm :
        orbit_map G p ∘ leftTranslation (I := I) g =
          (fun y : M ↦ g • y) ∘ orbit_map G p := by
      -- Left translation on the source commutes with the action on the target.
      funext x
      simp [Function.comp, orbit_map, smul_smul]
    calc
      rankAt I J (orbit_map G p) g
          = rankAt I J (orbit_map G p ∘ leftTranslation (I := I) g) (1 : G) := by
              symm
              exact rankAt_comp_leftTranslation (orbitMap_smooth (G := G) (I := I) (J := J) p) g
      _ = rankAt I J (((fun y : M ↦ g • y) ∘ orbit_map G p)) (1 : G) := by
            rw [hComm]
      _ = rankAt I J (orbit_map G p) (1 : G) := by
            exact rankAt_smul_comp (orbitMap_smooth (G := G) (I := I) (J := J) p) g

/-- Helper for Proposition 7.26: once the orbit map has constant rank, its fiber over `p` is a
properly embedded subset of `G`, hence the stabilizer is properly embedded as well. -/
lemma stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M)
    (hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  rcases hOrbitRank with ⟨r, hRank⟩
  -- The stabilizer is exactly the fiber of the orbit map over `p`.
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    constant_rank_level_set_isProperlyEmbedded (orbitMap_smooth (G := G) (I := I) (J := J) p)
      hRank p

/-- Helper for Proposition 7.26: the current section already contains the constant-rank witness
for the orbit map, so the proper-embedding conclusion can consume it without asking later theorem
bodies to reconstruct the ambient action-model data. -/
lemma stabilizerProperlyEmbedded_fromCurrentSection
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  -- Consume the orbit-map constant-rank witness while the full section context is still visible.
  exact stabilizerIsProperlyEmbedded_of_orbitMapHasConstantRank
    (G := G) (I := I) (J := J) p (orbitMap_hasConstantRank (G := G) (I := I) (J := J) p)

/-- Proposition 7.26 (3): for each `p ∈ M`, the isotropy group `MulAction.stabilizer G p` is a
properly embedded subset of `G`. -/
theorem stabilizer_isProperlyEmbedded
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] [T1Space M] (p : M) :
    ((MulAction.stabilizer G p : Set G)).IsProperlyEmbedded := by
  -- Reuse the current-section wrapper so the theorem body stays source-facing.
  exact stabilizerProperlyEmbedded_fromCurrentSection
    (G := G) (I := I) (J := J) p

/-- Helper for Proposition 7.26: the constant-rank level-set theorem equips the stabilizer subset
with the embedded-submanifold structure needed by Proposition 7.11. -/
lemma stabilizer_has_embeddedSubmanifold_data (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
    (hOrbitRank : ∃ r : ℕ, Manifold.HasConstantRank I J (orbit_map G p) r) :
    ∃ r : ℕ,
      let k : ℕ := Module.finrank 𝕜 EG - r
      let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
        ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
          let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
              ((MulAction.stabilizer G p : Set G)) := cs
          let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
            hEmb.codimension = r := by
  rcases hOrbitRank with ⟨r, hRank⟩
  refine ⟨r, ?_⟩
  -- Reinterpret the orbit-map fiber over `p` as the stabilizer subset once, then reuse the
  -- level-set owner directly.
  simpa [preimage_singleton_orbit_map_eq_stabilizer] using
    (constant_rank_level_set_has_embedded_submanifold_structure
      (orbitMap_smooth (G := G) (I := I) (J := J) p) hRank p)

/-- Helper for Proposition 7.26: the current section already contains the constant-rank witness
for the orbit map, so the stabilizer's embedded-submanifold package can be produced without
passing that witness through later theorem boundaries. -/
lemma stabilizerEmbeddedData_fromCurrentSection (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    ∃ r : ℕ,
      let k : ℕ := Module.finrank 𝕜 EG - r
      let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ∃ cs : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)),
        ∃ hs : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)),
          let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k))
              ((MulAction.stabilizer G p : Set G)) := cs
          let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
          ∃ hEmb : IsEmbeddedSubmanifold I K ((MulAction.stabilizer G p : Set G)),
            hEmb.codimension = r := by
  -- Consume the orbit-map constant-rank witness while the section still fixes all instances.
  exact stabilizer_has_embeddedSubmanifold_data
    (G := G) (I := I) (J := J) p (orbitMap_hasConstantRank (G := G) (I := I) (J := J) p)

/-- Proposition 7.26 (4): for each `p ∈ M`, the isotropy group `MulAction.stabilizer G p` carries
a Lie-subgroup structure compatible with the ambient Lie group `G`. This uses the constant-rank
level-set theorem and the chapter's embedded-subgroup-to-Lie-group bridge, so the ambient Lie
group and target manifold are assumed finite dimensional. -/
theorem stabilizer_has_lieSubgroup_structure (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM] :
    ∃ S : LieSubgroup I, S.carrier = MulAction.stabilizer G p := by
  rcases stabilizerEmbeddedData_fromCurrentSection (G := G) (I := I) (J := J) p with
    ⟨r, cs, hs, hEmb, hcodim⟩
  -- Install the embedded-submanifold package produced by the level-set theorem.
  let k : ℕ := Module.finrank 𝕜 EG - r
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)) := cs
  let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
  -- Proposition 7.11 upgrades the embedded subgroup to a Lie subgroup.
  simpa using subgroup_has_lieSubgroup_structure_of_isEmbeddedSubmanifold
    (𝕜 := 𝕜) (I := I) (E' := EuclideanSpace 𝕜 (Fin k))
    (S := MulAction.stabilizer G p) hEmb

/-- Helper for Proposition 7.26: if the isotropy group at `p` is trivial, then the orbit map
`g ↦ g • p` is injective. -/
theorem orbitMap_injective_of_stabilizer_eq_bot (p : M)
    (hp : MulAction.stabilizer G p = ⊥) :
    Function.Injective (orbit_map G p) := by
  intro g₁ g₂ hEq
  have hMem : g₂⁻¹ * g₁ ∈ MulAction.stabilizer G p := by
    -- Equality of orbit-map values makes `g₂⁻¹ * g₁` fix `p`.
    rw [MulAction.mem_stabilizer_iff]
    calc
      (g₂⁻¹ * g₁) • p = g₂⁻¹ • (g₁ • p) := by simp [smul_smul]
      _ = g₂⁻¹ • (g₂ • p) := by
        simpa [orbit_map] using congrArg (fun x : M ↦ g₂⁻¹ • x) hEq
      _ = p := by simp
  have hOne : g₂⁻¹ * g₁ = 1 := by
    have hBot : g₂⁻¹ * g₁ ∈ (⊥ : Subgroup G) := by
      simpa [hp] using hMem
    simpa using hBot
  -- Multiply by `g₂` on the left to recover equality in the ambient group.
  simpa [mul_assoc] using congrArg (fun x : G ↦ g₂ * x) hOne

/-- Helper for Proposition 7.26: a singleton cannot be an open subset of
`EuclideanSpace 𝕜 (Fin k)` when `k ≠ 0`. -/
lemma euclideanSpace_fin_not_isOpen_singleton {k : ℕ}
    (hk : k ≠ 0) (x : EuclideanSpace 𝕜 (Fin k)) :
    ¬ IsOpen ({x} : Set (EuclideanSpace 𝕜 (Fin k))) := by
  intro hx
  rw [Metric.isOpen_singleton_iff] at hx
  rcases hx with ⟨ε, hεpos, hball⟩
  have hkpos : 0 < k := Nat.pos_iff_ne_zero.mpr hk
  let i : Fin k := ⟨0, hkpos⟩
  let v : EuclideanSpace 𝕜 (Fin k) := fun j ↦ if j = i then 1 else 0
  have hv : v ≠ 0 := by
    intro hv0
    have hvi : v i = 0 := by simpa [hv0]
    exact one_ne_zero <| by simpa [v] using hvi
  have hvnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  obtain ⟨c, hcpos, hcsmall⟩ :
      ∃ c : 𝕜, 0 < ‖c‖ ∧ ‖c‖ < ε / ‖v‖ :=
    NormedField.exists_norm_lt 𝕜 (div_pos hεpos hvnormpos)
  let y : EuclideanSpace 𝕜 (Fin k) := x + c • v
  have hyBall : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, dist_eq_norm, y, add_sub_cancel_left]
    have hmul :
        ‖c‖ * ‖v‖ < ε := by
      have := mul_lt_mul_of_pos_right hcsmall hvnormpos
      simpa [div_eq_mul_inv, hvnormpos.ne'] using this
    simpa [norm_smul] using hmul
  have hyEq : y = x := hball hyBall
  have hcv : c • v = 0 := by
    simpa [y] using add_right_cancel hyEq
  exact hcpos.ne' <| by
    rw [norm_eq_zero] at hcpos
    exact smul_eq_zero.mp hcv |>.resolve_right hv

/-- Helper for Proposition 7.26: a nonempty subsingleton charted on
`EuclideanSpace 𝕜 (Fin k)` must have `k = 0`. -/
lemma subsingletonChartedSpace_fin_eq_zero {k : ℕ} {S : Type*}
    [TopologicalSpace S] [ChartedSpace (EuclideanSpace 𝕜 (Fin k)) S]
    [Nonempty S] [Subsingleton S] :
    k = 0 := by
  classical
  obtain ⟨x⟩ := ‹Nonempty S›
  let e := chartAt (EuclideanSpace 𝕜 (Fin k)) x
  have htargetSubsingleton : Set.Subsingleton e.target := by
    let h := e.toHomeomorphSourceTarget.toEquiv
    let _ : Subsingleton e.source := inferInstance
    exact h.subsingleton
  have htargetEq : e.target = {e x} :=
    htargetSubsingleton.eq_singleton_of_mem (mem_chart_target (EuclideanSpace 𝕜 (Fin k)) x)
  by_contra hk
  -- The chart target is a nonempty open singleton, which is impossible in positive dimension.
  exact euclideanSpace_fin_not_isOpen_singleton (𝕜 := 𝕜) hk (e x) <|
    by simpa [htargetEq] using e.open_target

/-- Helper for Proposition 7.26: trivial isotropy forces the orbit map to have full manifold rank
at every point. -/
lemma orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, rankAt I J (orbit_map G p) g = Module.finrank 𝕜 EG := by
  rcases orbitMap_hasConstantRank (G := G) (I := I) (J := J) p with ⟨r, hRank⟩
  rcases stabilizer_has_embeddedSubmanifold_data
      (G := G) (I := I) (J := J) p ⟨r, hRank⟩ with
    ⟨r', cs, hs, hEmb, hcodim⟩
  have hrEq : r' = r := by
    simpa using hcodim
  subst hrEq
  let k : ℕ := Module.finrank 𝕜 EG - r
  let K := modelWithCornersSelf 𝕜 (EuclideanSpace 𝕜 (Fin k))
  let _ : ChartedSpace (EuclideanSpace 𝕜 (Fin k)) ((MulAction.stabilizer G p : Set G)) := cs
  let _ : IsManifold K ∞ ((MulAction.stabilizer G p : Set G)) := hs
  have hStabNonempty : Nonempty ((MulAction.stabilizer G p : Set G)) := by
    refine ⟨⟨1, ?_⟩⟩
    simpa [hp]
  have hStabSubsingleton : Subsingleton ((MulAction.stabilizer G p : Set G)) := by
    rw [hp]
    infer_instance
  have hkZero : k = 0 := by
    -- Under `hp`, the stabilizer fiber is a singleton, so its chart dimension must vanish.
    exact subsingletonChartedSpace_fin_eq_zero (𝕜 := 𝕜)
      (S := ((MulAction.stabilizer G p : Set G)))
  have hSourceLe : r ≤ Module.finrank 𝕜 EG := by
    have hRangeLe :
        Module.finrank 𝕜 ((mfderiv I J (orbit_map G p) (1 : G)).range) ≤
          Module.finrank 𝕜 (TangentSpace I (1 : G)) :=
      (mfderiv I J (orbit_map G p) (1 : G)).range.finrank_le
    have hRankOne : rankAt I J (orbit_map G p) (1 : G) = r := hRank.2 (1 : G)
    rw [rankAt_eq_finrank_range_mfderiv] at hRankOne
    simpa [hRankOne] using hRangeLe
  have hSourceGe : Module.finrank 𝕜 EG ≤ r := by
    exact Nat.sub_eq_zero_iff_le.mp (by simpa [k] using hkZero)
  have hrFull : r = Module.finrank 𝕜 EG := le_antisymm hSourceLe hSourceGe
  intro g
  -- Constant rank now identifies every pointwise rank with the full source dimension.
  simpa [hrFull] using hRank.2 g

/-- Helper for Proposition 7.26: trivial isotropy makes every manifold derivative of the orbit map
injective, so the immersion criterion can close pointwise. -/
lemma orbitMapMfderiv_injective_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
    (hp : MulAction.stabilizer G p = ⊥) :
    ∀ g : G, Function.Injective (mfderiv I J (orbit_map G p) g) := by
  intro g
  let L := (mfderiv I J (orbit_map G p) g).toLinearMap
  letI : FiniteDimensional 𝕜 (TangentSpace I g) := by
    change FiniteDimensional 𝕜 EG
    infer_instance
  have hRangeFull :
      Module.finrank 𝕜 L.range = Module.finrank 𝕜 (TangentSpace I g) := by
    rw [← rankAt_eq_finrank_range_mfderiv]
    simpa using orbitMapRank_eq_sourceFinrank_of_stabilizer_eq_bot
      (G := G) (I := I) (J := J) p hp g
  have hKerZero : Module.finrank 𝕜 L.ker = 0 := by
    have hNullity := L.finrank_range_add_finrank_ker
    rw [hRangeFull] at hNullity
    exact add_left_cancel hNullity
  have hKerBot : L.ker = ⊥ := Submodule.finrank_eq_zero.mp hKerZero
  exact LinearMap.ker_eq_bot.1 hKerBot

/-- Proposition 7.26 (5): if the isotropy group at `p` is trivial, then the orbit map `g ↦ g • p`
is a smooth immersion. This is the source-facing immersion statement for the given Lie-group model
`I` on `G`; part (6) reuses it directly by instantiating `I` with the boundaryless self-model on
`G`. -/
theorem orbitMap_isImmersion_of_stabilizer_eq_bot (p : M)
    [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
    [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
    (hp : MulAction.stabilizer G p = ⊥) :
    IsImmersion I J (⊤ : WithTop ℕ∞) (orbit_map G p) := by
  -- Route correction: avoid the missing Theorem 7.25 owner by proving pointwise derivative
  -- injectivity directly from the constant-rank level-set package for the trivial stabilizer.
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv
    (orbitMap_smooth (G := G) (I := I) (J := J) p)).2 ?_
  intro g
  exact orbitMapMfderiv_injective_of_stabilizer_eq_bot
    (G := G) (I := I) (J := J) p hp g

section OrbitImmersedSubmanifold

variable [FiniteDimensional 𝕜 EG] [FiniteDimensional 𝕜 EM]
variable [T2Space G] [SecondCountableTopology G] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace EG G]
variable [IsManifold (modelWithCornersSelf 𝕜 EG) (⊤ : WithTop ℕ∞) G]
variable [LieGroup (modelWithCornersSelf 𝕜 EG) (⊤ : WithTop ℕ∞) G]
variable [ContMDiffSMul (modelWithCornersSelf 𝕜 EG) J (⊤ : WithTop ℕ∞) G M]

/-- Bridge for Proposition 7.26: under trivial isotropy, the injective orbit map for the
boundaryless self-model on `G` canonically determines an immersed submanifold of `M`. The
source-facing orbit statement is recorded below via the carrier and existence theorems. -/
noncomputable def orbitImmersedSubmanifold_of_stabilizer_eq_bot
    (p : M) (hp : MulAction.stabilizer G p = ⊥) :
    ImmersedSubmanifold J M :=
  let hImm :
      IsImmersion (modelWithCornersSelf 𝕜 EG) J (⊤ : WithTop ℕ∞) (orbit_map G p) :=
    orbitMap_isImmersion_of_stabilizer_eq_bot p hp
  hImm.toImmersedSubmanifold (orbitMap_injective_of_stabilizer_eq_bot p hp)

/-- Proposition 7.26 (6): if the isotropy group at `p` is trivial, then the orbit `G • p` is an
immersed submanifold of `M`. -/
theorem orbit_is_immersed_submanifold_of_stabilizer_eq_bot
    (p : M) (hp : MulAction.stabilizer G p = ⊥) :
    ∃ S : ImmersedSubmanifold J M,
      S.carrier = MulAction.orbit G p := by
  refine ⟨orbitImmersedSubmanifold_of_stabilizer_eq_bot (𝕜 := 𝕜) (J := J) p hp, ?_⟩
  -- The constructed immersed submanifold uses the orbit map itself, whose range is the orbit.
  simpa [orbitImmersedSubmanifold_of_stabilizer_eq_bot, range_orbit_map]

end OrbitImmersedSubmanifold

end OrbitMapProperties
