import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.SMul
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.GroupTheory.GroupAction.Transitive
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Exercise_4_4
import SmoothManifolds_Lee_2012.Chap04.Sec04_23.Theorem_4_14

-- Declarations for this item will be appended below by the statement pipeline.
-- `lean_leansearch` was unavailable in this environment; the statement shape was verified against
-- the local `Manifold.HasConstantRank` owner, the chapter-global constant-rank consequences in
-- `Theorem_4_14`, and the section's owner-level `MulActionHom` / `ContMDiffMonoidMorphism`
-- precedents for putting source-facing results in the canonical bundled-map namespace.

open scoped ContDiff Manifold
open Manifold

section EquivariantRankTheorem

universe u𝕜 uEG uHG uG uEM uHM uM uEN uHN uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners 𝕜 EG HG} [LieGroup I ∞ G]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IM : ModelWithCorners 𝕜 EM HM} [IsManifold IM ∞ M]
variable [MulAction G M] [ContMDiffSMul I IM ∞ G M]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN] [FiniteDimensional 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {IN : ModelWithCorners 𝕜 EN HN} [IsManifold IN ∞ N]
variable [MulAction G N] [ContMDiffSMul I IN ∞ G N]
variable [MulAction.IsPretransitive G M]

namespace MulActionHom

/-- Helper for the equivariant rank theorem: for a smooth `G`-action, fixing the group element `g`
gives a smooth self-map `x ↦ g • x`. -/
lemma contMDiff_const_smul
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type*} [TopologicalSpace HX]
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners 𝕜 EX HX} [IsManifold IX ∞ X]
    [MulAction G X] [ContMDiffSMul I IX ∞ G X] (g : G) :
    ContMDiff IX IX ∞ (fun x : X ↦ g • x) := by
  -- Freeze the group variable in the smooth action map.
  simpa using
    ((contMDiff_const : ContMDiff IX I ∞ fun _ : X ↦ g).smul
      (contMDiff_id : ContMDiff IX IX ∞ fun x : X ↦ x))

/-- Helper for the equivariant rank theorem: fixed multiplication by `g` is a diffeomorphism, with
inverse fixed multiplication by `g⁻¹`. -/
def smulDiffeomorph
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type*} [TopologicalSpace HX]
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners 𝕜 EX HX} [IsManifold IX ∞ X]
    [MulAction G X] [ContMDiffSMul I IX ∞ G X] (g : G) :
    X ≃ₘ⟮IX, IX⟯ X where
  toEquiv := MulAction.toPerm g
  contMDiff_toFun := by
    -- The forward branch is the smooth fixed-smul map.
    have hsmul : ContMDiff IX IX ∞ (fun x : X ↦ g • x) := by
      simpa using
        ((contMDiff_const : ContMDiff IX I ∞ fun _ : X ↦ g).smul
          (contMDiff_id : ContMDiff IX IX ∞ fun x : X ↦ x))
    simpa [MulAction.toPerm] using hsmul
  contMDiff_invFun := by
    -- The inverse branch is fixed multiplication by `g⁻¹`.
    have hsmulInv : ContMDiff IX IX ∞ (fun x : X ↦ g⁻¹ • x) := by
      simpa using
        ((contMDiff_const : ContMDiff IX I ∞ fun _ : X ↦ g⁻¹).smul
          (contMDiff_id : ContMDiff IX IX ∞ fun x : X ↦ x))
    simpa [MulAction.toPerm] using hsmulInv

/-- Helper for the equivariant rank theorem: `smulDiffeomorph` acts by the given group action. -/
@[simp] theorem smulDiffeomorph_apply
    {EX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX]
    {HX : Type*} [TopologicalSpace HX]
    {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
    {IX : ModelWithCorners 𝕜 EX HX} [IsManifold IX ∞ X]
    [MulAction G X] [ContMDiffSMul I IX ∞ G X] (g : G) (x : X) :
    (@smulDiffeomorph 𝕜 _ EG _ _ HG _ G _ _ _ I
      EX _ _ HX _ X _ _ IX _ _ _ g) x = g • x := rfl

/-- Helper for the equivariant rank theorem: equivariance rewrites as a commuting square for the
fixed-smul diffeomorphisms on source and target. -/
lemma comp_smulDiffeomorph_eq_smulDiffeomorph_comp
    (F : M →[G] N) (g : G) :
    F ∘ (@smulDiffeomorph 𝕜 _ EG _ _ HG _ G _ _ _ I
      EM _ _ HM _ M _ _ IM _ _ _ g) =
      (@smulDiffeomorph 𝕜 _ EG _ _ HG _ G _ _ _ I
        EN _ _ HN _ N _ _ IN _ _ _ g) ∘ F := by
  -- Pointwise, this is exactly the equivariance relation `F (g • x) = g • F x`.
  funext x
  simpa [Function.comp] using F.map_smul' g x

/-- Helper for Theorem 7.25: precomposing a smooth map with the source fixed-smul diffeomorphism
shifts the rank basepoint from `p` to `g • p` without changing the rank. -/
lemma rankAt_comp_smulDiffeomorph
    {I' : ModelWithCorners 𝕜 EG HG} [LieGroup I' ∞ G]
    [ContMDiffSMul I' IM ∞ G M] [ContMDiffSMul I' IN ∞ G N]
    (f : M → N) (hf : ContMDiff IM IN ∞ f) (g : G) (p : M) :
    rankAt IM IN (f ∘ fun x : M => g • x) p =
      rankAt IM IN f (g • p) := by
  -- Rewrite the source action map as a diffeomorphism so its derivative has full range.
  let e :=
    (smulDiffeomorph (I := I') (IX := IM) g).mfderivToContinuousLinearEquiv (by simp) p
  have hSmulEq :
      (fun x : M ↦ g • x) = (smulDiffeomorph (I := I') (IX := IM) g : M → M) := by
    funext x
    rfl
  have hSmulSmooth : ContMDiff IM IM ∞ (fun x : M ↦ g • x) := by
    simpa using contMDiff_const_smul (I := I') (IX := IM) g
  have hSmulRange :
      (mfderiv IM IM (fun x : M ↦ g • x) p).range = ⊤ := by
    -- The derivative is the forward map of the source `smulDiffeomorph`.
    rw [hSmulEq]
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (smulDiffeomorph (I := I') (IX := IM) g) (by simp) (x := p)]
    have hRangeTop :
        (e : TangentSpace IM p →L[𝕜]
          TangentSpace IM ((smulDiffeomorph (I := I') (IX := IM) g) p)).range = ⊤ :=
      LinearMap.range_eq_top.2 e.surjective
    exact hRangeTop
  have hComp :
      mfderiv IM IN (f ∘ fun x : M ↦ g • x) p =
        (mfderiv IM IN f ((fun x : M ↦ g • x) p)).comp
          (mfderiv IM IM (fun x : M ↦ g • x) p) :=
    mfderiv_comp
      (x := p)
      (g := f)
      (f := fun x : M ↦ g • x)
      (hf.mdifferentiableAt (by simp))
      (hSmulSmooth.mdifferentiableAt (by simp))
  have hRangeEq :
      (((mfderiv IM IN f ((fun x : M ↦ g • x) p)).toLinearMap.comp
        (mfderiv IM IM (fun x : M ↦ g • x) p).toLinearMap).range) =
        (mfderiv IM IN f ((fun x : M ↦ g • x) p)).range := by
    simpa using LinearMap.range_comp_of_range_eq_top
      (mfderiv IM IN f ((fun x : M ↦ g • x) p)).toLinearMap
      (show (mfderiv IM IM (fun x : M ↦ g • x) p).toLinearMap.range = ⊤ by
        simpa using hSmulRange)
  -- The chain rule adds an invertible source factor, so the rank only sees the point `g • p`.
  calc
    rankAt IM IN (f ∘ fun x : M ↦ g • x) p
        = Module.finrank 𝕜 ((mfderiv IM IN (f ∘ fun x : M ↦ g • x) p).range) := by
            rw [rankAt_eq_finrank_range_mfderiv]
    _ = Module.finrank 𝕜
          (((mfderiv IM IN f ((fun x : M ↦ g • x) p)).comp
            (mfderiv IM IM (fun x : M ↦ g • x) p)).range) := by
          simpa using congrArg
            (fun f' : TangentSpace IM p →L[𝕜]
              TangentSpace IN ((f ∘ fun x : M ↦ g • x) p) =>
              Module.finrank 𝕜 f'.range)
            hComp
    _ = Module.finrank 𝕜 ((mfderiv IM IN f ((fun x : M ↦ g • x) p)).range) := by
          simpa using congrArg
            (fun q : Submodule 𝕜 (TangentSpace IN (f ((fun x : M ↦ g • x) p))) =>
              Module.finrank 𝕜 q)
            hRangeEq
    _ = rankAt IM IN f (g • p) := by
          rw [← rankAt_eq_finrank_range_mfderiv]

/-- Helper for Theorem 7.25: postcomposing a smooth map with the target fixed-smul diffeomorphism
does not change the manifold rank. -/
lemma rankAt_smulDiffeomorph_comp
    {I' : ModelWithCorners 𝕜 EG HG} [LieGroup I' ∞ G]
    [ContMDiffSMul I' IM ∞ G M] [ContMDiffSMul I' IN ∞ G N]
    (f : M → N) (hf : ContMDiff IM IN ∞ f) (g : G) (p : M) :
    rankAt IM IN ((fun y : N => g • y) ∘ f) p =
      rankAt IM IN f p := by
  -- Rewrite the target action map as a diffeomorphism so its derivative acts by a linear
  -- equivalence on the derivative range of `f`.
  let e :=
    (smulDiffeomorph (I := I') (IX := IN) g).mfderivToContinuousLinearEquiv (by simp) (f p)
  have hSmulEq :
      (fun y : N ↦ g • y) = (smulDiffeomorph (I := I') (IX := IN) g : N → N) := by
    funext y
    rfl
  have hSmulSmooth : ContMDiff IN IN ∞ (fun y : N ↦ g • y) := by
    simpa using contMDiff_const_smul (I := I') (IX := IN) g
  have hComp :
      mfderiv IM IN ((fun y : N ↦ g • y) ∘ f) p =
        (mfderiv IN IN (fun y : N ↦ g • y) (f p)).comp (mfderiv IM IN f p) :=
    mfderiv_comp
      (x := p)
      (g := fun y : N ↦ g • y)
      (f := f)
      (hSmulSmooth.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))
  have hRangeComp :
      (((mfderiv IN IN (fun y : N ↦ g • y) (f p)).comp
        (mfderiv IM IN f p)).range) =
        ((mfderiv IM IN f p).range).map
          (mfderiv IN IN (fun y : N ↦ g • y) (f p)).toLinearMap := by
    simpa using LinearMap.range_comp
      (mfderiv IM IN f p).toLinearMap
      (mfderiv IN IN (fun y : N ↦ g • y) (f p)).toLinearMap
  have hDerivEq :
      mfderiv IN IN (fun y : N ↦ g • y) (f p) =
        (e : TangentSpace IN (f p) →L[𝕜]
          TangentSpace IN ((smulDiffeomorph (I := I') (IX := IN) g) (f p))) := by
    rw [hSmulEq]
    rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe
      (smulDiffeomorph (I := I') (IX := IN) g) (by simp) (x := f p)]
  have hDerivEqLinear :
      (mfderiv IN IN (fun y : N ↦ g • y) (f p)).toLinearMap =
        (e : TangentSpace IN (f p) →L[𝕜]
          TangentSpace IN
            ((smulDiffeomorph (I := I') (IX := IN) g) (f p))).toLinearMap := by
    simpa using congrArg ContinuousLinearMap.toLinearMap hDerivEq
  -- Route correction: keep the target action in one spelling world until the final rank rewrite.
  calc
    rankAt IM IN ((fun y : N ↦ g • y) ∘ f) p
        = Module.finrank 𝕜
            ((mfderiv IM IN ((fun y : N ↦ g • y) ∘ f) p).range) := by
            rw [rankAt_eq_finrank_range_mfderiv]
    _ = Module.finrank 𝕜
          (((mfderiv IN IN (fun y : N ↦ g • y) (f p)).comp
            (mfderiv IM IN f p)).range) := by
          simpa using congrArg
            (fun f' : TangentSpace IM p →L[𝕜]
              TangentSpace IN (((fun y : N ↦ g • y) ∘ f) p) =>
              Module.finrank 𝕜 f'.range)
            hComp
    _ = Module.finrank 𝕜
          (((mfderiv IM IN f p).range).map
            (mfderiv IN IN (fun y : N ↦ g • y) (f p)).toLinearMap) := by
          simpa using congrArg
            (fun q : Submodule 𝕜 (TangentSpace IN ((fun y : N ↦ g • y) (f p))) =>
              Module.finrank 𝕜 q)
            hRangeComp
    _ = Module.finrank 𝕜
          (((mfderiv IM IN f p).range).map
            ((e : TangentSpace IN (f p) →L[𝕜]
              TangentSpace IN
                ((smulDiffeomorph (I := I') (IX := IN) g) (f p))).toLinearMap)) := by
          simpa using congrArg
            (fun f' : TangentSpace IN (f p) →ₗ[𝕜]
              TangentSpace IN ((smulDiffeomorph (I := I') (IX := IN) g) (f p)) =>
              Module.finrank 𝕜 (((mfderiv IM IN f p).range).map f'))
            hDerivEqLinear
    _ = Module.finrank 𝕜 ((mfderiv IM IN f p).range) := by
          simpa [e] using LinearEquiv.finrank_map_eq e.toLinearEquiv
            ((mfderiv IM IN f p).range)
    _ = rankAt IM IN f p := by
          rw [← rankAt_eq_finrank_range_mfderiv]

/-- Helper for the equivariant rank theorem: equivariance transports the manifold rank of `F`
along the source `G`-orbit. -/
theorem rankAt_smul_eq
    {I' : ModelWithCorners 𝕜 EG HG} [LieGroup I' ∞ G]
    [ContMDiffSMul I' IM ∞ G M] [ContMDiffSMul I' IN ∞ G N]
    (F : M →[G] N) (hF : ContMDiff IM IN ∞ F) (g : G) (p : M) :
    rankAt IM IN F (g • p) = rankAt IM IN F p := by
  have hComm : F ∘ (fun x : M => g • x) = (fun y : N => g • y) ∘ F := by
    -- Equivariance identifies the source and target action composites pointwise.
    funext x
    simpa [Function.comp] using F.map_smul' g x
  -- Route correction: compare `rankAt` through the two composition lemmas, then rewrite the
  -- middle composite by equivariance.
  calc
    rankAt IM IN F (g • p) = rankAt IM IN (F ∘ fun x : M => g • x) p := by
      symm
      exact rankAt_comp_smulDiffeomorph (I' := I') (f := F) hF g p
    _ = rankAt IM IN ((fun y : N => g • y) ∘ F) p := by
      rw [hComm]
    _ = rankAt IM IN F p := by
      exact rankAt_smulDiffeomorph_comp (I' := I') (f := F) hF g p

include I in
/-- Helper for Theorem 7.25: the ambient section model specializes the general orbit-invariance
theorem without exposing the extra model parameter at later call sites. -/
theorem rankAt_smul_eq_currentSection
    (F : M →[G] N) (hF : ContMDiff IM IN ∞ F) (g : G) (p : M) :
    rankAt IM IN F (g • p) = rankAt IM IN F p := by
  -- The section already fixes the source action model, so this is just the generic theorem with
  -- that model made explicit once.
  exact rankAt_smul_eq (I' := I) (F := F) hF g p

/-- Theorem 7.25 (Equivariant Rank Theorem): a smooth equivariant map from a smooth manifold
with transitive smooth `G`-action to any smooth `G`-manifold has constant rank. -/
theorem hasConstantRank (F : M →[G] N) (hF : ContMDiff IM IN ∞ F)
    : ∃ r : ℕ, HasConstantRank IM IN F r := sorry

end MulActionHom

end EquivariantRankTheorem

section EquivariantRankTheoremConsequences

universe uEG uHG uG uM uN

variable {m n : ℕ}
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable {I : ModelWithCorners ℝ EG HG} [LieGroup I ∞ G]
variable {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M] [IsManifold (𝓡 m) ∞ M]
variable [MulAction G M] [ContMDiffSMul I (𝓡 m) ∞ G M] [MulAction.IsPretransitive G M]
variable {N : Type uN} [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
variable [MulAction G N] [ContMDiffSMul I (𝓡 n) ∞ G N]

namespace MulActionHom

/-- Consequence of Theorem 7.25 in the book's real-manifold setting: a surjective smooth
equivariant map is a smooth submersion. -/
theorem isSmoothSubmersion_of_surjective
    (F : M →[G] N) (hF : ContMDiff (𝓡 m) (𝓡 n) ∞ F)
    (h_surj : Function.Surjective F) : IsSmoothSubmersion (𝓡 m) (𝓡 n) F := sorry

/-- Consequence of Theorem 7.25 in the book's real-manifold setting: an injective smooth
equivariant map is a smooth immersion. -/
theorem isImmersion_of_injective
    (F : M →[G] N) (hF : ContMDiff (𝓡 m) (𝓡 n) ∞ F)
    (h_inj : Function.Injective F) : IsImmersion (𝓡 m) (𝓡 n) ∞ F := sorry

/-- Consequence of Theorem 7.25 in the book's real-manifold setting: a bijective smooth
equivariant map is a diffeomorphism. -/
theorem exists_diffeomorph_of_bijective
    (F : M →[G] N) (hF : ContMDiff (𝓡 m) (𝓡 n) ∞ F)
    (h_bij : Function.Bijective F) :
    ∃ e : M ≃ₘ⟮𝓡 m, 𝓡 n⟯ N, ∀ x : M, e x = F x := sorry

end MulActionHom

end EquivariantRankTheoremConsequences
