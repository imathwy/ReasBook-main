import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_05.Proposition_1_40
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_09.Example_2_14
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_12.Problem_2_4
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Definition_2_11_extra_3
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Proposition_2_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_8
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Proposition_4_22
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold

section

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]

-- Semantic recall note: `lean_leansearch` confirmed `IsProperMap` and
-- `Manifold.IsSmoothEmbedding` as the canonical owner APIs; nearby Section 6.40 Whitney
-- statements and Proposition 4.22 fixed the source-facing theorem surface.

/-- Helper for Lemma 6.14: the radial compactification of `ℝ^N` into the open unit ball, viewed
in the ambient Euclidean space. -/
noncomputable def boundedEuclideanCompactification (N : ℕ) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) :=
  fun y ↦
    ((Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) y :
      EuclideanSpace ℝ (Fin N))

/-- Helper for Lemma 6.14: the ambient radial compactification map `ℝ^N → ℝ^N` is smooth. -/
lemma boundedEuclideanCompactification_contMDiff (N : ℕ) :
    ContMDiff (𝓡 N) (𝓡 N) ∞ (boundedEuclideanCompactification N) := by
  let g : EuclideanSpace ℝ (Fin N) → unitOpenBall N := fun y ↦
    show unitOpenBall N from
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) y
  have hg : ContMDiff (𝓡 N) (𝓡 N) ∞ g := by
    -- Example 2.14 already packages the subtype-valued radial compactification as a smooth map.
    simpa [g] using unitBall_contMDiff N
  -- Forgetting the open-ball subtype gives the ambient Euclidean map used in the normalization.
  exact (ContMDiff.subtypeVal_comp_iff (unitOpenBall N) g).2 hg

/-- Helper for Lemma 6.14: the radial compactification always lands strictly inside the open unit
ball. -/
lemma boundedEuclideanCompactification_norm_lt_one (N : ℕ)
    (y : EuclideanSpace ℝ (Fin N)) :
    ‖boundedEuclideanCompactification N y‖ < 1 := by
  have hy :
      boundedEuclideanCompactification N y ∈
        Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    -- The homeomorphism target is definitionally the open unit ball.
    exact (Homeomorph.unitBall y).2
  simpa [Metric.mem_ball, dist_eq_norm] using hy

/-- Helper for Lemma 6.14: pairing a continuous map with a proper last coordinate gives a proper
map into the product. -/
lemma isProperMap_prodMk_of_isProperMap_snd
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space (Y × Z)] [CompactlyCoherentSpace (Y × Z)] [T2Space Z] [CompactlyCoherentSpace Z]
    {f : X → Y} {g : X → Z} (hf : Continuous f) (hg : IsProperMap g) :
    IsProperMap (fun x ↦ (f x, g x)) := by
  have hcont : Continuous (fun x ↦ (f x, g x)) := hf.prodMk hg.continuous
  refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, ?_⟩
  intro K hK
  have hsnd : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  have hpre : IsCompact (g ⁻¹' (Prod.snd '' K)) := hg.isCompact_preimage hsnd
  have hclosed : IsClosed ((fun x ↦ (f x, g x)) ⁻¹' K) := hK.isClosed.preimage hcont
  -- Compactness comes from the proper last coordinate; the full preimage is a closed subset of it.
  refine hpre.of_isClosed_subset hclosed ?_
  intro x hx
  exact ⟨(f x, g x), hx, rfl⟩

/-- Helper for Lemma 6.14: composing a smooth map into `ℝ^N` with the radial compactification
keeps it smooth and makes its image bounded by `1`. -/
lemma boundedAmbient_contMDiff {N : ℕ} {F : M → EuclideanSpace ℝ (Fin N)}
    (hF : ContMDiff (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F) :
    ContMDiff (leeBoundaryModelWithCorners n) (𝓡 N) ∞
      (fun x ↦ boundedEuclideanCompactification N (F x)) := by
  -- This is just the chain rule through the ambient radial compactification.
  exact (boundedEuclideanCompactification_contMDiff N).comp hF

/-- Helper for Lemma 6.14: an immersion has injective manifold derivative at every point. -/
lemma mfderivInjective_of_isImmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H' P] [IsManifold J ∞ P]
    {f : N → P}
    (hf : IsImmersion I J ∞ f) :
    ∀ x : N, Function.Injective (mfderiv I J f x) := by
  -- The owner characterization of immersions turns the global immersion back into pointwise
  -- injectivity of the manifold derivative.
  exact (Manifold.is_immersion_iff_forall_injective_mfderiv hf.contMDiff).1 hf

/-- Helper for Lemma 6.14: the ambient radial compactification is injective. -/
lemma boundedEuclideanCompactification_injective (N : ℕ) :
    Function.Injective (boundedEuclideanCompactification N) := by
  intro x y hxy
  -- The ambient equality is equality in the open-ball subtype after restoring the subtype wrapper.
  have hsub :
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) x =
        (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) y := by
    exact Subtype.ext hxy
  exact (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N).injective hsub

/-- Helper for Lemma 6.14: the ambient radial compactification is a topological embedding. -/
lemma boundedEuclideanCompactification_isEmbedding (N : ℕ) :
    Topology.IsEmbedding (boundedEuclideanCompactification N) := by
  let u : EuclideanSpace ℝ (Fin N) → unitOpenBall N := fun y ↦
    show unitOpenBall N from
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) y
  have hu : Topology.IsEmbedding u := by
    -- The subtype-valued radial compactification is literally the unit-ball homeomorphism.
    simpa [u] using
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N).isEmbedding
  -- Composing with the open-subset inclusion gives the ambient Euclidean version.
  simpa [boundedEuclideanCompactification, u] using Topology.IsEmbedding.subtypeVal.comp hu

/-- Helper for Lemma 6.14: the ambient radial compactification has injective manifold derivative at
every point. -/
lemma boundedEuclideanCompactification_mfderiv_injective (N : ℕ)
    (y : EuclideanSpace ℝ (Fin N)) :
    Function.Injective
      (mfderiv
        (𝓡 N)
        (𝓡 N)
        (boundedEuclideanCompactification N)
        y) := by
  let u : EuclideanSpace ℝ (Fin N) → unitOpenBall N := fun z ↦
    show unitOpenBall N from
      (Homeomorph.unitBall : EuclideanSpace ℝ (Fin N) ≃ₜ unitOpenBall N) z
  have huLocal : IsLocalDiffeomorph (𝓡 N) (𝓡 N) ∞ u := by
    -- Example 2.14 already promotes the radial compactification to a diffeomorphism onto the
    -- open unit ball.
    simpa [u] using (unitOpenBallDiffeomorph N).symm.isLocalDiffeomorph
  have huImm : IsImmersion (𝓡 N) (𝓡 N) ∞ u :=
    IsLocalDiffeomorph.isImmersion huLocal
  have huInj :
      Function.Injective (mfderiv (𝓡 N) (𝓡 N) u y) :=
    mfderivInjective_of_isImmersion huImm y
  have hsubImm :
      IsImmersion
        (𝓡 N)
        (𝓡 N)
        ∞
        (Subtype.val : unitOpenBall N → EuclideanSpace ℝ (Fin N)) :=
    (Manifold.IsSmoothEmbedding.of_opens (unitOpenBall N)).isImmersion
  have hsubInj :
      Function.Injective
        (mfderiv
          (𝓡 N)
          (𝓡 N)
          (Subtype.val : unitOpenBall N → EuclideanSpace ℝ (Fin N))
          (u y)) :=
    mfderivInjective_of_isImmersion hsubImm (u y)
  have huDiff :
      MDifferentiableAt (𝓡 N) (𝓡 N) u y :=
    huImm.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hsubDiff :
      MDifferentiableAt
        (𝓡 N)
        (𝓡 N)
        (Subtype.val : unitOpenBall N → EuclideanSpace ℝ (Fin N))
        (u y) :=
    hsubImm.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  -- Route correction: work through the subtype-valued diffeomorphism to avoid asking Lean to
  -- unfold the radial formula directly in the derivative.
  rw [show boundedEuclideanCompactification N =
      (Subtype.val : unitOpenBall N → EuclideanSpace ℝ (Fin N)) ∘ u by
      funext z
      rfl]
  rw [mfderiv_comp (x := y) hsubDiff huDiff]
  exact hsubInj.comp huInj

/-- Helper for Lemma 6.14: the recursive codimension-lowering argument only needs the image to lie
in a bounded tube around some nonzero line. -/
def mapsIntoLineTube {k : ℕ} (Φ : M → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∃ a : EuclideanSpace ℝ (Fin k), a ≠ 0 ∧
    ∃ R : ℝ, 0 < R ∧ ∀ x : M, ∃ t : ℝ, ‖Φ x - t • a‖ < R

/-- Helper for Lemma 6.14: after splitting off the last coordinate, a uniform bound on the first
factor packages the image into a tube around the last-coordinate axis. -/
lemma mapsIntoLineTube_of_splitLast
    {N : ℕ} {g : M → EuclideanSpace ℝ (Fin N)} {s : M → ℝ}
    (hg : ∀ x : M, ‖g x‖ < 1) :
    mapsIntoLineTube
      (fun x ↦
        (split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm (g x, s x)) := by
  let e :
      (EuclideanSpace ℝ (Fin N) × ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (N + 1)) :=
    (split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm
  let a : EuclideanSpace ℝ (Fin (N + 1)) := e (0, (1 : ℝ))
  let R : ℝ := ‖e.toContinuousLinearMap‖ + 1
  refine ⟨a, ?_, R, by positivity, ?_⟩
  · -- The chosen axis is the last-coordinate line transported through the split equivalence.
    intro ha
    have hsource : ((0 : EuclideanSpace ℝ (Fin N)), (1 : ℝ)) = 0 := by
      have haxis : e (0, (1 : ℝ)) = e 0 := by
        simpa [a] using ha
      exact e.injective haxis
    have hone : (1 : ℝ) = 0 := by
      exact congrArg Prod.snd hsource
    exact one_ne_zero hone
  · intro x
    refine ⟨s x, ?_⟩
    have hEq :
        (e (g x, s x)) - s x • a = e (g x, (0 : ℝ)) := by
      -- Subtracting the axis component kills the last coordinate and leaves only the bounded part.
      change e (g x, s x) - s x • e (0, (1 : ℝ)) = e (g x, (0 : ℝ))
      rw [← map_smul, ← map_sub]
      simp [Prod.smul_mk]
    have hnorm_nonneg : 0 ≤ ‖e.toContinuousLinearMap‖ := norm_nonneg _
    calc
      ‖(e (g x, s x)) - s x • a‖ = ‖e (g x, (0 : ℝ))‖ := by
        rw [hEq]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖(g x, (0 : ℝ))‖ := by
        exact e.toContinuousLinearMap.le_opNorm (g x, (0 : ℝ))
      _ = ‖e.toContinuousLinearMap‖ * ‖g x‖ := by
        simp
      _ ≤ ‖e.toContinuousLinearMap‖ * 1 := by
        exact mul_le_mul_of_nonneg_left (le_of_lt (hg x)) hnorm_nonneg
      _ = ‖e.toContinuousLinearMap‖ := by ring
      _ < R := by
        dsimp [R]
        linarith

/-- Helper for Lemma 6.14: the split-last linear equivalence is smooth when the domain is read
with the product-manifold charts. -/
lemma splitLastSymm_contMDiff (N : ℕ) :
    ContMDiff
      ((𝓡 N).prod 𝓘(ℝ, ℝ))
      (𝓡 (N + 1))
      ∞
      ((split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm) := by
  let e :
      (EuclideanSpace ℝ (Fin N) × ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (N + 1)) :=
    (split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm
  let idProd : EuclideanSpace ℝ (Fin N) × ℝ → EuclideanSpace ℝ (Fin N) × ℝ :=
    fun y ↦ (y.1, y.2)
  have hId :
      ContMDiff
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ))
        ∞
        idProd := by
    -- The coordinatewise identity is smooth because both product projections are smooth.
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    simpa [idProd] using
      (contMDiff_fst : ContMDiff ((𝓡 N).prod 𝓘(ℝ, ℝ)) (𝓡 N) ∞ Prod.fst).prodMk
        (contMDiff_snd : ContMDiff ((𝓡 N).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ Prod.snd)
  -- Compose the product-chart identity with the ambient linear map.
  simpa [idProd, Function.comp, e] using e.toContinuousLinearMap.contMDiff.comp hId

/-- Helper for Lemma 6.14: the split-last linear equivalence is a topological embedding. -/
lemma splitLastSymm_isEmbedding (N : ℕ) :
    Topology.IsEmbedding
      ((split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm) := by
  let e :
      (EuclideanSpace ℝ (Fin N) × ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (N + 1)) :=
    (split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm
  -- The ambient linear equivalence is already a homeomorphism.
  simpa [e] using e.toHomeomorph.isEmbedding

/-- Helper for Lemma 6.14: the split-last linear equivalence is a smooth embedding into ambient
Euclidean space. -/
lemma splitLastSymm_isSmoothEmbedding (N : ℕ) :
    IsSmoothEmbedding
      ((𝓡 N).prod 𝓘(ℝ, ℝ))
      (𝓡 (N + 1))
      ∞
      ((split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm) := by
  have hSmooth := splitLastSymm_contMDiff N
  have hEmb := splitLastSymm_isEmbedding N
  -- Route correction: the product-chart smoothness and topological embedding parts are now
  -- isolated. The remaining blocker is to package the chart-identity derivative as injective so
  -- the immersion field can be discharged cleanly.
  -- TODO: prove the immersion field by factoring through the product-chart identity
  -- `idProd : ((𝓡 N).prod 𝓘(ℝ, ℝ)) → 𝓘(ℝ, EuclideanSpace ℝ (Fin N) × ℝ)` and showing its
  -- manifold derivative is injective at every point.
  sorry

/-- Helper for Lemma 6.14: pairing a smooth embedding into `ℝ^N` with a smooth exhaustion
function gives a proper smooth embedding into `ℝ^N × ℝ`. -/
lemma properProductEmbeddingOfSmoothEmbedding
    {N : ℕ} {F : M → EuclideanSpace ℝ (Fin N)}
    (hF : IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F) :
    ∃ Φ : M → EuclideanSpace ℝ (Fin N) × ℝ,
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ ∧
      IsProperMap Φ := by
  haveI : T2Space M := hF.isEmbedding.t2Space
  haveI : SecondCountableTopology M := hF.isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace M :=
    topologicalManifoldWithBoundary_locallyCompactSpace
  haveI : SigmaCompactSpace M :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  have hExhaust :
      ∃ f : C^∞⟮leeBoundaryModelWithCorners n, M; ℝ⟯,
        (∀ x : M, 0 < f x) ∧ (f : M → ℝ).IsExhaustionFunction :=
    exists_positive_smooth_exhaustion_function (leeBoundaryModelWithCorners n)
  rcases hExhaust with ⟨f, -, hfexhaust⟩
  let Φ : M → EuclideanSpace ℝ (Fin N) × ℝ := fun x ↦ (F x, f x)
  have hFcont :
      ContMDiff (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F :=
    hF.isImmersion.contMDiff
  have hΦcont :
      ContMDiff
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ := by
    -- The product map is smooth because both components are smooth.
    simpa [Φ] using hFcont.prodMk f.contMDiff
  have hF_mfderiv :
      ∀ x : M, Function.Injective
        (mfderiv (leeBoundaryModelWithCorners n) (𝓡 N) F x) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hFcont).1 hF.isImmersion
  have hΦImm :
      IsImmersion
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ := by
    -- The first coordinate of the product derivative is exactly the derivative of `F`, so the
    -- existing immersion of `F` forces the whole product derivative to be injective.
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΦcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv
            (leeBoundaryModelWithCorners n)
            ((𝓡 N).prod 𝓘(ℝ, ℝ))
            Φ
            x =
          (mfderiv (leeBoundaryModelWithCorners n) (𝓡 N) F x).prod
            (mfderiv (leeBoundaryModelWithCorners n) 𝓘(ℝ, ℝ) (fun y : M ↦ f y) x) := by
      -- `mfderiv_prodMk` gives the product derivative in the exact form needed for the first
      -- projection argument below.
      simpa [Φ] using
        (mfderiv_prodMk
          (I := leeBoundaryModelWithCorners n)
          (I' := 𝓡 N)
          (I'' := 𝓘(ℝ, ℝ))
          (f := F)
          (g := fun y : M ↦ f y)
          (x := x)
          (hFcont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (f.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv
              (leeBoundaryModelWithCorners n)
              ((𝓡 N).prod 𝓘(ℝ, ℝ))
              Φ
              x) v).1 =
          ((mfderiv
              (leeBoundaryModelWithCorners n)
              ((𝓡 N).prod 𝓘(ℝ, ℝ))
              Φ
              x) w).1 := by
      exact congrArg Prod.fst hvw
    exact hF_mfderiv x <| by
      simpa [hDeriv] using hFirst
  have hΦEmb : Topology.IsEmbedding Φ := by
    have hGraphEmb : Topology.IsEmbedding (fun x : M ↦ (x, f x)) :=
      isEmbedding_graph f.contMDiff.continuous
    have hProdEmb : Topology.IsEmbedding (Prod.map F (id : ℝ → ℝ)) :=
      hF.isEmbedding.prodMap Topology.IsEmbedding.id
    -- Factor the graph map through the original embedding in the first coordinate.
    simpa [Φ, Function.comp] using hProdEmb.comp hGraphEmb
  have hΦProper : IsProperMap Φ := by
    -- Properness comes entirely from the exhaustion coordinate.
    exact isProperMap_prodMk_of_isProperMap_snd hFcont.continuous hfexhaust.isProperMap
  refine ⟨Φ, ?_, hΦProper⟩
  -- The product graph is a smooth immersion and a topological embedding.
  exact ⟨hΦImm, hΦEmb⟩

/-- Helper for Lemma 6.14: after radial compactification and splitting off the last coordinate, a
smooth embedding into `ℝ^N` yields an explicit proper smooth embedding into `ℝ^(N + 1)` whose
image lies in a bounded tube around a line. -/
lemma properTubeEmbeddingOfSmoothEmbedding
    {N : ℕ} {F : M → EuclideanSpace ℝ (Fin N)}
    (hF : IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F) :
    ∃ G : M → EuclideanSpace ℝ (Fin (N + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (N + 1)) ∞ G ∧
        IsProperMap G ∧ mapsIntoLineTube G := by
  haveI : T2Space M := hF.isEmbedding.t2Space
  haveI : SecondCountableTopology M := hF.isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace M :=
    topologicalManifoldWithBoundary_locallyCompactSpace
  haveI : SigmaCompactSpace M :=
    sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨f, -, hfexhaust⟩ :
      ∃ f : C^∞⟮leeBoundaryModelWithCorners n, M; ℝ⟯,
        (∀ x : M, 0 < f x) ∧ (f : M → ℝ).IsExhaustionFunction :=
    exists_positive_smooth_exhaustion_function (leeBoundaryModelWithCorners n)
  let g : M → EuclideanSpace ℝ (Fin N) := fun x ↦
    boundedEuclideanCompactification N (F x)
  let Φ : M → EuclideanSpace ℝ (Fin N) × ℝ := fun x ↦ (g x, f x)
  let e :
      (EuclideanSpace ℝ (Fin N) × ℝ) ≃L[ℝ]
        EuclideanSpace ℝ (Fin (N + 1)) :=
    (split_at_coordinate_continuousLinearEquiv (k := N) (Fin.last N)).symm
  let G : M → EuclideanSpace ℝ (Fin (N + 1)) := fun x ↦ e (Φ x)
  have hFcont :
      ContMDiff (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F :=
    hF.isImmersion.contMDiff
  have hgcont :
      ContMDiff (leeBoundaryModelWithCorners n) (𝓡 N) ∞ g :=
    boundedAmbient_contMDiff hFcont
  have hgmfderiv :
      ∀ x : M, Function.Injective
        (mfderiv (leeBoundaryModelWithCorners n) (𝓡 N) g x) := by
    intro x
    have hcompactDiff :
        MDifferentiableAt
          (𝓡 N)
          (𝓡 N)
          (boundedEuclideanCompactification N)
          (F x) :=
      (boundedEuclideanCompactification_contMDiff N).contMDiffAt.mdifferentiableAt
        (by simp : (∞ : ℕ∞ω) ≠ 0)
    have hFdiff :
        MDifferentiableAt
          (leeBoundaryModelWithCorners n)
          (𝓡 N)
          F
          x :=
      hFcont.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
    -- The compactification has injective derivative, so composing it with the embedded `F`
    -- preserves injectivity of the manifold derivative.
    rw [show g = boundedEuclideanCompactification N ∘ F by
      funext y
      rfl]
    rw [mfderiv_comp (x := x) hcompactDiff hFdiff]
    exact (boundedEuclideanCompactification_mfderiv_injective N (F x)).comp
      (mfderivInjective_of_isImmersion hF.isImmersion x)
  have hΦcont :
      ContMDiff
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ := by
    -- The compactified Euclidean factor and the exhaustion coordinate are both smooth.
    simpa [Φ] using hgcont.prodMk f.contMDiff
  have hΦImm :
      IsImmersion
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ := by
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hΦcont).2 ?_
    intro x v w hvw
    have hDeriv :
        mfderiv
            (leeBoundaryModelWithCorners n)
            ((𝓡 N).prod 𝓘(ℝ, ℝ))
            Φ
            x =
          (mfderiv (leeBoundaryModelWithCorners n) (𝓡 N) g x).prod
            (mfderiv (leeBoundaryModelWithCorners n) 𝓘(ℝ, ℝ) (fun y : M ↦ f y) x) := by
      -- `mfderiv_prodMk` puts the first factor into a form where the compactified derivative
      -- injectivity closes the goal directly.
      simpa [Φ] using
        (mfderiv_prodMk
          (I := leeBoundaryModelWithCorners n)
          (I' := 𝓡 N)
          (I'' := 𝓘(ℝ, ℝ))
          (f := g)
          (g := fun y : M ↦ f y)
          (x := x)
          (hgcont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (f.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hFirst :
        ((mfderiv
              (leeBoundaryModelWithCorners n)
              ((𝓡 N).prod 𝓘(ℝ, ℝ))
              Φ
              x) v).1 =
          ((mfderiv
              (leeBoundaryModelWithCorners n)
              ((𝓡 N).prod 𝓘(ℝ, ℝ))
              Φ
              x) w).1 := by
      exact congrArg Prod.fst hvw
    exact hgmfderiv x <| by
      simpa [hDeriv] using hFirst
  have hgEmb : Topology.IsEmbedding g := by
    -- Topological embedding survives ambient compactification because the radial map is itself an
    -- embedding into the open unit ball.
    exact (boundedEuclideanCompactification_isEmbedding N).comp hF.isEmbedding
  have hΦEmb : Topology.IsEmbedding Φ := by
    have hGraphEmb : Topology.IsEmbedding (fun x : M ↦ (x, f x)) :=
      isEmbedding_graph f.contMDiff.continuous
    have hProdEmb : Topology.IsEmbedding (Prod.map g (id : ℝ → ℝ)) :=
      hgEmb.prodMap Topology.IsEmbedding.id
    -- Factor the graph map through the compactified first coordinate.
    simpa [Φ, Function.comp] using hProdEmb.comp hGraphEmb
  have hΦProper : IsProperMap Φ := by
    -- Properness still comes entirely from the exhaustion coordinate.
    exact isProperMap_prodMk_of_isProperMap_snd hgcont.continuous hfexhaust.isProperMap
  have hTube : mapsIntoLineTube G := by
    have hgBound : ∀ x : M, ‖g x‖ < 1 := by
      intro x
      simpa [g] using boundedEuclideanCompactification_norm_lt_one N (F x)
    -- Splitting off the last coordinate turns the uniformly bounded first factor into a line tube.
    simpa [G, Φ, g, e] using
      (mapsIntoLineTube_of_splitLast (M := M) (g := g) (s := fun x ↦ f x) hgBound)
  have hΦSmooth :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners n)
        ((𝓡 N).prod 𝓘(ℝ, ℝ))
        ∞
        Φ := ⟨hΦImm, hΦEmb⟩
  have hGSmooth :
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners n)
        (𝓡 (N + 1))
        ∞
        G := by
    -- Route correction: own the product-to-ambient transport once through the split diffeomorphism.
    simpa [G, Φ, e, Function.comp] using
      Manifold.IsSmoothEmbedding.comp (splitLastSymm_isSmoothEmbedding N) hΦSmooth
  have hGProper : IsProperMap G := by
    have heProper : IsProperMap e := by
      simpa [e] using e.toHomeomorph.isProperMap
    exact heProper.comp hΦProper
  exact ⟨G, hGSmooth, hGProper, hTube⟩

/-- Lemma 6.14: let `M` be a smooth `n`-manifold with or without boundary. If `M` admits a smooth
embedding into `ℝ^N` for some `N`, then it admits a proper smooth embedding into
`ℝ^(2 * n + 1)`. -/
  theorem exists_proper_isSmoothEmbedding_euclidean_of_exists_isSmoothEmbedding_euclidean
    (h : ∃ N : ℕ, ∃ F : M → EuclideanSpace ℝ (Fin N),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 N) ∞ F) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (leeBoundaryModelWithCorners n) (𝓡 (2 * n + 1)) ∞ F ∧
        IsProperMap F := by
  rcases h with ⟨N, F, hF⟩
  rcases properTubeEmbeddingOfSmoothEmbedding hF with ⟨G, hGSmooth, hGProper, hTube⟩
  -- Route correction: the front-end normalization is now complete. We have an explicit proper
  -- ambient smooth embedding into `ℝ^(N + 1)` together with the line-tube invariant from Lee's
  -- proof.
  -- TODO: use Proposition 5.2 and Lemma 6.13 to perform the codimension-drop step on this
  -- stabilized front-end package and recurse down to ambient dimension `2 * n + 1`.
  -- The remaining blocker is now only the geometric codimension descent, not the front-end smooth
  -- transport or the properness/tube setup.
  have _ := hGSmooth
  have _ := hGProper
  have _ := hTube
  sorry

end
