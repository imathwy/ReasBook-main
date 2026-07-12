import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.PartitionOfUnity
import SmoothManifolds_Lee_2012.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.Chap02.Sec02_11.Definition_2_11_extra_2
import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_32.Definition_5_32_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Theorem_6_15
import SmoothManifolds_Lee_2012.Chap06.Sec06_40.Corollary_6_16
import SmoothManifolds_Lee_2012.Chap06.Sec06_41.Theorem_6_21
import SmoothManifolds_Lee_2012.Chap06.Sec06_42.Theorem_6_24
import SmoothManifolds_Lee_2012.Chap06.Sec06_42.Proposition_6_25

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open Manifold
open NormalBundle

noncomputable section

-- Domain sampling pass:
-- * source-facing layer: Whitney approximation for continuous maps into a smooth manifold, with
--   and without a relative closed-subset constraint.
-- * source-facing owner for the relative hypothesis: `Function.IsSmoothOn` on the restricted map.
-- * core/canonical owner available upstream: mathlib's
--   `Continuous.exists_contMDiff_approx_and_eqOn`, which handles the vector-space target case.
-- * bridge/view owner used in this chapter: mathlib's `ContinuousMap.Homotopic` and
--   `ContinuousMap.HomotopicRel` relations on the underlying continuous maps.
-- Semantic search note: `lean_leansearch` surfaced only the `SmoothApprox` approximation owners,
-- so this item keeps the source-facing homotopy theorem here and uses the relative clause as the
-- main labeled entry.

universe uN uM

section

variable {n m : ℕ}
variable {N : Type uN} [TopologicalSpace N] [SmoothManifoldWithBoundary n N]
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold m M]
  [IsManifold (𝓡 m) ∞ M]

/-- Helper for Theorem 6.26: bundle a codomain-restricted continuous map as a `ContinuousMap`. -/
def continuousMapCodRestrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) : C(X, s) :=
  ⟨Set.codRestrict f s hs, f.continuous.codRestrict hs⟩

/-- Helper for Theorem 6.26: the bundled codomain restriction evaluates to the original map. -/
@[simp] theorem continuousMapCodRestrict_apply {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (s : Set Y) (hs : ∀ x, f x ∈ s) (x : X) :
    continuousMapCodRestrict f s hs x = ⟨f x, hs x⟩ :=
  rfl

/-- Helper for Theorem 6.26: an open subset of Euclidean space admits a continuous positive
radius function whose metric balls stay inside that open set. -/
lemma continuousOpenRadiusFunction {k : ℕ}
    (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k))) :
    ∃ ρ : EuclideanSpace ℝ (Fin k) → ℝ,
      Continuous ρ ∧
      (∀ x ∈ (U : Set (EuclideanSpace ℝ (Fin k))), 0 < ρ x) ∧
      (∀ x ∈ (U : Set (EuclideanSpace ℝ (Fin k))), Metric.ball x (ρ x) ⊆ (U : Set _)) := by
  by_cases hcompl : ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ).Nonempty
  · refine ⟨fun x ↦ Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) / 2, ?_, ?_, ?_⟩
    · -- The distance-to-complement function is continuous, hence so is its half.
      exact (Metric.continuous_infDist_pt ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ)).div_const 2
    · intro x hx
      have hxnot : x ∉ ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) := by
        simpa using hx
      have hpos :
          0 < Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) := by
        exact (IsClosed.notMem_iff_infDist_pos U.isOpen.isClosed_compl hcompl).mp hxnot
      exact div_pos hpos two_pos
    · intro x hx
      have hsubset :
          Metric.ball x (Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ)) ⊆
            (U : Set (EuclideanSpace ℝ (Fin k))) :=
        Metric.ball_infDist_compl_subset
      have hhalf :
          Metric.ball x (Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) / 2) ⊆
            Metric.ball x (Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ)) := by
        intro y hy
        have hnonneg :
            0 ≤ Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) :=
          Metric.infDist_nonneg
        exact
          (Metric.ball_subset_ball
            (show
              Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) / 2 ≤
                Metric.infDist x ((U : Set (EuclideanSpace ℝ (Fin k)))ᶜ) by
              nlinarith)) hy
      exact hhalf.trans hsubset
  · refine ⟨fun _ ↦ 1, continuous_const, ?_, ?_⟩
    · intro x hx
      norm_num
    · intro x hx
      have hUniv : (U : Set (EuclideanSpace ℝ (Fin k))) = Set.univ := by
        ext y
        by_cases hy : y ∈ (U : Set (EuclideanSpace ℝ (Fin k)))
        · simp [hy]
        · exact False.elim (hcompl ⟨y, hy⟩)
      simpa [hUniv]

/-- Helper for Theorem 6.26: composing a map that is smooth on a closed subset with a smooth
embedding into Euclidean space preserves the source-facing `IsSmoothOn` hypothesis. -/
lemma isSmoothOn_comp_contMDiffEmbedding
    {A : Set N} {k : ℕ}
    {f : A → M} (hf : f.IsSmoothOn (leeBoundaryModelWithCorners n) (𝓡 m))
    {e : M → EuclideanSpace ℝ (Fin k)}
    (he : Manifold.IsSmoothEmbedding (𝓡 m) (𝓡 k) ∞ e) :
    (fun x : A ↦ e (f x)).IsSmoothOn (leeBoundaryModelWithCorners n) (𝓡 k) := by
  -- Unpack the source-facing local-extension formulation and postcompose each extension with `e`.
  rw [Function.isSmoothOn_iff_exists_local_extension] at hf ⊢
  intro x
  rcases hf x with ⟨U, hU_open, hxU, Fext, hFext, hEq⟩
  refine ⟨U, hU_open, hxU, e ∘ Fext, ?_, ?_⟩
  · simpa [Function.comp] using he.isImmersion.contMDiff.comp_contMDiffOn hFext
  · intro y hy
    simpa [Function.comp] using congrArg e (hEq y hy)

/-- Helper for Theorem 6.26: if every affine segment from `f` to `g` stays in `U`, then the
codomain restrictions of `f` and `g` are homotopic relative to the set on which they agree. -/
lemma affineHomotopyCodRestrict {B : Set N} {ℓ : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin ℓ))}
    {f g : C(N, EuclideanSpace ℝ (Fin ℓ))}
    (hfg : Set.EqOn f g B)
    (hU : ∀ t x, ContinuousMap.Homotopy.affine f g (t, x) ∈ U) :
    (continuousMapCodRestrict f U (fun x ↦ by
      simpa [ContinuousMap.Homotopy.affine_apply] using hU 0 x)).HomotopicRel
      (continuousMapCodRestrict g U (fun x ↦ by
        simpa [ContinuousMap.Homotopy.affine_apply] using hU 1 x)) B := by
  -- Package the ambient affine homotopy as a homotopy in the open subtype `U`.
  refine ⟨{
    toHomotopy := {
      toFun := fun p ↦ ⟨ContinuousMap.Homotopy.affine f g p, hU p.1 p.2⟩
      continuous_toFun :=
        (ContinuousMap.Homotopy.affine f g).continuous.subtype_mk
          (fun p ↦ hU p.1 p.2)
      map_zero_left := by
        intro x
        apply Subtype.ext
        simp [continuousMapCodRestrict_apply, ContinuousMap.Homotopy.affine_apply]
      map_one_left := by
        intro x
        apply Subtype.ext
        simp [continuousMapCodRestrict_apply, ContinuousMap.Homotopy.affine_apply]
    }
    prop' := by
      intro t x hx
      have hfgx : f x = g x := hfg hx
      apply Subtype.ext
      simp [continuousMapCodRestrict_apply, hfgx]
  }⟩

/-- Helper for Theorem 6.26: retracting the canonical inclusion of the embedded range and then
transporting back by the range diffeomorphism recovers the original point of `M`. -/
lemma retractionInclusion_eq_idOnEmbeddedRange {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin k))}
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]
    [IsManifold (𝓡 m) ∞ S]
    (ψ : M ≃ₘ⟮𝓡 m, 𝓡 m⟯ S)
    [IsEmbeddedSubmanifold (𝓡 k) (𝓡 m) S]
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) (NM[k, m; S])]
    [IsManifold (𝓡 k) ∞ (NM[k, m; S])]
    (T : NormalBundle.TubularNeighborhood k m S)
    (hLeftInverse : Function.LeftInverse T.retraction (Set.inclusion T.contains_base)) :
    ∀ x : M, ψ.symm (T.retraction (Set.inclusion T.contains_base (ψ x))) = x := by
  intro x
  -- Apply the range diffeomorphism inverse to the retraction identity on the embedded point.
  simpa using congrArg ψ.symm (hLeftInverse (ψ x))

/-- Theorem 6.26 (Whitney Approximation Theorem). If `F : N → M` is already smooth on a
closed subset `A ⊆ N`, then the homotopy can be taken to be relative to `A`. -/
theorem exists_homotopicRel_to_smooth_map_of_isClosed
    (F : C(N, M)) {A : Set N} (hA : IsClosed A)
    (hFA : (fun x : A ↦ F x).IsSmoothOn (leeBoundaryModelWithCorners n) (𝓡 m)) :
    ∃ G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯,
      F.HomotopicRel (G : C(N, M)) A := by
  -- Route correction: replace the local duplicate tube API with the earlier canonical range and
  -- retraction owners, then run the textbook Euclidean approximation inside the chosen tube.
  obtain ⟨e, he, -⟩ := _root_.weak_whitney_embedding_boundaryless (M := M) (n := m)
  obtain ⟨csS, hsS, hSubtype, ψ, hψ⟩ :=
    _root_.smoothEmbeddingRangeData
      (J := 𝓡 m)
      (I := 𝓡 (2 * m + 1))
      (N := M)
      (M := EuclideanSpace ℝ (Fin (2 * m + 1)))
      (F := e)
      he
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) (Set.range e) := csS
  let _ : IsManifold (𝓡 m) ∞ (Set.range e) := hsS
  have hEmbedded : IsEmbeddedSubmanifold (𝓡 (2 * m + 1)) (𝓡 m) (Set.range e) := by
    simpa using
      (_root_.embeddedSubmanifoldOfSubtypeEmbedding (n := m) (m := 2 * m + 1) hSubtype)
  let _ : IsEmbeddedSubmanifold (𝓡 (2 * m + 1)) (𝓡 m) (Set.range e) := hEmbedded
  -- Choose a tubular neighborhood of the embedded range and its canonical smooth retraction.
  rcases embedded_submanifold_has_tubular_neighborhood
      (n := 2 * m + 1) (m := m) (M := Set.range e) with
    ⟨csNM, hsNM, hTube⟩
  let _ :
      ChartedSpace
        (EuclideanSpace ℝ (Fin (2 * m + 1)))
        (NM[2 * m + 1, m; Set.range e]) := csNM
  let _ : IsManifold (𝓡 (2 * m + 1)) ∞ (NM[2 * m + 1, m; Set.range e]) := hsNM
  rcases hTube with ⟨T⟩
  rcases tubular_neighborhood_has_retraction_and_smooth_submersion
      (n := 2 * m + 1) (m := m) (M := Set.range e) T with
    ⟨hLeftInverse, hRetr⟩
  -- View the original map in the ambient Euclidean space and pick a positive tube-radius gauge.
  let eF : C(N, EuclideanSpace ℝ (Fin (2 * m + 1))) :=
    ⟨fun x ↦ e (F x), he.isImmersion.contMDiff.continuous.comp F.continuous⟩
  obtain ⟨ρ, hρcont, hρpos, hρball⟩ := continuousOpenRadiusFunction T.neighborhood
  have hBase : ∀ x : N, eF x ∈ (T.neighborhood : Set (EuclideanSpace ℝ (Fin (2 * m + 1)))) := by
    intro x
    simpa [eF, hψ (F x)] using T.contains_base (ψ (F x)).property
  let δ : N → ℝ := fun x ↦ ρ (eF x)
  have hδcont : Continuous δ := hρcont.comp eF.continuous
  have hδpos : ∀ x : N, 0 < δ x := by
    intro x
    exact hρpos (eF x) (hBase x)
  -- Postcomposing the relative smoothness hypothesis with the Euclidean embedding keeps it smooth.
  have hFAe :
      (fun x : A ↦ e (F x)).IsSmoothOn
        (leeBoundaryModelWithCorners n) (𝓡 (2 * m + 1)) := by
    simpa [Function.comp] using
      isSmoothOn_comp_contMDiffEmbedding (f := fun x : A ↦ F x) hFA he
  -- Approximate the embedded map by a smooth Euclidean map that still agrees with `F` on `A`.
  let _ : SigmaCompactSpace N := by
    infer_instance
  obtain ⟨ftilde, hEqOn, hClose⟩ :=
    Manifold.exists_smooth_approximation_eqOn_of_isClosed
      (F := fun x : N ↦ e (F x))
      eF.continuous
      hδcont
      hδpos
      hA
      hFAe
  rw [delta_close_iff] at hClose
  have hftildeU :
      ∀ x : N, ftilde x ∈ (T.neighborhood : Set (EuclideanSpace ℝ (Fin (2 * m + 1)))) := by
    intro x
    have hball :
        ftilde x ∈ Metric.ball (eF x) (δ x) := by
      simpa [Metric.mem_ball, eF, δ] using hClose x
    exact hρball (eF x) (hBase x) hball
  have hSegment :
      ∀ t x,
        ContinuousMap.Homotopy.affine eF (ftilde : C(N, EuclideanSpace ℝ (Fin (2 * m + 1))))
            (t, x) ∈
          (T.neighborhood : Set (EuclideanSpace ℝ (Fin (2 * m + 1)))) := by
    intro t x
    have hSegmentBall :
        segment ℝ (eF x) (ftilde x) ⊆ Metric.ball (eF x) (δ x) :=
      (convex_ball (eF x) (δ x)).segment_subset
        (Metric.mem_ball_self (hδpos x))
        (by simpa [Metric.mem_ball, eF, δ] using hClose x)
    have hmemBall :
        ContinuousMap.Homotopy.affine eF (ftilde : C(N, EuclideanSpace ℝ (Fin (2 * m + 1))))
            (t, x) ∈
          Metric.ball (eF x) (δ x) := by
      refine hSegmentBall ?_
      simpa [ContinuousMap.Homotopy.affine_apply, Path.segment_apply] using
        lineMap_mem_segment ℝ (eF x) (ftilde x) t.2
    exact hρball (eF x) (hBase x) hmemBall
  let f0 : C(N, T.neighborhood) :=
    continuousMapCodRestrict eF (T.neighborhood : Set (EuclideanSpace ℝ (Fin (2 * m + 1)))) hBase
  let f1 : C(N, T.neighborhood) :=
    continuousMapCodRestrict
      (ftilde : C(N, EuclideanSpace ℝ (Fin (2 * m + 1))))
      (T.neighborhood : Set (EuclideanSpace ℝ (Fin (2 * m + 1))))
      hftildeU
  let retractToTarget : C(T.neighborhood, M) :=
    ⟨fun y ↦ ψ.symm (T.retraction y), ψ.symm.continuous.comp hRetr.contMDiff.continuous⟩
  have hSubtypeSmooth :
      ContMDiff
        (leeBoundaryModelWithCorners n)
        (𝓡 (2 * m + 1))
        ∞
        (fun x : N ↦ (⟨ftilde x, hftildeU x⟩ : T.neighborhood)) := by
    simpa using
      contMDiff_codRestrict_opens
        (I := 𝓡 (2 * m + 1))
        (K := leeBoundaryModelWithCorners n)
        T.neighborhood
        ftilde.contMDiff
        hftildeU
  let Gcont : C(N, M) := retractToTarget.comp f1
  have hGcontMDiff :
      ContMDiff (leeBoundaryModelWithCorners n) (𝓡 m) ∞ Gcont := by
    -- The final smooth map is the codomain-restricted approximation followed by retraction.
    simpa [Gcont, retractToTarget, f1, Function.comp, continuousMapCodRestrict] using
      ψ.symm.contMDiff.comp (hRetr.contMDiff.comp hSubtypeSmooth)
  let G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯ := ⟨Gcont, hGcontMDiff⟩
  have hAffineRel : f0.HomotopicRel f1 A := by
    -- The straight-line homotopy stays inside the tubular neighborhood by the radius control.
    refine affineHomotopyCodRestrict (f := eF) (g := (ftilde : C(N, _))) ?_ hSegment
    intro x hx
    exact (hEqOn hx).symm
  have hPostcompose :
      (retractToTarget.comp f0).HomotopicRel Gcont A :=
    ContinuousMap.HomotopicRel.comp_continuousMap hAffineRel retractToTarget
  have hStart :
      retractToTarget.comp f0 = F := by
    ext x
    change ψ.symm (T.retraction (f0 x)) = F x
    have hcod : f0 x = Set.inclusion T.contains_base (ψ (F x)) := by
      apply Subtype.ext
      simpa [f0, eF, continuousMapCodRestrict_apply, hψ (F x)]
    rw [hcod]
    simpa using
      retractionInclusion_eq_idOnEmbeddedRange
        (ψ := ψ)
        (T := T)
        hLeftInverse
        (F x)
  refine ⟨G, ?_⟩
  simpa [G, Gcont, hStart] using hPostcompose

/-- Companion corollary: taking `A = ∅` recovers the non-relative Whitney approximation
statement. -/
theorem exists_homotopic_to_smooth_map
    (F : C(N, M)) :
    ∃ G : C^∞⟮leeBoundaryModelWithCorners n, N; 𝓡 m, M⟯,
      F.Homotopic (G : C(N, M)) := by
  -- Specialize the relative theorem to the empty subset and drop the vacuous relative condition.
  have hEmptySmooth :
      (fun x : (∅ : Set N) ↦ F x).IsSmoothOn (leeBoundaryModelWithCorners n) (𝓡 m) := by
    rw [Function.isSmoothOn_iff_exists_local_extension]
    intro x
    exact False.elim x.2
  rcases exists_homotopicRel_to_smooth_map_of_isClosed
      (n := n) (m := m) (F := F) (A := ∅) isClosed_empty hEmptySmooth with
    ⟨G, hG⟩
  refine ⟨G, ?_⟩
  exact (ContinuousMap.homotopicRel_empty).mp hG

end
