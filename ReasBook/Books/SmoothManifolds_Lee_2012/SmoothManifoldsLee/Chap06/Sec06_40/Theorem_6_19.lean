import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.Maps.Proper.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_11.Proposition_2_28
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Exercise_4_16
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_22.Proposition_4_8
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap04.Sec04_24.Proposition_4_22
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_40.Corollary_6_16
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_40.Theorem_6_18
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_40.Theorem_6_15

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` was unavailable in this environment, so local Whitney
-- immersion/embedding precedents, mathlib's `WhitneyEmbedding` API, and the intrinsic manifold
-- owner guidance in `IsManifold.Basic` were inspected directly.

open scoped ContDiff Manifold

namespace Manifold

noncomputable section

universe uM

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [TopologicalManifold n M] [IsManifold (𝓡 n) ∞ M]

/-- Helper for Theorem 6.19: reuse the earlier weak Whitney owner theorem instead of shadowing it
inside this file. -/
theorem weakWhitneyEmbeddingBoundarylessFromOwner :
    ∃ G : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G ∧
        IsProperMap G := by
  -- The earlier Section 6.40 owner already has the precise weak Whitney boundaryless statement.
  simpa using (_root_.weak_whitney_embedding_boundaryless (M := M) (n := n))

/-- Helper for Theorem 6.19: package the range of a proper smooth embedding with its induced
manifold structure, subtype embedding, range diffeomorphism, and proper embeddedness. -/
theorem properlyEmbeddedRangePackageOfProperSmoothEmbedding
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G)
    (hproper : IsProperMap G) :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range G),
      ∃ hs : IsManifold (𝓡 n) ∞ (Set.range G),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range G) := cs
        let _ : IsManifold (𝓡 n) ∞ (Set.range G) := hs
        IsSmoothEmbedding
          (𝓡 n)
          (𝓡 (2 * n + 1))
          ∞
          (Subtype.val : Set.range G → EuclideanSpace ℝ (Fin (2 * n + 1))) ∧
            ∃ Φ : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ Set.range G,
              (∀ x, (Φ x : EuclideanSpace ℝ (Fin (2 * n + 1))) = G x) ∧
                (Set.range G).IsProperlyEmbedded := by
  -- Route correction: use the Corollary 6.16 owner package directly, then add proper
  -- embeddedness from the proper-map owner instead of keeping local copies of those theorems.
  obtain ⟨cs, hs, hSubtype, Φ, hΦ_apply⟩ :=
    _root_.smoothEmbeddingRangeData
      (J := 𝓡 n)
      (I := 𝓡 (2 * n + 1))
      (N := M)
      (M := EuclideanSpace ℝ (Fin (2 * n + 1)))
      (F := G)
      hG
  refine ⟨cs, hs, hSubtype, Φ, ?_⟩
  -- Properness of `G` turns the Euclidean range into a properly embedded closed subset.
  refine ⟨hΦ_apply, ?_⟩
  simpa using (_root_.rangeIsProperlyEmbeddedOfIsProperMap (F := G) hproper)

/-- Helper for Theorem 6.19: once a codimension-one candidate map is known to be a proper injective
immersion, Proposition 4.22 upgrades it to a smooth embedding. -/
theorem properInjectiveImmersionGivesSmoothEmbedding
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    {f : S → EuclideanSpace ℝ (Fin (2 * n))}
    (hf_inj : Function.Injective f)
    (hf_imm : IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ f)
    (hf_proper : IsProperMap f) :
    IsSmoothEmbedding
      (𝓡 n)
      (𝓡 (2 * n))
      ∞
      f := by
  -- A proper injective immersion is a smooth embedding by Proposition 4.22.
  simpa using
    (smooth_embedding_of_injective_isImmersion_isProperMap
      (I := 𝓡 n)
      (J := 𝓡 (2 * n))
      (M := S)
      (N := EuclideanSpace ℝ (Fin (2 * n)))
      (F := f)
      hf_inj
      hf_imm
      hf_proper)

/-- Helper for Theorem 6.19: a properly embedded boundaryless range carries a positive smooth
exhaustion function. -/
theorem existsPositiveSmoothExhaustionFunctionOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1)))) :
    ∃ f : C^∞⟮𝓡 n, S; ℝ⟯,
      (∀ x : S, 0 < f x) ∧
        (f : S → ℝ).IsExhaustionFunction := by
  let _ : TopologicalManifold n S := topologicalManifoldOfChartedSpace n S
  haveI : T2Space S := hSubtype.isEmbedding.t2Space
  haveI : SecondCountableTopology S := hSubtype.isEmbedding.secondCountableTopology
  letI : LocallyCompactSpace S :=
    TopologicalManifold.locallyCompactSpace_of_topologicalManifold n S
  haveI : SigmaCompactSpace S := sigmaCompactSpace_of_locallyCompact_secondCountable
  -- Proposition 2.28 now applies directly to the range manifold `S`.
  simpa using
    (exists_positive_smooth_exhaustion_function (I := 𝓡 n) (M := S))

/-- Helper for Theorem 6.19: the weak Whitney owner theorem can be reused directly on the properly
embedded range manifold. -/
theorem weakWhitneyEmbeddingBoundarylessOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1)))) :
    ∃ G : S → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G ∧
        IsProperMap G := by
  have hEmb :
      Topology.IsEmbedding (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))) :=
    hSubtype.isEmbedding
  let _ : TopologicalManifold n S := topologicalManifoldOfChartedSpace n S
  haveI : T2Space S := hEmb.t2Space
  haveI : SecondCountableTopology S := hEmb.secondCountableTopology
  -- The earlier Section 6.40 owner theorem applies to `S` once its topological-manifold data are
  -- reintroduced from the charted-space assumptions.
  simpa using (_root_.weak_whitney_embedding_boundaryless (M := S) (n := n))

/-- Helper for Theorem 6.19: view the ambient line `ℝ v` inside the Euclidean tangent space at
`G x`. -/
def ambientProjectionLineAt
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    {G : S → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (v : EuclideanSpace ℝ (Fin (2 * n + 1))) (x : S) :
    Submodule ℝ (TangentSpace (𝓡 (2 * n + 1)) (G x)) :=
  Submodule.span ℝ
    ({(show TangentSpace (𝓡 (2 * n + 1)) (G x) from v)} :
      Set (TangentSpace (𝓡 (2 * n + 1)) (G x)))

/-- Helper for Theorem 6.19: rewrite the kernel of the codimension-one projection as the line
`ℝ v`. -/
lemma projectionAlongLastHyperplaneCLM_ker_eq_span_singleton
    (v : EuclideanSpace ℝ (Fin (2 * n + 1)))
    (hv : v (Fin.last (2 * n)) ≠ 0) :
    LinearMap.ker (projectionAlongLastHyperplaneCLM (n := n) v).toLinearMap =
      Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) := by
  ext x
  constructor
  · intro hx
    -- The previously proved kernel computation identifies the kernel with the line `ℝ v`.
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_span_singleton]
    rcases (projectionAlongLastHyperplaneCLM_eq_zero_iff_smul (n := n) v hv).1 hx with ⟨a, ha⟩
    exact ⟨a, ha.symm⟩
  · intro hx
    -- Conversely, every vector on the line `ℝ v` is killed by the projection.
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_span_singleton] at hx
    rcases hx with ⟨a, ha⟩
    exact (projectionAlongLastHyperplaneCLM_eq_zero_iff_smul (n := n) v hv).2 ⟨a, ha.symm⟩

/-- Helper for Theorem 6.19: once a direction avoids both secants and tangent lines, the ambient
codimension-one projection is injective and immersive. -/
theorem projectionInjectiveImmersion_ofDirectionAvoidance
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    {G : S → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G)
    {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hv : v (Fin.last (2 * n)) ≠ 0)
    (hsecant :
      ∀ ⦃x y : S⦄, x ≠ y → ¬ ∃ a : ℝ, G y - G x = a • v)
    (htangent :
      ∀ x : S,
        Disjoint
          (LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x).toLinearMap)
          (ambientProjectionLineAt (n := n) (G := G) v x)) :
    Function.Injective (fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)) ∧
      IsImmersion
        (𝓡 n)
        (𝓡 (2 * n))
        ∞
        (fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)) := by
  let P : EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    projectionAlongLastHyperplaneCLM (n := n) v
  let F : S → EuclideanSpace ℝ (Fin (2 * n)) := fun x ↦ P (G x)
  constructor
  · intro x y hxy
    by_contra hne
    have hprojDiff : P (G y - G x) = 0 := by
      -- Equal projected values force the secant vector to lie in the kernel of the projection.
      have hsub : P (G y) - P (G x) = 0 := by
        simpa [F, P] using sub_eq_zero.mpr hxy.symm
      simpa [map_sub, P] using hsub
    rcases (projectionAlongLastHyperplaneCLM_eq_zero_iff_smul (n := n) v hv).1 hprojDiff with
      ⟨a, ha⟩
    exact hsecant hne ⟨a, ha⟩
  · have hGCont : ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ G := hG.isImmersion.contMDiff
    have hFCont : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ F := by
      -- The projected map is smooth because it is the composition of `G` with a continuous linear
      -- map.
      simpa [F, P, Function.comp] using P.contMDiff.comp hGCont
    have hGInj :
        ∀ x : S, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x) :=
      (Manifold.is_immersion_iff_forall_injective_mfderiv hGCont).1 hG.isImmersion
    -- It is enough to show that every projected derivative stays injective.
    refine (Manifold.is_immersion_iff_forall_injective_mfderiv hFCont).2 ?_
    intro x u w huw
    have hComp :
        mfderiv (𝓡 n) (𝓡 (2 * n)) F x = P.comp (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x) := by
      -- The chain rule identifies the derivative of the projected map.
      simpa [F, P, Function.comp] using
        (mfderiv_comp (x := x)
          (g := P)
          (f := G)
          (P.contMDiffAt.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0))
          (hGCont.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)))
    have hCompU :
        mfderiv (𝓡 n) (𝓡 (2 * n)) F x u =
          P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u) := by
      -- Evaluate the chain-rule identity on the first tangent vector.
      simpa [P] using congrArg (fun L ↦ L u) hComp
    have hCompW :
        mfderiv (𝓡 n) (𝓡 (2 * n)) F x w =
          P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) := by
      -- Evaluate the same identity on the second tangent vector.
      simpa [P] using congrArg (fun L ↦ L w) hComp
    have hKernelEq :
        P
          (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) = 0 := by
      -- Equality of projected derivative values forces the ambient derivative difference into the
      -- kernel of `P`.
      have hsub :
          mfderiv (𝓡 n) (𝓡 (2 * n)) F x u -
            mfderiv (𝓡 n) (𝓡 (2 * n)) F x w = 0 := by
        simp [huw]
      calc
        P
            (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
              mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) =
            P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u) -
              P (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w) := by
              exact
                P.map_sub
                  (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u)
                  (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w)
        _ = mfderiv (𝓡 n) (𝓡 (2 * n)) F x u -
              mfderiv (𝓡 n) (𝓡 (2 * n)) F x w := by
              rw [← hCompU, ← hCompW]
              rfl
        _ = 0 := hsub
    have hInKernel :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w ∈ LinearMap.ker P.toLinearMap := by
      -- The derivative difference lands in the kernel of the ambient projection.
      simpa [LinearMap.mem_ker] using hKernelEq
    have hInLineRaw :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w ∈
          Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))) := by
      -- The kernel formula turns the kernel membership into membership in the line `ℝ v`.
      rw [projectionAlongLastHyperplaneCLM_ker_eq_span_singleton (n := n) v hv] at hInKernel
      exact hInKernel
    have hInLine :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w ∈ ambientProjectionLineAt (n := n) (G := G) v x := by
      -- The same line is viewed in the tangent space using the standard Euclidean model.
      simpa [ambientProjectionLineAt] using hInLineRaw
    have hInRange :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w ∈
          LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x).toLinearMap := by
      -- Any derivative value lies in the range of that derivative.
      refine ⟨u - w, ?_⟩
      simp [map_sub]
    have hAmbientZeroSub :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x u -
            mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x w = 0 := by
      -- Tangent-line avoidance forces the overlap of the range and the ambient line to vanish.
      exact (Submodule.disjoint_def.mp (htangent x)) _ hInRange hInLine
    have hAmbientZero :
        mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x (u - w) = 0 := by
      -- Repackage the vanishing difference as vanishing on the tangent difference itself.
      simpa [map_sub] using hAmbientZeroSub
    have hDiffZero : u - w = 0 := by
      -- Injectivity of the original embedding derivative kills the tangent difference itself.
      apply hGInj x
      simpa using hAmbientZero
    exact sub_eq_zero.mp hDiffZero

/-- Helper for Theorem 6.19: once a proper embedding is known to stay inside a fixed tube around
an axis `a`, any oblique projection whose image of `a` is nonzero remains proper. -/
theorem projectionProper_ofLineTube
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    {G : S → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hGproper : IsProperMap G)
    {a : EuclideanSpace ℝ (Fin (2 * n + 1))} {R : ℝ}
    (hR : 0 < R)
    (hTube : ∀ x : S, ∃ t : ℝ, ‖G x - t • a‖ < R)
    {v : EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hprojAxis : projectionAlongLastHyperplaneCLM (n := n) v a ≠ 0) :
    IsProperMap
      (fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)) := by
  let P : EuclideanSpace ℝ (Fin (2 * n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * n)) :=
    projectionAlongLastHyperplaneCLM (n := n) v
  let F : S → EuclideanSpace ℝ (Fin (2 * n)) := fun x ↦ P (G x)
  have _ := hR
  have hFcont : Continuous F := P.continuous.comp hGproper.continuous
  refine isProperMap_iff_isCompact_preimage.2 ⟨hFcont, ?_⟩
  intro K hK
  obtain ⟨B, hBpos, hKbound⟩ := hK.isBounded.subset_closedBall_lt 0 0
  have hPa_pos : 0 < ‖P a‖ := norm_pos_iff.mpr hprojAxis
  let T : ℝ := (B + ‖P‖ * R) / ‖P a‖
  let C : ℝ := R + T * ‖a‖
  have hpreCompact : IsCompact (G ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) C) :=
    hGproper.isCompact_preimage (isCompact_closedBall 0 C)
  have hclosed : IsClosed (F ⁻¹' K) := hK.isClosed.preimage hFcont
  refine hpreCompact.of_isClosed_subset hclosed ?_
  intro x hxK
  have hFx_bound :
      ‖P (G x)‖ ≤ B := by
    have hmem : F x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (2 * n))) B := hKbound hxK
    simpa [F, Metric.mem_closedBall, dist_eq_norm] using hmem
  rcases hTube x with ⟨t, ht⟩
  have hG_split : (G x - t • a) + t • a = G x := by
    simp [sub_eq_add_neg, add_assoc]
  have hP_split : P (G x) = P (G x - t • a) + t • P a := by
    -- Rewrite the projected point as tube error plus axis component.
    have hP_split_aux :
        P ((G x - t • a) + t • a) = P (G x - t • a) + t • P a := by
      rw [map_add, map_smul]
    calc
      P (G x) = P ((G x - t • a) + t • a) := congrArg P hG_split.symm
      _ = P (G x - t • a) + t • P a := hP_split_aux
  have hP_error :
      ‖P (G x - t • a)‖ ≤ ‖P‖ * R := by
    -- The projection of the bounded tube error is uniformly bounded by the operator norm.
    calc
      ‖P (G x - t • a)‖ ≤ ‖P‖ * ‖G x - t • a‖ := P.le_opNorm _
      _ ≤ ‖P‖ * R := by
        exact mul_le_mul_of_nonneg_left (le_of_lt ht) (norm_nonneg _)
  have hAxis_component :
      ‖t • P a‖ ≤ B + ‖P‖ * R := by
    have htPa_eq : t • P a = P (G x) - P (G x - t • a) := by
      apply eq_sub_iff_add_eq.2
      simpa [add_comm] using hP_split
    rw [htPa_eq]
    exact (norm_sub_le _ _).trans (add_le_add hFx_bound hP_error)
  have hScalar_bound :
      ‖t‖ ≤ T := by
    refine (le_div_iff₀ hPa_pos).2 ?_
    simpa [T, norm_smul, mul_comm, mul_left_comm, mul_assoc] using hAxis_component
  have hAxis_norm :
      ‖t • a‖ ≤ T * ‖a‖ := by
    calc
      ‖t • a‖ = ‖t‖ * ‖a‖ := by rw [norm_smul]
      _ ≤ T * ‖a‖ := by
        exact mul_le_mul_of_nonneg_right hScalar_bound (norm_nonneg _)
  have hGx_bound :
      ‖G x‖ ≤ C := by
    -- The ambient point is the sum of the small tube error and a bounded axis component.
    have hnorm_split : ‖G x‖ = ‖(G x - t • a) + t • a‖ := by
      exact congrArg norm hG_split.symm
    calc
      ‖G x‖ = ‖(G x - t • a) + t • a‖ := hnorm_split
      _ ≤ ‖G x - t • a‖ + ‖t • a‖ := norm_add_le _ _
      _ ≤ R + T * ‖a‖ := by linarith [le_of_lt ht, hAxis_norm]
      _ = C := by rfl
  simpa [Metric.mem_closedBall, dist_eq_norm, C] using hGx_bound

/-- Helper for Theorem 6.19: isolate the remaining geometric existence theorem as production of a
proper weak embedding together with a direction whose codimension-one projection is already
proper and avoids the tangent and secant bad sets. -/
theorem existsGoodProjectionDataOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hn : 0 < n)
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))))
    (hProper : S.IsProperlyEmbedded) :
    ∃ G : S → EuclideanSpace ℝ (Fin (2 * n + 1)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G ∧
        IsProperMap G ∧
          ∃ v : EuclideanSpace ℝ (Fin (2 * n + 1)),
            v (Fin.last (2 * n)) ≠ 0 ∧
              (∀ ⦃x y : S⦄, x ≠ y → ¬ ∃ a : ℝ, G y - G x = a • v) ∧
                (∀ x : S,
                  Disjoint
                    (LinearMap.range (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) G x).toLinearMap)
                    (ambientProjectionLineAt (n := n) (G := G) v x)) ∧
                  IsProperMap
                    (fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)) := by
  -- Route correction: the old proof spine mixed a weak embedding, an arbitrary exhaustion
  -- function, and the codimension-one projection step. The remaining missing premise is now a
  -- single source-facing existence theorem for a good projection datum.
  have _ := hn
  have _ := hSubtype
  have _ := hProper
  -- TODO: thread the positive-dimension hypothesis through the geometric part of the
  -- codimension-one source route: first build a projection-ready normalization of the properly
  -- embedded range, then choose a direction avoiding both tangent and secant bad sets. The final
  -- properness step is now isolated in `projectionProper_ofLineTube`.
  sorry

/-- Helper for Theorem 6.19: isolate the remaining sharp premise as existence of a codimension-one
candidate map that is already known to be a proper injective immersion. -/
theorem existsProperInjectiveImmersionOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hn : 0 < n)
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))))
    (hProper : S.IsProperlyEmbedded) :
    ∃ f : S → EuclideanSpace ℝ (Fin (2 * n)),
      Function.Injective f ∧
        IsImmersion (𝓡 n) (𝓡 (2 * n)) ∞ f ∧
          IsProperMap f := by
  -- Route correction: consume the isolated good-projection datum instead of rebuilding the same
  -- weak-embedding-plus-exhaustion route inside this theorem.
  obtain ⟨G, hG, hGproper, v, hv, hsecant, htangent, hProjProper⟩ :=
    existsGoodProjectionDataOfProperlyEmbeddedRange
      (n := n)
      (S := S)
      hn
      hSubtype
      hProper
  let f : S → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun x ↦ projectionAlongLastHyperplaneCLM (n := n) v (G x)
  obtain ⟨hf_inj, hf_imm⟩ :=
    projectionInjectiveImmersion_ofDirectionAvoidance
      (n := n)
      (S := S)
      (G := G)
      hG
      hv
      hsecant
      htangent
  refine ⟨f, ?_, ?_, ?_⟩
  · -- The codimension-one projection is injective because the chosen direction avoids secants.
    simpa [f] using hf_inj
  · -- The same direction also avoids every tangent line, so the projection is an immersion.
    simpa [f] using hf_imm
  · -- Properness is part of the isolated good-projection datum.
    simpa [f] using hProjProper

/-- Helper for Theorem 6.19: isolate the sharp codimension-one geometric step on a properly
embedded boundaryless smooth submanifold of `ℝ^(2 * n + 1)`. -/
theorem existsCodimensionOneStrongStepOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hn : 0 < n)
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))))
    (hProper : S.IsProperlyEmbedded) :
    ∃ f : S → EuclideanSpace ℝ (Fin (2 * n)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ f := by
  -- Route correction: the closing step is now explicit. What remains is only the codimension-one
  -- production of a proper injective immersion.
  obtain ⟨f, hf_inj, hf_imm, hf_proper⟩ :=
    existsProperInjectiveImmersionOfProperlyEmbeddedRange
      (n := n)
      (S := S)
      hn
      hSubtype
      hProper
  refine ⟨f, ?_⟩
  -- Apply Proposition 4.22 through the isolated proper-injective-immersion interface.
  exact properInjectiveImmersionGivesSmoothEmbedding
    (n := n)
    (S := S)
    hf_inj
    hf_imm
    hf_proper

/-- Helper for Theorem 6.19: a properly embedded boundaryless smooth submanifold of `ℝ^(2 * n +
1)` admits a smooth embedding into `ℝ^(2 * n)`. -/
theorem existsStrongEmbeddingOfProperlyEmbeddedRange
    {S : Set (EuclideanSpace ℝ (Fin (2 * n + 1)))}
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
    [IsManifold (𝓡 n) ∞ S]
    (hn : 0 < n)
    (hSubtype :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 (2 * n + 1))
        ∞
        (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))))
    (hProper : S.IsProperlyEmbedded) :
    ∃ f : S → EuclideanSpace ℝ (Fin (2 * n)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ f := by
  -- Reduce the range-level theorem to the isolated codimension-one geometric helper.
  exact
    existsCodimensionOneStrongStepOfProperlyEmbeddedRange
      (n := n)
      (S := S)
      hn
      hSubtype
      hProper

/-- Helper for Theorem 6.19: once the strong theorem is proved on the properly embedded range,
transport it back to the original manifold through the range diffeomorphism. -/
theorem strongEmbeddingOfProperSmoothEmbedding
    {G : M → EuclideanSpace ℝ (Fin (2 * n + 1))}
    (hn : 0 < n)
    (hG : IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G)
    (hproper : IsProperMap G) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n)),
      IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ F := by
  -- First replace `M` by the properly embedded range carrying the induced manifold structure.
  obtain ⟨cs, hs, hSubtype, Φ, hΦ_apply, hRangeProper⟩ :=
    properlyEmbeddedRangePackageOfProperSmoothEmbedding hG hproper
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (Set.range G) := cs
  let _ : IsManifold (𝓡 n) ∞ (Set.range G) := hs
  have _ := hΦ_apply
  obtain ⟨f, hf⟩ := existsStrongEmbeddingOfProperlyEmbeddedRange hn hSubtype hRangeProper
  have hΦ :
      IsSmoothEmbedding
        (𝓡 n)
        (𝓡 n)
        ∞
        Φ := by
    -- A diffeomorphism is already a smooth embedding between the source and the range manifold.
    refine ⟨IsLocalDiffeomorph.isImmersion Φ.isLocalDiffeomorph, Φ.toHomeomorph.isEmbedding⟩
  refine ⟨f ∘ Φ, ?_⟩
  -- Compose the range embedding with the range diffeomorphism to return to the original manifold.
  simpa [Function.comp] using Manifold.IsSmoothEmbedding.comp hf hΦ

/-- Theorem 6.19 (Strong Whitney Embedding Theorem). If `n > 0`, every smooth `n`-manifold admits
a smooth embedding into `ℝ^(2n)`. -/
theorem strong_whitney_embedding (hn : 0 < n) :
    ∃ F : M → EuclideanSpace ℝ (Fin (2 * n)), IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n)) ∞ F :=
  by
    -- Route correction: reduce the theorem to the earlier weak Whitney embedding theorem and
    -- isolate the missing codimension-one geometric argument in a single range-level helper.
    have hWeak :
        ∃ G : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
          IsSmoothEmbedding (𝓡 n) (𝓡 (2 * n + 1)) ∞ G ∧
            IsProperMap G :=
      weakWhitneyEmbeddingBoundarylessFromOwner
    obtain ⟨G, hG, hproper⟩ := hWeak
    -- The remaining work is exactly the sharp strong-step theorem on the properly embedded range.
    exact strongEmbeddingOfProperSmoothEmbedding hn hG hproper

end

end Manifold
