import SmoothManifolds_Lee_2012.Chap03.Sec03_16.Proposition_3_20
import SmoothManifolds_Lee_2012.Chap05.Sec05_29.Theorem_5_8
import SmoothManifolds_Lee_2012.Chap06.Sec06_42.Definition_6_42_extra_2

open Manifold
open scoped ContDiff Manifold NormalBundle RealInnerProductSpace

noncomputable section

section EmbeddedNormalBundle

variable (n m : ℕ)
variable (S : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]
variable [IsManifold (𝓡 m) (∞ : ℕ∞ω) S]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S]

omit [IsManifold (𝓡 m) ∞ S] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S] in
/-- Helper for Theorem 6.23: the tautological inclusion of the normal bundle into the ambient
tangent bundle is injective because a total-space point is determined by its base point and fiber
vector. -/
theorem normalBundleInclusion_injective :
    Function.Injective (normal_bundle_inclusion n m S) := by
  intro v w h
  rcases v with ⟨x, vx⟩
  rcases w with ⟨y, vy⟩
  -- Compare the base points first through the bundle projection.
  have hxy_val : (x : EuclideanSpace ℝ (Fin n)) = y := by
    simpa [normal_bundle_inclusion] using congrArg Bundle.TotalSpace.proj h
  have hxy : x = y := Subtype.ext hxy_val
  -- Once the base points agree, the tangent-bundle equality is exactly the fiber equality.
  cases hxy
  simpa [normal_bundle_inclusion] using h

omit [IsManifold (𝓡 m) ∞ S] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S] in
/-- Helper for Theorem 6.23: the chosen topology on the normal bundle is the topology induced by
its tautological inclusion into the ambient tangent bundle, so that inclusion is a topological
embedding. -/
theorem normalBundleInclusion_isEmbedding :
    Topology.IsEmbedding (normal_bundle_inclusion n m S) :=
  (normalBundleInclusion_injective (n := n) (m := m) (S := S)).isEmbedding_induced

omit [IsManifold (𝓡 m) ∞ S] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S] in
/-- Helper for Theorem 6.23: the normal-bundle product coordinates remember both the base point and
the ambient tangent vector, so they are injective on the total space. -/
theorem normalBundleToProd_injective :
    Function.Injective (normal_bundle_toProd n m S) := by
  intro v w h
  rcases v with ⟨x, vx⟩
  rcases w with ⟨y, vy⟩
  -- The product coordinates determine the base point from the first component.
  dsimp [normal_bundle_toProd, normal_bundle_vector] at h ⊢
  have hxy_val : (x : EuclideanSpace ℝ (Fin n)) = y := by
    exact congrArg Prod.fst h
  have hxy : x = y := Subtype.ext hxy_val
  -- After identifying the base point, the second component determines the fiber vector.
  cases hxy
  have hvy : vx = vy := by
    apply Subtype.ext
    apply (NormedSpace.fromTangentSpace ((x : S) : EuclideanSpace ℝ (Fin n))).injective
    exact congrArg Prod.snd h
  cases hvy
  rfl

/-- Helper for Theorem 6.23: the normal bundle is canonically homeomorphic to the range of its
tautological inclusion in the ambient tangent bundle. -/
noncomputable def normalBundleInclusion_rangeHomeomorph :
    NM[n, m; S] ≃ₜ Set.range (normal_bundle_inclusion n m S) :=
  (normalBundleInclusion_isEmbedding (n := n) (m := m) (S := S)).toHomeomorph

/-- Helper for Theorem 6.23: Euclidean space has a global chart, so its tangent bundle is
canonically diffeomorphic to `ℝ^n × ℝ^n`. -/
noncomputable def euclideanTangentBundleToProd :
    TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) ≃ₘ⟮(𝓡 n).tangent, (𝓡 n).prod (𝓡 n)⟯
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := by
  -- On the model space, the tangent bundle is canonically the product of the base with the model
  -- vector space.
  let Φ :=
    tangentBundleModelSpaceDiffeomorph (I := 𝓡 n) (n := (∞ : ℕ∞))
  simpa [ModelProd] using Φ

/-- Helper for Theorem 6.23: the Euclidean tangent-bundle/product diffeomorphism sends the
tautological normal-bundle inclusion to the explicit product-coordinate map. -/
theorem euclideanTangentBundleToProd_comp_normalBundleInclusion :
    (euclideanTangentBundleToProd (n := n) :
        TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∘
      normal_bundle_inclusion n m S =
    normal_bundle_toProd n m S := by
  -- On the Euclidean model space, the tangent-bundle diffeomorphism is definitionally the
  -- canonical product identification `(x, v)`.
  funext v
  simpa [euclideanTangentBundleToProd, ModelProd, normal_bundle_inclusion, normal_bundle_toProd,
    normal_bundle_vector] using rfl

/-- Helper for Theorem 6.23: the explicit product-coordinate map on the normal bundle is a
topological embedding because it is the tautological inclusion followed by the ambient Euclidean
tangent-bundle/product homeomorphism. -/
theorem normalBundleToProd_isEmbedding :
    Topology.IsEmbedding (normal_bundle_toProd n m S) := by
  -- Rewrite the coordinate map as a composition of two known embeddings.
  rw [← euclideanTangentBundleToProd_comp_normalBundleInclusion (n := n) (m := m) (S := S)]
  exact (euclideanTangentBundleToProd (n := n)).toHomeomorph.isEmbedding.comp
    (normalBundleInclusion_isEmbedding (n := n) (m := m) (S := S))

/-- Helper for Theorem 6.23: the normal bundle is canonically homeomorphic to the range of its
explicit product-coordinate map. -/
noncomputable def normalBundleToProd_rangeHomeomorph :
    NM[n, m; S] ≃ₜ Set.range (normal_bundle_toProd n m S) :=
  (normalBundleToProd_isEmbedding (n := n) (m := m) (S := S)).toHomeomorph

/-- Theorem 6.23: if `S ⊆ ℝ^n` is an embedded `m`-dimensional submanifold, then its normal bundle
is an embedded `n`-dimensional submanifold of the ambient tangent bundle `Tℝ^n ≃ ℝ^n × ℝ^n`. -/
theorem normalBundle_exists_isSmoothEmbedding :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; S]),
      letI := cs
      ∃ hs : IsManifold (𝓡 n) (∞ : ℕ∞ω) (NM[n, m; S]),
        letI := hs
        IsSmoothEmbedding (𝓡 n) (𝓡 n).tangent (∞ : ℕ∞ω)
          (normal_bundle_inclusion n m S) := by
  -- The verified frontier is the range/topology transport interface:
  -- `normal_bundle_inclusion` and `normal_bundle_toProd` are injective, and the normal bundle is
  -- already homeomorphic to the range of its inclusion in the ambient tangent bundle.
  -- TODO: prove that `Set.range (normal_bundle_toProd n m S)` satisfies the local `n`-slice
  -- condition in `ℝ^n × ℝ^n`, use the Chapter 5 range-construction theorem there, and transport
  -- the resulting charted/manifold structure back along `normalBundleInclusion_rangeHomeomorph`.
  sorry

end EmbeddedNormalBundle
