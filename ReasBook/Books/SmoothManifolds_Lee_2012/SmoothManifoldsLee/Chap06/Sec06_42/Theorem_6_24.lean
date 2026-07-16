import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap06.Sec06_42.Definition_6_42_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open Manifold
open NormalBundle
open scoped ContDiff Manifold

section TubularNeighborhoodTheorem

variable {n m : ℕ}
variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M]

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the zero tangent vector belongs to every normal fiber. -/
theorem zero_mem_normalSpace (x : M) :
    (0 : TangentSpace (𝓡 n) (x : EuclideanSpace ℝ (Fin n))) ∈ N[n, m; M; x] := by
  -- The normal space is a linear subspace, so it contains the zero vector.
  exact Submodule.zero_mem _

/-- Helper for Theorem 6.24: the zero section of the normal bundle at `x`. -/
noncomputable def zeroNormalPoint (x : M) : NM[n, m; M] :=
  ⟨x, ⟨0, zero_mem_normalSpace x⟩⟩

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the endpoint map restricts to the identity on the zero section. -/
@[simp] theorem endpointMap_zeroNormalPoint (x : M) :
    NormalBundle.endpointMap n m M (zeroNormalPoint x) =
      (x : EuclideanSpace ℝ (Fin n)) := by
  -- On the zero section, the normal contribution vanishes and only the base point remains.
  change (x : EuclideanSpace ℝ (Fin n)) +
      (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))) 0 =
    (x : EuclideanSpace ℝ (Fin n))
  rw [map_zero, add_zero]

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: a positive radius function contains the zero section in the
corresponding radius slice. -/
theorem zeroNormalPoint_mem_radiusSlice
    (δ : M → ℝ) (hδ : ∀ x : M, 0 < δ x) (x : M) :
    zeroNormalPoint x ∈ NormalBundle.radiusSlice n m M δ := by
  -- The zero section has fiber norm `0`, so positivity of `δ` gives the defining inequality.
  change ‖(NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))) 0‖ < δ x
  rw [map_zero, norm_zero]
  exact hδ x

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: enlarging the radius function enlarges the corresponding radius
slice. -/
theorem radiusSlice_mono {δ₁ δ₂ : M → ℝ}
    (hδ : ∀ x : M, δ₁ x ≤ δ₂ x) :
    NormalBundle.radiusSlice n m M δ₁ ⊆ NormalBundle.radiusSlice n m M δ₂ := by
  intro p hp
  -- Rewrite both radius slices by their defining inequalities and compare the radii pointwise.
  rw [NormalBundle.mem_radiusSlice_iff] at hp ⊢
  exact lt_of_lt_of_le hp (hδ p.proj)

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: equal endpoint values force the base-point difference to equal the
corresponding difference of normal vectors. -/
theorem base_sub_eq_vector_sub_of_endpointMap_eq
    (p q : NM[n, m; M])
    (h : NormalBundle.endpointMap n m M p = NormalBundle.endpointMap n m M q) :
    ((p.proj : EuclideanSpace ℝ (Fin n)) - q.proj) =
      normal_bundle_vector n m M q - normal_bundle_vector n m M p := by
  -- Subtract the same base point and normal vector from both sides of the endpoint equality.
  have h' :
      (p.proj : EuclideanSpace ℝ (Fin n)) + normal_bundle_vector n m M p =
        (q.proj : EuclideanSpace ℝ (Fin n)) + normal_bundle_vector n m M q := by
    simpa [NormalBundle.endpointMap] using h
  have hShift :=
    congrArg
      (fun z : EuclideanSpace ℝ (Fin n) ↦
        z - (q.proj : EuclideanSpace ℝ (Fin n)) - normal_bundle_vector n m M p)
      h'
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: if two normal vectors have the same endpoint, then the norm of the
base-point difference equals the norm of the difference of their normal components. -/
theorem norm_base_sub_eq_norm_vector_sub_of_endpointMap_eq
    (p q : NM[n, m; M])
    (h : NormalBundle.endpointMap n m M p = NormalBundle.endpointMap n m M q) :
    ‖((p.proj : EuclideanSpace ℝ (Fin n)) - q.proj)‖ =
      ‖normal_bundle_vector n m M q - normal_bundle_vector n m M p‖ := by
  -- Rewrite the base-point difference using the previous endpoint-equality identity.
  rw [base_sub_eq_vector_sub_of_endpointMap_eq (n := n) (m := m) (M := M) p q h]

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the tautological inclusion of the normal bundle into the ambient
tangent bundle is injective because a total-space point is determined by its base point and fiber
vector. -/
theorem normalBundleInclusion_injective :
    Function.Injective (normal_bundle_inclusion n m M) := by
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

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the normal bundle topology is induced from the tautological inclusion
into the ambient tangent bundle, so that inclusion is a topological embedding. -/
theorem normalBundleInclusion_isEmbedding :
    Topology.IsEmbedding (normal_bundle_inclusion n m M) :=
  (normalBundleInclusion_injective (n := n) (m := m) (M := M)).isEmbedding_induced

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the explicit product coordinates on the normal bundle remember both
the base point and the normal vector, so they are injective. -/
theorem normalBundleToProd_injective :
    Function.Injective (normal_bundle_toProd n m M) := by
  intro v w h
  rcases v with ⟨x, vx⟩
  rcases w with ⟨y, vy⟩
  -- The first product coordinate already determines the base point.
  dsimp [normal_bundle_toProd, normal_bundle_vector] at h ⊢
  have hxy_val : (x : EuclideanSpace ℝ (Fin n)) = y := by
    exact congrArg Prod.fst h
  have hxy : x = y := Subtype.ext hxy_val
  -- After identifying the base point, the second coordinate determines the fiber vector.
  cases hxy
  have hvy : vx = vy := by
    apply Subtype.ext
    apply (NormedSpace.fromTangentSpace ((x : M) : EuclideanSpace ℝ (Fin n))).injective
    exact congrArg Prod.snd h
  cases hvy
  rfl

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: in Euclidean space, the tangent bundle trivialization from
mathlib sends the tautological normal-bundle inclusion to the explicit product-coordinate map. -/
theorem tangentBundleToProd_comp_normalBundleInclusion :
    (tangentBundleModelSpaceHomeomorph (𝓡 n) :
        TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∘
      normal_bundle_inclusion n m M =
    normal_bundle_toProd n m M := by
  -- In model-space tangent coordinates, the bundle point is literally `(x, v)`.
  funext v
  rcases v with ⟨x, vx⟩
  simp [tangentBundleModelSpaceHomeomorph_coe, normal_bundle_inclusion, normal_bundle_toProd,
    normal_bundle_vector, NormedSpace.fromTangentSpace]

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the explicit product-coordinate map on the normal bundle is a
topological embedding because it is the tautological inclusion followed by the Euclidean
tangent-bundle trivialization. -/
theorem normalBundleToProd_isEmbedding :
    Topology.IsEmbedding (normal_bundle_toProd n m M) := by
  -- Rewrite the coordinate map as a composition of the normal-bundle inclusion with a homeomorph.
  rw [← tangentBundleToProd_comp_normalBundleInclusion (n := n) (m := m) (M := M)]
  exact
    (tangentBundleModelSpaceHomeomorph (𝓡 n)).isEmbedding.comp
      (normalBundleInclusion_isEmbedding (n := n) (m := m) (M := M))

/-- Helper for Theorem 6.24: the normal bundle is canonically homeomorphic to the range of its
explicit product-coordinate map. -/
noncomputable def normalBundleToProd_rangeHomeomorph :
    NM[n, m; M] ≃ₜ Set.range (normal_bundle_toProd n m M) :=
  (normalBundleToProd_isEmbedding (n := n) (m := m) (M := M)).toHomeomorph

/-- Helper for Theorem 6.24: pack a pair of Euclidean vectors into the single ambient space
`ℝ^(N + m)` by writing the left block first and the right block second. -/
noncomputable def packEuclideanPair (N m : ℕ) :
    EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) →
      EuclideanSpace ℝ (Fin (N + m)) :=
  fun p ↦ (EuclideanSpace.equiv (Fin (N + m)) ℝ).symm (Fin.append p.1 p.2)

/-- Helper for Theorem 6.24: unpack the first and last Euclidean coordinate blocks from
`ℝ^(N + m)`. -/
noncomputable def unpackEuclideanPair (N m : ℕ) :
    EuclideanSpace ℝ (Fin (N + m)) →
      EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m) :=
  fun z ↦
    ((EuclideanSpace.equiv (Fin N) ℝ).symm fun i ↦ z (Fin.castAdd m i),
      (EuclideanSpace.equiv (Fin m) ℝ).symm fun i ↦ z (Fin.natAdd N i))

/-- Helper for Theorem 6.24: packing Euclidean coordinate pairs is continuous because it is a
linear map between finite-dimensional spaces. -/
theorem continuous_packEuclideanPair (N m : ℕ) :
    Continuous (packEuclideanPair N m) := by
  -- Pass to function coordinates and use continuity of the assembled finite tuple.
  refine ((EuclideanSpace.equiv (Fin (N + m)) ℝ).symm.toHomeomorph.continuous_toFun).comp ?_
  fun_prop

/-- Helper for Theorem 6.24: unpacking Euclidean coordinate pairs is continuous for the same
finite-dimensional linear-algebra reason. -/
theorem continuous_unpackEuclideanPair (N m : ℕ) :
    Continuous (unpackEuclideanPair N m) := by
  -- Each coordinate block is continuous after passing through the Euclidean/function homeomorph.
  apply Continuous.prodMk
  · exact ((EuclideanSpace.equiv (Fin N) ℝ).symm.toHomeomorph.continuous_toFun).comp (by fun_prop)
  · exact ((EuclideanSpace.equiv (Fin m) ℝ).symm.toHomeomorph.continuous_toFun).comp (by fun_prop)

/-- Helper for Theorem 6.24: unpacking after packing recovers the original pair of Euclidean
coordinates. -/
theorem unpackEuclideanPair_packEuclideanPair
    {N m : ℕ}
    (p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin m)) :
    unpackEuclideanPair N m (packEuclideanPair N m p) = p := by
  -- Check the two Euclidean coordinate blocks separately.
  ext i <;>
    simp [unpackEuclideanPair, packEuclideanPair]

/-- Helper for Theorem 6.24: packing Euclidean coordinate pairs is a topological embedding,
because unpacking is a continuous left inverse. -/
theorem packEuclideanPair_isEmbedding (N m : ℕ) :
    Topology.IsEmbedding (packEuclideanPair N m) := by
  have hLeft :
      Function.LeftInverse (unpackEuclideanPair N m) (packEuclideanPair N m) := by
    intro p
    exact unpackEuclideanPair_packEuclideanPair p
  -- The continuous left inverse upgrades the injective coordinate packing to an embedding.
  exact (hLeft.isClosedEmbedding
    (continuous_unpackEuclideanPair N m)
    (continuous_packEuclideanPair N m)).isEmbedding

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: pack the product coordinates of the normal bundle into the single
Euclidean ambient `ℝ^(n + n)`. -/
noncomputable abbrev packedNormalBundleToEuclidean :
    NM[n, m; M] → EuclideanSpace ℝ (Fin (n + n)) :=
  fun p ↦ packEuclideanPair n n (normal_bundle_toProd n m M p)

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: truncating the packed coordinates recovers the base point of the
normal-bundle vector. -/
theorem truncateTailCoordinates_packedNormalBundleToEuclidean
    (p : NM[n, m; M]) :
    (unpackEuclideanPair n n
        (packedNormalBundleToEuclidean (n := n) (m := m) (M := M) p)).1 =
      (p.proj : EuclideanSpace ℝ (Fin n)) := by
  -- Unpacking the first coordinate block returns the base point.
  simpa [packedNormalBundleToEuclidean, normal_bundle_toProd] using
    congrArg Prod.fst
      (unpackEuclideanPair_packEuclideanPair
        (N := n)
        (m := n)
        (p := normal_bundle_toProd n m M p))

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the packed Euclidean coordinates still determine a normal-bundle
point uniquely. -/
theorem packedNormalBundleToEuclidean_injective :
    Function.Injective (packedNormalBundleToEuclidean (n := n) (m := m) (M := M)) := by
  intro p q hpq
  -- Unpack the ambient coordinates first, then use injectivity of the product-coordinate model.
  have hUnpacked :
      unpackEuclideanPair n n
          (packedNormalBundleToEuclidean (n := n) (m := m) (M := M) p) =
        unpackEuclideanPair n n
          (packedNormalBundleToEuclidean (n := n) (m := m) (M := M) q) :=
    congrArg (unpackEuclideanPair n n) hpq
  have hProd :
      normal_bundle_toProd n m M p = normal_bundle_toProd n m M q := by
    simpa [packedNormalBundleToEuclidean, unpackEuclideanPair_packEuclideanPair] using hUnpacked
  exact (normalBundleToProd_injective (n := n) (m := m) (M := M)) hProd

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the packed Euclidean coordinate map is a topological embedding,
because it is the product-coordinate embedding followed by a linear homeomorphism. -/
theorem packedNormalBundleToEuclidean_isEmbedding :
    Topology.IsEmbedding (packedNormalBundleToEuclidean (n := n) (m := m) (M := M)) := by
  -- Route correction: switch to the packed ambient `ℝ^(n + n)` so the remaining local-slice
  -- theorem lives in the Chapter 5 single-Euclidean-space API.
  simpa [packedNormalBundleToEuclidean, Function.comp] using
    (packEuclideanPair_isEmbedding n n).comp
      (normalBundleToProd_isEmbedding (n := n) (m := m) (M := M))

/-- Helper for Theorem 6.24: the normal bundle is canonically homeomorphic to the range of its
packed Euclidean coordinate map. -/
noncomputable def packedNormalBundleToEuclidean_rangeHomeomorph :
    NM[n, m; M] ≃ₜ
      Set.range (packedNormalBundleToEuclidean (n := n) (m := m) (M := M)) :=
  (packedNormalBundleToEuclidean_isEmbedding (n := n) (m := m) (M := M)).toHomeomorph

omit [IsManifold (𝓡 m) ∞ M] [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M] in
/-- Helper for Theorem 6.24: the zero section is sent to the packed point `(x, 0)` in the ambient
Euclidean coordinates. -/
@[simp] theorem packedNormalBundleToEuclidean_zeroNormalPoint (x : M) :
    packedNormalBundleToEuclidean (n := n) (m := m) (M := M) (zeroNormalPoint x) =
      packEuclideanPair n n
        ((x : EuclideanSpace ℝ (Fin n)), 0) := by
  -- On the zero section the second product coordinate is the zero vector.
  change
    packEuclideanPair n n
        ((x : EuclideanSpace ℝ (Fin n)),
          (NormedSpace.fromTangentSpace (x : EuclideanSpace ℝ (Fin n))) 0) =
      packEuclideanPair n n ((x : EuclideanSpace ℝ (Fin n)), 0)
  rw [map_zero]

/-
Domain sampling pass: the target belongs to the embedded-submanifold / normal-bundle domain.
Relevant owner declarations checked before refinement:
* `NM[n, m; M]` from `Definition_6_42_extra_1`,
* `Bundle.TotalSpace.proj`,
* `TubularNeighborhood n m M` and its field `TubularNeighborhood.contains_base`
  from `Definition_6_42_extra_2`.
Source/core/bridge triage:
* source-facing item: this theorem is the textbook existence statement for a tubular neighborhood;
* core/canonical owner: `TubularNeighborhood n m M`;
* bridge/view data: the smooth structure on `NM[n, m; M]` must be supplied explicitly here,
  because this chapter proves its existence but does not install canonical instances globally.
-/
-- Semantic recall note: `lean_leansearch` did not reveal an upstream tubular-neighborhood
-- existence theorem for this embedded-submanifold setup, so the local owner remains
-- `NormalBundle.TubularNeighborhood n m M`.
/-- Theorem 6.24 (Tubular Neighborhood Theorem): every embedded submanifold of `ℝ^n` has a
tubular neighborhood. The theorem exposes the auxiliary smooth structure on `NM[n, m; M]`
and an actual tubular-neighborhood object. -/
theorem embedded_submanifold_has_tubular_neighborhood :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]),
      letI := cs
      ∃ hs : IsManifold (𝓡 n) ∞ (NM[n, m; M]),
        letI := hs
        ∃ T : NormalBundle.TubularNeighborhood n m M,
          M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) := by
  -- Route correction: package the auxiliary `NM[n, m; M]` structure through local instances
  -- before quantifying the tubular neighborhood, instead of partially applying the owner.
  have hToProdEmbedding :
      Topology.IsEmbedding (normal_bundle_toProd n m M) :=
    normalBundleToProd_isEmbedding (n := n) (m := m) (M := M)
  have hToProdHomeomorph :
      NM[n, m; M] ≃ₜ Set.range (normal_bundle_toProd n m M) :=
    normalBundleToProd_rangeHomeomorph (n := n) (m := m) (M := M)
  let P : NM[n, m; M] → EuclideanSpace ℝ (Fin (n + n)) :=
    packedNormalBundleToEuclidean (n := n) (m := m) (M := M)
  have hPackedEmbedding : Topology.IsEmbedding P := by
    -- The packed coordinates are the intended ambient model for the remaining local-slice step.
    simpa [P] using packedNormalBundleToEuclidean_isEmbedding (n := n) (m := m) (M := M)
  have hPackedHomeomorph : NM[n, m; M] ≃ₜ Set.range P := by
    -- The induced-range transport is now stated in the single Euclidean ambient `ℝ^(n + n)`.
    simpa [P] using packedNormalBundleToEuclidean_rangeHomeomorph (n := n) (m := m) (M := M)
  -- The verified frontier now reaches the packed-range transport interface.
  -- TODO: prove that `Set.range P` satisfies the local `n`-slice condition in `ℝ^(n + n)`,
  -- use Chapter 5 to put the induced smooth structure on that packed range, transport it back
  -- along `hPackedHomeomorph`, and then reuse the same packed local normal form to prove the
  -- endpoint map is locally a diffeomorphism at the zero section before the half-radius argument.
  let _ := hToProdEmbedding
  let _ := hToProdHomeomorph
  let _ := hPackedEmbedding
  let _ := hPackedHomeomorph
  sorry

end TubularNeighborhoodTheorem
