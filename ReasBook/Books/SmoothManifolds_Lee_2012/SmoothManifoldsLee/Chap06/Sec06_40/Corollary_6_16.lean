import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Topology.Maps.Proper.Basic
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01.Definition_1_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Proposition_5_2

-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic recall note: `lean_leansearch` surfaced mathlib's smooth-embedding/proper-map owners
-- `Manifold.IsSmoothEmbedding` and `IsProperMap.isClosed_range`; the statement surface follows the
-- repo's Chapter 1/5 owners `TopologicalManifold`, `SmoothManifoldWithBoundary`,
-- `IsEmbeddedSubmanifold`, and `Set.IsProperlyEmbedded`.

open scoped Manifold ContDiff

noncomputable section

universe u

section Helpers

universe u𝕜 uE uH uM uE' uH' uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (∞ : ℕ∞ω) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable [IsManifold J (∞ : ℕ∞ω) N]

/-- Helper for Corollary 6.16: unpack Proposition 5.2 into explicit charted-space, manifold,
subtype-embedding, and diffeomorphism data on the range of a smooth embedding. -/
theorem smoothEmbeddingRangeData {F : N → M}
    (hF : Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) F) :
    ∃ cs : ChartedSpace H' (Set.range F),
      ∃ hs : IsManifold J (∞ : ℕ∞ω) (Set.range F),
        let _ : ChartedSpace H' (Set.range F) := cs
        let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := hs
        Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : Set.range F → M) ∧
          ∃ Φ : N ≃ₘ⟮J, J⟯ Set.range F, ∀ x, (Φ x : M) = F x := by
  -- Proposition 5.2 already constructs the induced range structure, so only its existential
  -- packaging needs to be normalized to the tuple used below.
  rcases smooth_embedding_range_has_induced_manifold_structure hF with ⟨cs, hcs⟩
  have hRange :
      ∃ hs : IsManifold J (∞ : ℕ∞ω) (Set.range F),
        let _ : ChartedSpace H' (Set.range F) := cs
        let _ : IsManifold J (∞ : ℕ∞ω) (Set.range F) := hs
        Manifold.IsSmoothEmbedding J I (∞ : ℕ∞ω) (Subtype.val : Set.range F → M) ∧
          ∃ Φ : N ≃ₘ⟮J, J⟯ Set.range F, ∀ x, (Φ x : M) = F x := by
    -- The opaque induced-image predicate unfolds exactly to the concrete range data.
    simpa [IsInducedImageManifoldStructure] using hcs
  rcases hRange with ⟨hs, hSubtype, Φ, hΦ⟩
  exact ⟨cs, hs, hSubtype, Φ, hΦ⟩

/-- Helper for Corollary 6.16: the range of a proper map into a Hausdorff space is properly
embedded because proper maps have closed range. -/
theorem rangeIsProperlyEmbeddedOfIsProperMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y] {F : X → Y}
    (hF : IsProperMap F) : (Set.range F).IsProperlyEmbedded := by
  -- Closed subsets are properly embedded in the chapter's source-facing sense.
  exact hF.isClosed_range.isProperlyEmbedded

section BoundaryPackaging

variable {n : ℕ} {S : Type u} [TopologicalSpace S] [ChartedSpace (ℍ^{n}) S]

/-- Helper for Corollary 6.16: an `∞`-smooth Lee boundary atlas supplies the `C^0` manifold data
required by `TopologicalManifoldWithBoundary`. -/
theorem isManifoldBoundaryZeroOfTop
    (hs : IsManifold (leeBoundaryModelWithCorners n) ω S) :
    IsManifold (leeBoundaryModelWithCorners n) 0 S := by
  -- The owner `TopologicalManifoldWithBoundary` only needs the downgraded `C^0` manifold
  -- structure, which follows from monotonicity in differentiability order.
  let _ : IsManifold (leeBoundaryModelWithCorners n) ω S := hs
  infer_instance

/-- Helper for Corollary 6.16: package charted-space and smooth Lee-boundary manifold data into
the chapter's `SmoothManifoldWithBoundary` owner. -/
@[reducible] noncomputable def smoothManifoldWithBoundaryOfChartedSpaceIsManifold
    [T2Space S] [SecondCountableTopology S]
    (hs : IsManifold (leeBoundaryModelWithCorners n) ω S) :
    SmoothManifoldWithBoundary n S :=
  { toTopologicalManifoldWithBoundary :=
      { toT2Space := inferInstance
        toSecondCountableTopology := inferInstance
        toChartedSpace := inferInstance
        toIsManifold := isManifoldBoundaryZeroOfTop hs }
    smooth := hs }

end BoundaryPackaging

section EmbeddedPackaging

variable {n m : ℕ}
variable {S : Set (EuclideanSpace ℝ (Fin m))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) S]
variable [IsManifold (𝓡 n) ω S]

/-- Helper for Corollary 6.16: once the range subtype carries the induced boundaryless manifold
structure and its inclusion is a smooth embedding, it is an embedded submanifold. -/
theorem embeddedSubmanifoldOfSubtypeEmbedding
    (hSubtype : Manifold.IsSmoothEmbedding (𝓡 n) (𝓡 m) ω
      (Subtype.val : S → EuclideanSpace ℝ (Fin m))) :
    IsEmbeddedSubmanifold (𝓡 m) (𝓡 n) S := by
  -- The only extra data in `IsEmbeddedSubmanifold` is boundarylessness of the source, and that is
  -- inherited automatically from the Euclidean model.
  have _ : IsManifold (𝓡 n) ω S := inferInstance
  exact
    { toBoundarylessManifold := inferInstance
      isSmoothEmbedding_subtype_val := by
        simpa using hSubtype }

end EmbeddedPackaging

end Helpers

section

variable {n : ℕ}
variable {M : Type u} [TopologicalSpace M]

/-- Boundaryless companion to Corollary 6.16: every smooth boundaryless `n`-manifold is
diffeomorphic to a properly embedded boundaryless smooth submanifold of `ℝ^(2 * n + 1)`. -/
theorem exists_diffeomorph_boundaryless_properly_embedded_submanifold_euclidean
    [TopologicalManifold n M]
    [IsManifold (𝓡 n) ∞ M] :
    ∃ S : Set (EuclideanSpace ℝ (Fin (2 * n + 1))),
      ∃ instTopological : TopologicalManifold n S,
        ∃ instManifold : IsManifold (𝓡 n) ∞ S,
          let _ : TopologicalManifold n S := instTopological
          let _ : IsManifold (𝓡 n) ∞ S := instManifold
          ∃ Φ : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ S,
            Manifold.IsSmoothEmbedding
                (𝓡 n)
                (𝓡 (2 * n + 1))
                ∞
                (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))) ∧
              S.IsProperlyEmbedded := sorry

/-- Corollary 6.16: every smooth `n`-dimensional manifold with or without boundary is
diffeomorphic to a properly embedded submanifold with or without boundary of
`ℝ^(2 * n + 1)`. -/
theorem exists_diffeomorph_properly_embedded_submanifold_with_boundary_euclidean
    [SmoothManifoldWithBoundary n M] :
    ∃ S : Set (EuclideanSpace ℝ (Fin (2 * n + 1))),
      ∃ instSmooth : SmoothManifoldWithBoundary n S,
          let _ : SmoothManifoldWithBoundary n S := instSmooth
        ∃ Φ : M ≃ₘ⟮leeBoundaryModelWithCorners n, leeBoundaryModelWithCorners n⟯ S,
          Manifold.IsSmoothEmbedding
              (leeBoundaryModelWithCorners n)
              (𝓡 (2 * n + 1))
              ∞
              (Subtype.val : S → EuclideanSpace ℝ (Fin (2 * n + 1))) ∧
            S.IsProperlyEmbedded := sorry

end
