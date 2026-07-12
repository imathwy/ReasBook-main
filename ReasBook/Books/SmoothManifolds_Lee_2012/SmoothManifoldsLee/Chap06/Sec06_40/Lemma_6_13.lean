import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Semantic recall note: the dedicated `lean_leansearch` tool was unavailable in this runner, so
-- the statement surface was matched against the repository's Euclidean embedded-submanifold
-- statements and mathlib's `Manifold.IsSmoothEmbedding` / `Manifold.IsImmersion` APIs.

universe uE uH

/-- The last coordinate index of `Fin N`, defined under the positivity hypothesis `0 < N`. -/
private def lastCoordinateIndex {N : ℕ} (hN : 0 < N) : Fin N :=
  ⟨N - 1, Nat.sub_lt hN (Nat.succ_pos 0)⟩

/-- The order-preserving embedding of the first `N - 1` coordinates into `Fin N`. -/
private def dropLastCoordinateEmbedding {N : ℕ} (hN : 0 < N) :
    Fin (N - 1) → Fin N :=
  fun i ↦ ⟨i.1, lt_trans i.2 (Nat.sub_lt hN (Nat.succ_pos 0))⟩

/-- The oblique projection from `ℝ^N` onto the last-coordinate-zero hyperplane, written in
`Fin`-coordinates and taken along the line spanned by `v`. For vectors `v` with nonzero last
coordinate, this is the projection whose kernel is `ℝ v`. -/
def obliqueProjectionToLastHyperplane {N : ℕ} (hN : 0 < N)
    (v : EuclideanSpace ℝ (Fin N)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin (N - 1)) :=
  fun x ↦
    (EuclideanSpace.equiv (Fin (N - 1)) ℝ).symm fun i ↦
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i)

/-- The oblique projection along `v` is given coordinatewise by subtracting the unique multiple of
`v` that kills the last coordinate. -/
theorem obliqueProjectionToLastHyperplane_apply {N : ℕ} (hN : 0 < N)
    (v x : EuclideanSpace ℝ (Fin N)) (i : Fin (N - 1)) :
    obliqueProjectionToLastHyperplane hN v x i =
      x (dropLastCoordinateEmbedding hN i) -
        (x (lastCoordinateIndex hN) / v (lastCoordinateIndex hN)) *
          v (dropLastCoordinateEmbedding hN i) := by
  -- The coordinate formula is exactly the definition of `obliqueProjectionToLastHyperplane`.
  rfl

section

variable {N : ℕ}
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {J : ModelWithCorners ℝ E H}
variable {M : Set (EuclideanSpace ℝ (Fin N))}
variable [ChartedSpace H M] [IsManifold J ∞ M]

/-- A direction whose associated oblique projection to the last-coordinate-zero hyperplane is
defined and restricts to an injective immersion on `M`. -/
class ObliqueProjectionDirectionRestrictsToInjectiveImmersion
    (hN : 0 < N) (v : EuclideanSpace ℝ (Fin N)) : Prop where
  lastCoordinate_ne_zero :
    v (lastCoordinateIndex hN) ≠ 0
  injective :
    Function.Injective (fun p : M ↦ obliqueProjectionToLastHyperplane hN v p.1)
  isImmersion :
    Manifold.IsImmersion
      J
      (𝓡 (N - 1))
      ∞
      (fun p : M ↦ obliqueProjectionToLastHyperplane hN v p.1)

/-- The nonvanishing last-coordinate condition attached to a good oblique projection direction. -/
theorem obliqueProjectionDirectionRestrictsToInjectiveImmersion_fact_lastCoordinate_ne_zero
    (hN : 0 < N) (v : EuclideanSpace ℝ (Fin N))
    [hv :
      ObliqueProjectionDirectionRestrictsToInjectiveImmersion (J := J) (M := M) hN v] :
    Fact (v (lastCoordinateIndex hN) ≠ 0) := by
  -- The class stores the nonvanishing last-coordinate hypothesis as one of its fields.
  exact ⟨hv.lastCoordinate_ne_zero⟩

/-- Lemma 6.13: let `M ⊆ ℝ^N` be a smooth submanifold with or without boundary, presented as a
smoothly embedded subtype. If `N > 2 * dim(M) + 1`, then the set of vectors with nonzero last
coordinate for which the corresponding oblique projection to the last-coordinate-zero hyperplane
restricts to an injective immersion on `M` is dense in `ℝ^N`. -/
theorem dense_oblique_projection_directions_restrict_to_injective_immersion
    (hN : 0 < N)
    (hM :
      Manifold.IsSmoothEmbedding
        J
        (𝓡 N)
        ∞
        (Subtype.val : M → EuclideanSpace ℝ (Fin N)))
    (hdim : 2 * Module.finrank ℝ E + 1 < N) :
    Dense
      {v : EuclideanSpace ℝ (Fin N) |
        ObliqueProjectionDirectionRestrictsToInjectiveImmersion (J := J) (M := M) hN v} := sorry

end
