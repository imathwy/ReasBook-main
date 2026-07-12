import SmoothManifolds_Lee_2012.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [CompactSpace M] [Nonempty M]

/-- Problem 4-6: a nonempty compact smooth manifold admits no smooth submersion to `ℝ^k` for any
positive integer `k`. -/
-- Proof sketch: pointwise surjectivity of the manifold derivative gives the local projection form
-- for `F`, hence `F` is an open map. Therefore `Set.range F` is a nonempty open subset of
-- `EuclideanSpace ℝ (Fin k)`. Since `M` is compact and `F` is continuous, this range is also
-- compact. For `k > 0`, a nonempty open subset of `ℝ^k` cannot be compact, giving a
-- contradiction.
theorem not_exists_smooth_submersion_to_euclideanSpace {k : ℕ} (hk : 0 < k) :
    ¬ ∃ F : M → EuclideanSpace ℝ (Fin k),
      Manifold.IsSmoothSubmersion I (𝓡 k) F := by
  rintro ⟨F, hF⟩
  have hopen : IsOpen (Set.range F) := hF.isOpenMap.isOpen_range
  have hcompact : IsCompact (Set.range F) := isCompact_range hF.contMDiff.continuous
  have hnonempty : (Set.range F).Nonempty := by
    rcases ‹Nonempty M› with ⟨x⟩
    exact ⟨F x, ⟨x, rfl⟩⟩
  have hrange : Set.range F = Set.univ :=
    IsClopen.eq_univ ⟨hcompact.isClosed, hopen⟩ hnonempty
  have hcompact_target : IsCompact (Set.univ : Set (EuclideanSpace ℝ (Fin k))) := by
    simpa [hrange] using hcompact
  let i : Fin k := ⟨0, hk⟩
  have hcompact_coord : IsCompact (Set.range fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp i) := by
    simpa [Set.image_univ] using hcompact_target.image (EuclideanSpace.proj i).continuous
  have hcoord_surj : Function.Surjective (fun x : EuclideanSpace ℝ (Fin k) ↦ x.ofLp i) := by
    intro t
    refine ⟨EuclideanSpace.single i t, ?_⟩
    simp
  have hcompact_real : IsCompact (Set.univ : Set ℝ) := by
    simpa [hcoord_surj.range_eq] using hcompact_coord
  exact
    (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ))
      (isCompact_univ_iff.mp hcompact_real)
