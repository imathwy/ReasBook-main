import SmoothManifolds_Lee_2012.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.Chap05.Sec05_36.Definition_5_36_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_42.Definition_6_42_extra_2
import SmoothManifolds_Lee_2012.Chap06.Sec06_45.Problem_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ContDiff Manifold NormalBundle

noncomputable section

/-
Domain sampling pass: the target declarations split into two domains.
For the tube-compactness consequences `(1)`, `(3)`, and `(5)`, the owner abstraction is the
canonical metric thickening API:
* `Metric.thickening` / `Metric.cthickening`,
* `IsCompact.cthickening`,
* `Metric.closure_thickening_subset_cthickening`,
* `Metric.self_subset_thickening`,
* `Metric.thickening_subset_interior_cthickening`,
* `Metric.closure_thickening`.
For the genuinely source-facing manifold consequences `(2)` and `(4)`, the relevant chapter owners
remain:
* `IsEmbeddedSubmanifold.IsHypersurface`,
* `Set.IsRegularDomain`,
* the nearby tubular-neighborhood owner `NormalBundle.TubularNeighborhood`.
Source/core/bridge triage:
* source-facing items: the hypersurface and regular-domain consequences `(2)` and `(4)`;
* core/canonical owners: `Metric.thickening`, `Metric.cthickening`,
  `IsEmbeddedSubmanifold.IsHypersurface`, and `Set.IsRegularDomain`;
* bridge/view layer: `frontier` and `closure` applied to the canonical metric thickening owners,
  with no extra local tube wrapper.
-/

universe u

variable {n m : ℕ}

section

/-- For a compact subset of a proper pseudo-metric space, the frontier of each open thickening is
compact. -/
theorem isCompact_frontier_thickening
    {α : Type u} [PseudoMetricSpace α] [ProperSpace α] {M : Set α}
    (hMcompact : IsCompact M) (ε : ℝ) :
    IsCompact (frontier (Metric.thickening ε M)) := by
  have hclosure : IsCompact (closure (Metric.thickening ε M)) := by
    exact (hMcompact.cthickening : IsCompact (Metric.cthickening ε M)).of_isClosed_subset
      isClosed_closure (Metric.closure_thickening_subset_cthickening ε M)
  exact hclosure.of_isClosed_subset isClosed_frontier frontier_subset_closure

/-- For a compact subset of a proper pseudo-metric space, the closure of each open thickening is
compact. -/
theorem isCompact_closure_thickening
    {α : Type u} [PseudoMetricSpace α] [ProperSpace α] {M : Set α}
    (hMcompact : IsCompact M) (ε : ℝ) :
    IsCompact (closure (Metric.thickening ε M)) :=
  (hMcompact.cthickening : IsCompact (Metric.cthickening ε M)).of_isClosed_subset
    isClosed_closure (Metric.closure_thickening_subset_cthickening ε M)

/-- In a pseudo-metric space, every set is contained in the interior of the closure of each
positive-radius open thickening around it. -/
theorem subset_interior_closure_thickening
    {α : Type u} [PseudoMetricSpace α] {M : Set α}
    {ε : ℝ} (hε : 0 < ε) :
    M ⊆ interior (closure (Metric.thickening ε M)) := by
  exact (Metric.self_subset_thickening hε M).trans Metric.isOpen_thickening.subset_interior_closure

end

section

variable {M : Set (EuclideanSpace ℝ (Fin n))}
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
variable [IsManifold (𝓡 m) ∞ M]

local notation "dimRn" => Module.finrank ℝ (EuclideanSpace ℝ (Fin n))

/-- Helper for Problem 6-6: a compact embedded submanifold fits inside a sufficiently small closed
metric tube lying in any chosen tubular neighborhood. -/
theorem existsSmallClosedThickeningSubsetNeighborhood
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (hMcompact : IsCompact (M : Set (EuclideanSpace ℝ (Fin n))))
    (T : NormalBundle.TubularNeighborhood n m M) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) := by
  -- Shrink the ambient open neighborhood of `M` using the compact-set thickening lemma.
  simpa using hMcompact.exists_cthickening_subset_open T.neighborhood.2 T.contains_base

/-- Helper for Problem 6-6: for any positive radius, the metric tube around a compact set already
has the compactness and interior-containment pieces needed in the final theorem. -/
theorem thickeningCompactnessAndInterior
    (hMcompact : IsCompact (M : Set (EuclideanSpace ℝ (Fin n))))
    {ε : ℝ} (hε : 0 < ε) :
    let S : Set (EuclideanSpace ℝ (Fin n)) := frontier (Metric.thickening ε M)
    let T : Set (EuclideanSpace ℝ (Fin n)) := closure (Metric.thickening ε M)
    IsCompact S ∧ IsCompact T ∧ M ⊆ interior T := by
  -- Package the already-proved metric-thickening lemmas in the same `let`-shape as the target.
  dsimp
  exact ⟨isCompact_frontier_thickening hMcompact ε,
    isCompact_closure_thickening hMcompact ε,
    subset_interior_closure_thickening hε⟩

/-- Helper for Problem 6-6: choose one tubular neighborhood of the compact embedded submanifold and
shrink it to a uniform closed metric tube. -/
theorem existsTubularNeighborhoodWithSmallClosedThickening
    (hM : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M)
    (hMcompact : IsCompact (M : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ csNM : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]),
      ∃ hsNM : IsManifold (𝓡 n) ∞ (NM[n, m; M]),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
        let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
        ∃ T : NormalBundle.TubularNeighborhood n m M,
          ∃ ε₀ : ℝ, 0 < ε₀ ∧
            Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) := by
  let _ : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M := hM
  -- First choose the closest-point tubular neighborhood supplied by the earlier Problem 6-5 owner,
  -- then ignore the extra minimization data and shrink its ambient neighborhood by compactness.
  obtain ⟨csNM, hsNM, T, _hclosest⟩ :=
    embedded_submanifold_has_tubular_neighborhood_with_unique_closest_point_retraction
      (n := n) (m := m) (M := M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
  let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
  -- Then compactness shrinks that open neighborhood to a uniform closed metric thickening.
  obtain ⟨ε₀, hε₀, hsubset⟩ :=
    existsSmallClosedThickeningSubsetNeighborhood (M := M) hMcompact T
  exact ⟨csNM, hsNM, T, ε₀, hε₀, hsubset⟩

/-- Helper for Problem 6-6: once one closed `ε₀`-tube lies inside a tubular neighborhood, every
smaller closed and open tube lies in the same ambient neighborhood. -/
theorem smallerThickeningsSubsetTubularNeighborhood
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    {ε ε₀ : ℝ} (hε₀ : ε < ε₀)
    (hcthick₀ :
      Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n)))) :
    Metric.cthickening ε M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) ∧
      Metric.thickening ε M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) := by
  constructor
  · -- Monotonicity of the closed thickening shrinks the `ε₀`-tube down to the current radius.
    exact (Metric.cthickening_mono hε₀.le M).trans hcthick₀
  · -- The open thickening is always contained in the corresponding closed thickening.
    exact (Metric.thickening_subset_cthickening ε M).trans
      ((Metric.cthickening_mono hε₀.le M).trans hcthick₀)

/-- Helper for Problem 6-6: the distance function from a tubular-neighborhood point to the base
submanifold, viewed on the subtype `M`. -/
def tubularBaseDistance
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (y : T.neighborhood) : M → ℝ :=
  fun z ↦ dist (y : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n))

/-- Helper for Problem 6-6: the canonical base-point projection of a tubular-neighborhood point,
written without importing Proposition 6.25. -/
def tubularBasePoint
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (y : T.neighborhood) : M :=
  π_NM[n, m; M] (T.endpointDiffeomorph.symm y)

/-- Helper for Problem 6-6: if a tubular neighborhood comes with the closest-point
characterization from Problem 6-5, then the ambient distance to `M` is the norm of the normal
coordinate. -/
-- TODO: refactor this minimizing-point argument through the later controlled distance identity
-- `tubularBasePoint_dist_eq_normalNorm` so the `IsMinOn`/`infDist` bridge does not hit `whnf`
-- timeout in the current toolchain.
theorem tubularInfDist_eq_normalNorm_of_closestPoint
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (hclosest :
      ∀ y : T.neighborhood, ∀ x : M,
        IsMinOn (tubularBaseDistance (M := M) T y) Set.univ x ↔
          x = tubularBasePoint (M := M) T y) :
    ∀ y : T.neighborhood,
      Metric.infDist (y : EuclideanSpace ℝ (Fin n)) M =
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ := sorry

/-- Helper for Problem 6-6: one can choose a tubular neighborhood whose canonical base-point
projection is exactly the unique closest-point map. -/
theorem existsTubularNeighborhoodWithClosestPoint
    (hM : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M) :
    ∃ csNM : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]),
      ∃ hsNM : IsManifold (𝓡 n) ∞ (NM[n, m; M]),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
        let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
        ∃ T : NormalBundle.TubularNeighborhood n m M,
          ∀ y : T.neighborhood, ∀ x : M,
            IsMinOn (tubularBaseDistance (M := M) T y) Set.univ x ↔
              x = tubularBasePoint (M := M) T y := by
  let _ : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M := hM
  -- Use the earlier textbook owner that upgrades one tubular neighborhood to the unique
  -- closest-point retraction package.
  obtain ⟨csNM, hsNM, T, hclosest⟩ :=
    embedded_submanifold_has_tubular_neighborhood_with_unique_closest_point_retraction
      (n := n) (m := m) (M := M)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
  let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
  refine ⟨csNM, hsNM, T, ?_⟩
  intro y x
  -- Rewrite the imported closest-point statement into this file's local helper names.
  simpa [tubularBaseDistance, tubularBasePoint,
    NormalBundle.TubularNeighborhood.retraction] using hclosest y x

/-- Helper for Problem 6-6: after choosing a closest-point tubular neighborhood, compactness still
shrinks it to a uniform closed metric tube on which the tubular normal coordinate computes the
ambient distance to `M`. -/
theorem existsSmallTubeInfDistBridge
    (hM : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M)
    (hMcompact : IsCompact (M : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ csNM : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]),
      ∃ hsNM : IsManifold (𝓡 n) ∞ (NM[n, m; M]),
        let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
        let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
        ∃ T : NormalBundle.TubularNeighborhood n m M,
          ∃ ε₀ : ℝ, 0 < ε₀ ∧
            Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))) ∧
            ∀ y : T.neighborhood,
              (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.cthickening ε₀ M →
                Metric.infDist (y : EuclideanSpace ℝ (Fin n)) M =
                  ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ := by
  -- Route correction: instead of leaving the closest-point step implicit, first choose the
  -- Problem 6-5 tubular neighborhood and then shrink it by compactness.
  obtain ⟨csNM, hsNM, T, hclosest⟩ :=
    existsTubularNeighborhoodWithClosestPoint (M := M) hM
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
  let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
  obtain ⟨ε₀, hε₀, hsubset⟩ :=
    existsSmallClosedThickeningSubsetNeighborhood (M := M) hMcompact T
  refine ⟨csNM, hsNM, T, ε₀, hε₀, hsubset, ?_⟩
  intro y _hy
  -- The closest-point characterization upgrades the tubular base point to the exact infimum
  -- distance formula on the whole chosen neighborhood, so in particular on the small closed tube.
  exact tubularInfDist_eq_normalNorm_of_closestPoint (M := M) T hclosest y

/-- Helper for Problem 6-6: in tubular coordinates, the distinguished base point is exactly
`‖v‖` away from the ambient endpoint. -/
theorem tubularBasePoint_dist_eq_normalNorm
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (y : T.neighborhood) :
    dist (y : EuclideanSpace ℝ (Fin n))
        ((tubularBasePoint (M := M) T y : M) : EuclideanSpace ℝ (Fin n)) =
      ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ := by
  -- Rewrite `y` by its endpoint coordinates and then subtract the base point component.
  have hy :
      (y : EuclideanSpace ℝ (Fin n)) =
        NormalBundle.endpointMap n m M (T.endpointDiffeomorph.symm y) := by
    calc
      (y : EuclideanSpace ℝ (Fin n)) =
          (T.endpointDiffeomorph (T.endpointDiffeomorph.symm y) :
            EuclideanSpace ℝ (Fin n)) := by
              simp
      _ = NormalBundle.endpointMap n m M (T.endpointDiffeomorph.symm y) := by
            simpa using T.endpointDiffeomorph_eq (T.endpointDiffeomorph.symm y)
  rw [dist_eq_norm, hy, tubularBasePoint, NormalBundle.endpointMap]
  change
    ‖(((π_NM[n, m; M] (T.endpointDiffeomorph.symm y) : M) :
        EuclideanSpace ℝ (Fin n)) +
        normal_bundle_vector n m M (T.endpointDiffeomorph.symm y) -
        ((π_NM[n, m; M] (T.endpointDiffeomorph.symm y) : M) :
          EuclideanSpace ℝ (Fin n)))‖ =
      ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖
  have hcancel :
      (((π_NM[n, m; M] (T.endpointDiffeomorph.symm y) : M) :
          EuclideanSpace ℝ (Fin n)) +
          normal_bundle_vector n m M (T.endpointDiffeomorph.symm y) -
          ((π_NM[n, m; M] (T.endpointDiffeomorph.symm y) : M) :
            EuclideanSpace ℝ (Fin n))) =
        normal_bundle_vector n m M (T.endpointDiffeomorph.symm y) := by
    abel
  rw [hcancel]

/-- Helper for Problem 6-6: a tubular-neighborhood point with normal norm `< ε` already lies in
the ambient open `ε`-tube. -/
theorem tubularPoint_mem_thickening_of_normalNorm_lt
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (y : T.neighborhood) {ε : ℝ}
    (hε : ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ < ε) :
    (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.thickening ε M := by
  -- Use the canonical tubular base point as the witness in the metric thickening.
  refine Metric.mem_thickening_iff.2 ?_
  refine ⟨((tubularBasePoint (M := M) T y : M) : EuclideanSpace ℝ (Fin n)),
    (tubularBasePoint (M := M) T y).2, ?_⟩
  simpa [tubularBasePoint_dist_eq_normalNorm (M := M) T y] using hε

/-- Helper for Problem 6-6: a tubular-neighborhood point with normal norm `≤ ε` already lies in
the ambient closed `ε`-tube. -/
theorem tubularPoint_mem_cthickening_of_normalNorm_le
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    (y : T.neighborhood) {ε : ℝ}
    (hε : ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ≤ ε) :
    (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.cthickening ε M := by
  -- The same canonical base point provides the closed-thickening witness after weakening `<` to `≤`.
  refine Metric.mem_cthickening_of_dist_le
    (y : EuclideanSpace ℝ (Fin n))
    (((tubularBasePoint (M := M) T y : M) : EuclideanSpace ℝ (Fin n)))
    ε M
    (tubularBasePoint (M := M) T y).2 ?_
  simpa [tubularBasePoint_dist_eq_normalNorm (M := M) T y] using hε

/-- Helper for Problem 6-6: inside the chosen small tubular neighborhood, the open metric
`ε`-tube is exactly the image of the tubular squared-radius sublevel set. -/
theorem smallTube_eq_radiusSqSublevelImage
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (T : NormalBundle.TubularNeighborhood n m M)
    {ε ε₀ : ℝ} (hε : 0 < ε) (hε₀ : ε < ε₀)
    (hcthick₀ :
      Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))))
    (hbridge :
      ∀ y : T.neighborhood,
        (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.cthickening ε₀ M →
          Metric.infDist (y : EuclideanSpace ℝ (Fin n)) M =
            ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖) :
    Metric.thickening ε M =
      Subtype.val '' {y : T.neighborhood |
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) <
          ε ^ (2 : ℕ)} := by
  ext x
  constructor
  · intro hx
    -- Rewrite the metric tube through the closest-point bridge on the small closed neighborhood.
    obtain ⟨z, hz, hxz⟩ := Metric.mem_thickening_iff.1 hx
    have hx₀ : x ∈ Metric.cthickening ε₀ M := by
      exact Metric.mem_cthickening_of_dist_le x z ε₀ M hz (by linarith)
    let y : T.neighborhood := ⟨x, hcthick₀ hx₀⟩
    have hinf : Metric.infDist x M < ε := by
      exact (Metric.mem_thickening_iff_infDist_lt ⟨z, hz⟩).1 hx
    have hnorm :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ < ε := by
      simpa [y, hbridge y hx₀] using hinf
    refine ⟨y, ?_, rfl⟩
    have hvnonneg :
        0 ≤ ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ :=
      norm_nonneg _
    have hsq :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ *
            ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ <
          ε * ε := by
      nlinarith [hε, hnorm, hvnonneg]
    simpa [pow_two] using hsq
  · rintro ⟨y, hy, rfl⟩
    -- Unsquare the radius inequality and use the canonical base point as the thickening witness.
    have hnorm :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ < ε := by
      have hvnonneg :
          0 ≤ ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ :=
        norm_nonneg _
      have hySq :
          ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ *
              ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ <
            ε * ε := by
        simpa [pow_two] using hy
      nlinarith [hε, hvnonneg, hySq]
    exact tubularPoint_mem_thickening_of_normalNorm_lt (M := M) T y hnorm

/-- Helper for Problem 6-6: for a nonempty compact embedded submanifold, the closed metric
`ε`-tube is exactly the image of the closed tubular squared-radius sublevel set. -/
theorem smallClosedTube_eq_radiusSqClosedSublevelImage
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (hMne : M.Nonempty)
    (T : NormalBundle.TubularNeighborhood n m M)
    {ε ε₀ : ℝ} (hε : 0 < ε) (hε₀ : ε < ε₀)
    (hcthick₀ :
      Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))))
    (hbridge :
      ∀ y : T.neighborhood,
        (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.cthickening ε₀ M →
          Metric.infDist (y : EuclideanSpace ℝ (Fin n)) M =
            ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖) :
    Metric.cthickening ε M =
      Subtype.val '' {y : T.neighborhood |
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) ≤
          ε ^ (2 : ℕ)} := by
  ext x
  constructor
  · intro hx
    -- Shrink the closed-tube point into the chosen tubular neighborhood and rewrite its distance
    -- to `M` through the closest-point bridge.
    have hx₀ : x ∈ Metric.cthickening ε₀ M :=
      Metric.cthickening_mono hε₀.le M hx
    let y : T.neighborhood := ⟨x, hcthick₀ hx₀⟩
    have hinf : Metric.infDist x M ≤ ε := by
      have hinfEDist :
          Metric.infEDist x M ≤ ENNReal.ofReal ε :=
        Metric.mem_cthickening_iff.1 hx
      have htoReal :
          (Metric.infEDist x M).toReal ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hinfEDist
      simpa [Metric.infDist, hε.le] using htoReal
    have hnorm :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ≤ ε := by
      simpa [y, hbridge y hx₀] using hinf
    refine ⟨y, ?_, rfl⟩
    have hvnonneg :
        0 ≤ ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ :=
      norm_nonneg _
    have hsq :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ *
            ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ≤
          ε * ε := by
      nlinarith [hε, hnorm, hvnonneg]
    simpa [pow_two] using hsq
  · rintro ⟨y, hy, rfl⟩
    -- Unsquare the closed inequality and use the canonical base point of the tubular coordinates.
    have hnorm :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ≤ ε := by
      have hvnonneg :
          0 ≤ ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ :=
        norm_nonneg _
      have hySq :
          ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ *
              ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ≤
            ε * ε := by
        simpa [pow_two] using hy
      nlinarith [hε, hvnonneg, hySq]
    exact tubularPoint_mem_cthickening_of_normalNorm_le (M := M) T y hnorm

/-- Helper for Problem 6-6: for a nonempty compact embedded submanifold, the frontier of the open
`ε`-tube is exactly the image of the tubular squared-radius level set. -/
theorem smallTube_frontier_eq_radiusSqLevelImage
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M])]
    [IsManifold (𝓡 n) ∞ (NM[n, m; M])]
    (hMne : M.Nonempty)
    (T : NormalBundle.TubularNeighborhood n m M)
    {ε ε₀ : ℝ} (hε : 0 < ε) (hε₀ : ε < ε₀)
    (hcthick₀ :
      Metric.cthickening ε₀ M ⊆ (T.neighborhood : Set (EuclideanSpace ℝ (Fin n))))
    (hbridge :
      ∀ y : T.neighborhood,
        (y : EuclideanSpace ℝ (Fin n)) ∈ Metric.cthickening ε₀ M →
          Metric.infDist (y : EuclideanSpace ℝ (Fin n)) M =
            ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖) :
    frontier (Metric.thickening ε M) =
      Subtype.val '' {y : T.neighborhood |
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) =
          ε ^ (2 : ℕ)} := by
  -- Rewrite both the closure and the open tube by the already-stabilized tubular radius-squared
  -- descriptions, so the frontier becomes the difference between `≤` and `<`.
  rw [Metric.isOpen_thickening.frontier_eq, closure_thickening hε M]
  rw [smallClosedTube_eq_radiusSqClosedSublevelImage (M := M) hMne T hε hε₀ hcthick₀ hbridge]
  rw [smallTube_eq_radiusSqSublevelImage (M := M) T hε hε₀ hcthick₀ hbridge]
  ext x
  constructor
  · rintro ⟨hxClosed, hxOpen⟩
    obtain ⟨y, hyLe, rfl⟩ := hxClosed
    have hyNotLt :
        ¬ ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) <
            ε ^ (2 : ℕ) := by
      intro hyLt
      exact hxOpen ⟨y, hyLt, rfl⟩
    have hyEq :
        ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) =
          ε ^ (2 : ℕ) := by
      exact le_antisymm hyLe (le_of_not_gt hyNotLt)
    exact ⟨y, hyEq, rfl⟩
  · rintro ⟨y, hyEq, rfl⟩
    constructor
    · exact ⟨y, by simpa using hyEq.le, rfl⟩
    · intro hxOpen
      rcases hxOpen with ⟨y', hy'lt, hy'x⟩
      have hy' : y' = y := by
        apply Subtype.ext
        simpa using hy'x
      have hyLt :
          ‖normal_bundle_vector n m M (T.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ) <
            ε ^ (2 : ℕ) := by
        simpa [hy'] using hy'lt
      exact (lt_irrefl (ε ^ (2 : ℕ))) (hyEq ▸ hyLt)

/-- Problem 6-6: if `M ⊆ ℝ^n` is a compact embedded submanifold and `n > 0`, then for all
sufficiently small `ε > 0`, the frontier of its open `ε`-tube is a compact embedded hypersurface
in `ℝ^n`, and the closure of the open `ε`-tube is a compact regular domain in `ℝ^n` whose interior
contains `M`. -/
theorem compact_embedded_submanifold_small_tubes
    (hn : 0 < n)
    (hM : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M)
    (hMcompact : IsCompact (M : Set (EuclideanSpace ℝ (Fin n)))) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ⦃ε : ℝ⦄ (hε : 0 < ε) (hε₀ : ε < ε₀),
        let S : Set (EuclideanSpace ℝ (Fin n)) := frontier (Metric.thickening ε M)
        let T : Set (EuclideanSpace ℝ (Fin n)) := closure (Metric.thickening ε M)
        IsCompact S ∧
          (∃ cs :
              ChartedSpace
                (EuclideanSpace ℝ (Fin (n - 1)))
                S,
            ∃ hs :
                IsManifold
                  (𝓡 (n - 1))
                  ∞
                  S,
              let _ :
                  ChartedSpace
                    (EuclideanSpace ℝ (Fin (n - 1)))
                    S := cs
              let _ :
                  IsManifold
                    (𝓡 (n - 1))
                    ∞
                    S := hs
              ∃ hFrontier :
                  IsEmbeddedSubmanifold
                    (𝓡 n)
                    (𝓡 (n - 1))
                    S,
                hFrontier.IsHypersurface) ∧
          IsCompact T ∧
          (∃ smwb : SmoothManifoldWithBoundary dimRn T,
            let _ :
                SmoothManifoldWithBoundary dimRn T := smwb
            Set.IsRegularDomain (𝓡 n) T) ∧
          M ⊆ interior T := by
  let _ : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) M := hM
  -- Route correction: the available compiled prefix already provides Theorem 6.24, so we can fix
  -- a tubular neighborhood, the closest-point bridge, and a uniform closed metric tube before the
  -- remaining regular-value packaging.
  obtain ⟨csNM, hsNM, Ttube, ε₀, hε₀, hcthick₀, hbridge⟩ :=
    existsSmallTubeInfDistBridge (M := M) hM hMcompact
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin n)) (NM[n, m; M]) := csNM
  let _ : IsManifold (𝓡 n) ∞ (NM[n, m; M]) := hsNM
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀
  -- The compactness and interior-containment part of the target is already available metric-side.
  have hmetric :
      let S : Set (EuclideanSpace ℝ (Fin n)) := frontier (Metric.thickening ε M)
      let T : Set (EuclideanSpace ℝ (Fin n)) := closure (Metric.thickening ε M)
      IsCompact S ∧ IsCompact T ∧ M ⊆ interior T :=
    thickeningCompactnessAndInterior (M := M) hMcompact hε
  obtain ⟨hcthick, hthick⟩ :=
    smallerThickeningsSubsetTubularNeighborhood (M := M) Ttube hε₀ hcthick₀
  let _ := hmetric
  let _ := hthick
  let ρ : Ttube.neighborhood → ℝ := fun y ↦
    ‖normal_bundle_vector n m M (Ttube.endpointDiffeomorph.symm y)‖ ^ (2 : ℕ)
  let _ := ρ
  let _ := hbridge
  -- The metric-side rewrite layer is now isolated in the closed-tube and frontier image lemmas
  -- above. The only remaining blocker is the smooth/regular-value interface for `ρ`.
  -- TODO: expose a dependency-closed smooth normal-bundle coordinate package for the chosen
  -- `csNM/hsNM/Ttube`, prove `ContMDiff` and regular-value data for `ρ`, and then transport the
  -- Chapter 5 regular-sublevel / regular-level owners back to the ambient Euclidean sets.
  sorry

end
