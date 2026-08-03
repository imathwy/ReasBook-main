module

public import Topology_Munkres_2000.Book.Theorem_9_0_1
public import Mathlib.Analysis.Convex.PathConnected

public section

open Set

/-- Helper for Remark 9.0.2: the standard coordinate splitting identifies
three-dimensional Euclidean space with `ℂ × ℝ`. -/
private noncomputable def euclideanThreeSpaceHomeomorphComplexProdReal :
    EuclideanSpace ℝ (Fin 3) ≃ₜ ℂ × ℝ :=
  EuclideanSpace.finAddEquivProd.toHomeomorph |>.trans
    (Complex.orthonormalBasisOneI.repr.symm.toHomeomorph.prodCongr
      ((EuclideanSpace.equiv (Fin 1) ℝ).trans
        (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ))).toHomeomorph)

/-- Helper for Remark 9.0.2: the standard circle in `ℝ³` is the coordinate
preimage of `Metric.sphere 0 1 × {0}` in `ℂ × ℝ`. -/
private def standardCircleThreeSpace : Set (EuclideanSpace ℝ (Fin 3)) :=
  euclideanThreeSpaceHomeomorphComplexProdReal ⁻¹'
    (Metric.sphere (0 : ℂ) 1 ×ˢ ({0} : Set ℝ))

/-- Helper for Remark 9.0.2: the complement of
`Metric.sphere (0 : ℂ) 1 ×ˢ {0}` is path-connected. -/
private lemma complexCircleProdZero_compl_isPathConnected :
    IsPathConnected (((Metric.sphere (0 : ℂ) 1) ×ˢ ({0} : Set ℝ))ᶜ) := by
  let circleProd : Set (ℂ × ℝ) := Metric.sphere (0 : ℂ) 1 ×ˢ ({0} : Set ℝ)
  let upper : Set (ℂ × ℝ) := circleProdᶜ ∩ {x | 0 ≤ x.2}
  let lower : Set (ℂ × ℝ) := circleProdᶜ ∩ {x | x.2 ≤ 0}
  let upperCenter : ℂ × ℝ := (0, 1)
  let lowerCenter : ℂ × ℝ := (0, -1)
  -- Each height half is star-convex about a point off the circle.
  have hUpperCenter : upperCenter ∈ upper := by
    simp [upper, upperCenter, circleProd]
  have hLowerCenter : lowerCenter ∈ lower := by
    simp [lower, lowerCenter, circleProd]
  have hUpperStar : StarConvex ℝ upperCenter upper := by
    intro y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hz
      have hby : 0 ≤ b * y.2 := mul_nonneg hb hy.2
      have hheight : a + b * y.2 = 0 := by
        simpa [upperCenter, circleProd] using hz.2
      have haZero : a = 0 := by
        linarith
      have hbOne : b = 1 := by
        linarith
      apply hy.1
      simpa [haZero, hbOne] using hz
    · simpa [upperCenter] using add_nonneg ha (mul_nonneg hb hy.2)
  have hLowerStar : StarConvex ℝ lowerCenter lower := by
    intro y hy a b ha hb hab
    refine ⟨?_, ?_⟩
    · intro hz
      have hby : b * y.2 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb hy.2
      have hheight : -a + b * y.2 = 0 := by
        simpa [lowerCenter, circleProd] using hz.2
      have haZero : a = 0 := by
        linarith
      have hbOne : b = 1 := by
        linarith
      apply hy.1
      simpa [haZero, hbOne] using hz
    · simpa [lowerCenter] using add_nonpos (neg_nonpos.mpr ha)
        (mul_nonpos_of_nonneg_of_nonpos hb hy.2)
  have hUpperPath : IsPathConnected upper :=
    hUpperStar.isPathConnected hUpperCenter
  have hLowerPath : IsPathConnected lower :=
    hLowerStar.isPathConnected hLowerCenter
  -- The origin joins the two halves, whose union is the full complement.
  have hIntersection : (upper ∩ lower).Nonempty := by
    refine ⟨(0, 0), ?_⟩
    simp [upper, lower, circleProd]
  have hUnion : upper ∪ lower = circleProdᶜ := by
    apply Set.Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact hx.1
      · exact hx.1
    · intro x hx
      rcases le_total 0 x.2 with hxHeight | hxHeight
      · exact Or.inl ⟨hx, hxHeight⟩
      · exact Or.inr ⟨hx, hxHeight⟩
  rw [← hUnion]
  exact hUpperPath.union hLowerPath hIntersection

/-- Helper for Remark 9.0.2: the coordinate standard circle in `ℝ³` is a
simple closed curve. -/
private lemma standardCircleThreeSpace_isSimpleClosedCurve :
    Topology.IsSimpleClosedCurve standardCircleThreeSpace := by
  -- Restrict the coordinate homeomorphism, split the product subtype, and
  -- discard the singleton factor.
  let circleProd : Set (ℂ × ℝ) := Metric.sphere (0 : ℂ) 1 ×ˢ ({0} : Set ℝ)
  have hPreimage : standardCircleThreeSpace =
      euclideanThreeSpaceHomeomorphComplexProdReal ⁻¹' circleProd := rfl
  let hRestriction :=
    euclideanThreeSpaceHomeomorphComplexProdReal.sets hPreimage
  let hProduct := Homeomorph.Set.prod (Metric.sphere (0 : ℂ) 1) ({0} : Set ℝ)
  let hSingleton := Homeomorph.prodUnique Circle ({0} : Set ℝ)
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  exact ⟨hRestriction.trans (hProduct.trans hSingleton)⟩

/-- Helper for Remark 9.0.2: the complement of the coordinate standard circle
in `ℝ³` is preconnected. -/
private lemma standardCircleThreeSpace_compl_isPreconnected :
    IsPreconnected (standardCircleThreeSpaceᶜ) := by
  -- Transport path-connectedness of the product complement back through the
  -- coordinate homeomorphism.
  rw [standardCircleThreeSpace, ← Set.preimage_compl]
  exact euclideanThreeSpaceHomeomorphComplexProdReal.isPreconnected_preimage.mpr
    complexCircleProdZero_compl_isPathConnected.isConnected.isPreconnected

/-- Helper for Remark 9.0.2: a homeomorphism preimage of a simple closed curve
is again a simple closed curve. -/
private lemma isSimpleClosedCurve_preimage_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (C : Set Y) (hC : Topology.IsSimpleClosedCurve C) :
    Topology.IsSimpleClosedCurve (e ⁻¹' C) := by
  -- Compose the restricted ambient homeomorphism with a circle model for `C`.
  obtain ⟨hCircle⟩ := hC.homeomorphic_circle
  have hPreimage : e ⁻¹' C = e ⁻¹' C := rfl
  rw [Topology.IsSimpleClosedCurve.iff_nonempty_homeomorph_circle]
  exact ⟨(e.sets hPreimage).trans hCircle⟩

/-- Helper for Remark 9.0.2: a preconnected set has at most one connected
component. -/
private lemma mk_connectedComponents_le_one_of_isPreconnected
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S) :
    Cardinal.mk (ConnectedComponents S) ≤ 1 := by
  -- Turn preconnectedness into the subtype instance used by `π₀`.
  letI : PreconnectedSpace S := Subtype.preconnectedSpace hS
  exact Cardinal.le_one_iff_subsingleton.mpr inferInstance

/-- Remark 9.0.2: The plane `ℝ²` is not homeomorphic to three-dimensional
Euclidean space `ℝ³`, although the elementary topological properties developed
so far do not distinguish them. -/
theorem planeNotHomeomorphicThreeSpace :
    ¬ Nonempty (EuclideanSpace ℝ (Fin 2) ≃ₜ EuclideanSpace ℝ (Fin 3)) := by
  -- Pull the fixed circle in `ℝ³` back to the plane.
  rintro ⟨e⟩
  let C : Set (EuclideanSpace ℝ (Fin 2)) := e ⁻¹' standardCircleThreeSpace
  letI : Topology.IsSimpleClosedCurve C :=
    isSimpleClosedCurve_preimage_homeomorph e standardCircleThreeSpace
      standardCircleThreeSpace_isSimpleClosedCurve
  have hJordan := jordanCurve_complement_components C
  rw [Set.separatesInto_iff] at hJordan
  -- Its complement remains preconnected by homeomorphism transport, so it
  -- cannot have the two components supplied by Jordan's theorem.
  have hComplement : IsPreconnected (Cᶜ) := by
    have hComplementEq : Cᶜ = e ⁻¹' standardCircleThreeSpaceᶜ := by
      exact Set.preimage_compl.symm
    rw [hComplementEq]
    exact e.isPreconnected_preimage.mpr standardCircleThreeSpace_compl_isPreconnected
  have hAtMostOne := mk_connectedComponents_le_one_of_isPreconnected hComplement
  rw [hJordan] at hAtMostOne
  norm_num at hAtMostOne
