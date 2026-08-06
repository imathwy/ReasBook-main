import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.IsLocalHomeomorph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace

open scoped TopCat Manifold

/- The standard smooth structure on `RealProjectiveSpace n` is reusable Chapter 23 support data:
it is needed to talk about both the tangent bundle in Problem 23.9.1 and immersion obstructions
in Problem 23.9.2. -/

/-- The standard charted-space structure on `𝕊 n`, transported from the metric sphere model by
`Homeomorph.ulift`. -/
noncomputable instance topCatSphereChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (𝕊 n) :=
  let x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    Classical.choice (NormedSpace.sphere_nonempty_rclike ℝ zero_le_one)
  letI : Nonempty (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
    ⟨ULift.up x⟩
  let hUlift :
      Topology.IsOpenEmbedding
        (Homeomorph.ulift :
          ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
            Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
    Homeomorph.ulift.isOpenEmbedding
  letI : ChartedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (𝕊 n) :=
    hUlift.singletonChartedSpace
  ChartedSpace.comp
    (EuclideanSpace ℝ (Fin n))
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    (𝕊 n)

private noncomputable def realProjectiveSpaceStandardLocalInverse
    (n : ℕ) (x : RealProjectiveSpace n) :
    OpenPartialHomeomorph (RealProjectiveSpace n) (𝕊 n) :=
  let rep : 𝕊 n := Quotient.out x
  let e : OpenPartialHomeomorph (𝕊 n) (RealProjectiveSpace n) :=
    Classical.choose ((sphereToRealProjectiveSpace_isCoveringMap n).isLocalHomeomorph rep)
  e.symm

/-- The standard quotient chart on `RealProjectiveSpace n`, obtained by composing a chosen local
inverse to `sphereToRealProjectiveSpace n` with the standard sphere chart at a chosen
representative. -/
noncomputable def realProjectiveSpaceStandardChartAt (n : ℕ) (x : RealProjectiveSpace n) :
    OpenPartialHomeomorph (RealProjectiveSpace n) (EuclideanSpace ℝ (Fin n)) :=
  let rep : 𝕊 n := Quotient.out x
  (realProjectiveSpaceStandardLocalInverse n x).trans
    (chartAt (EuclideanSpace ℝ (Fin n)) rep)

/-- The standard quotient chart on `RealProjectiveSpace n` is defined at its center point. -/
theorem realProjectiveSpaceStandardChartAt_mem_source (n : ℕ) (x : RealProjectiveSpace n) :
    x ∈ (realProjectiveSpaceStandardChartAt n x).source := sorry

/-- Each standard quotient chart belongs to the standard atlas on `RealProjectiveSpace n`. -/
theorem realProjectiveSpaceStandardChartAt_mem_atlas (n : ℕ) (x : RealProjectiveSpace n) :
    realProjectiveSpaceStandardChartAt n x ∈ Set.range (realProjectiveSpaceStandardChartAt n) :=
  sorry

/-- The standard quotient charts define the canonical charted-space structure on
`RealProjectiveSpace n`. -/
noncomputable instance realProjectiveSpaceStandardChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (RealProjectiveSpace n) where
  atlas :=
    Set.range
      (realProjectiveSpaceStandardChartAt n :
        RealProjectiveSpace n → OpenPartialHomeomorph (RealProjectiveSpace n)
          (EuclideanSpace ℝ (Fin n)))
  chartAt := realProjectiveSpaceStandardChartAt n
  mem_chart_source := realProjectiveSpaceStandardChartAt_mem_source n
  chart_mem_atlas := realProjectiveSpaceStandardChartAt_mem_atlas n

/-- The standard quotient charted-space structure on `RealProjectiveSpace n` is smooth. -/
noncomputable instance realProjectiveSpaceStandardIsManifold (n : ℕ) :
    IsManifold (𝓡 n) ⊤ (RealProjectiveSpace n) := sorry
