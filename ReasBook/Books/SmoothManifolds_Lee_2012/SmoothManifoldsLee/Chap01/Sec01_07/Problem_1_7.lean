import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_02.Proposition_1_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ChartedSpace
open scoped Manifold ContDiff

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the
-- stereographic-coordinate API is stated with explicit coordinate formulas and the smooth-structure
-- comparison is phrased via `StructureGroupoid.maximalAtlas`.

section Problem17

variable (n : ℕ)

local notation "AmbientSpace" => EuclideanSpace ℝ (Fin (n + 1))
local notation "ModelSpace" => EuclideanSpace ℝ (Fin n)
local notation "UnitSphere" => Metric.sphere (0 : AmbientSpace) 1

/-- The north pole `(0, …, 0, 1)` of the unit sphere in `ℝ^(n+1)`. -/
def northPoleVec : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc (0 : Fin n → ℝ) (1 : ℝ)) : AmbientSpace)

/-- The south pole `(0, …, 0, -1)` of the unit sphere in `ℝ^(n+1)`. -/
def southPoleVec : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc (0 : Fin n → ℝ) (-1 : ℝ)) : AmbientSpace)

/-- The north pole lies on the unit sphere. -/
theorem northPoleVec_mem_unitSphere :
    northPoleVec n ∈ UnitSphere := sorry

/-- The south pole lies on the unit sphere. -/
theorem southPoleVec_mem_unitSphere :
    southPoleVec n ∈ UnitSphere := sorry

/-- The north pole as a point of the unit sphere. -/
def northPolePoint : UnitSphere :=
  ⟨northPoleVec n, northPoleVec_mem_unitSphere n⟩

/-- The south pole as a point of the unit sphere. -/
def southPolePoint : UnitSphere :=
  ⟨southPoleVec n, southPoleVec_mem_unitSphere n⟩

/-- The complement of the north pole in the unit sphere. -/
def northPoleComplement : TopologicalSpace.Opens UnitSphere :=
  ⟨{x | x ≠ northPolePoint n}, isOpen_compl_singleton⟩

/-- The complement of the south pole in the unit sphere. -/
def southPoleComplement : TopologicalSpace.Opens UnitSphere :=
  ⟨{x | x ≠ southPolePoint n}, isOpen_compl_singleton⟩

/-- The inclusion `ℝ^n → ℝ^(n+1)` obtained by adjoining a last coordinate equal to `0`. -/
def equatorialInclusion (u : ModelSpace) : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc u (0 : ℝ)) : AmbientSpace)

/-- The explicit stereographic projection from the north pole, viewed as a total map on the
underlying sphere. -/
def stereographicNorthMap : UnitSphere → ModelSpace :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x.1 (Fin.castSucc i) / (1 - x.1 (Fin.last n))

/-- The explicit stereographic projection from the south pole, viewed as a total map on the
underlying sphere. -/
def stereographicSouthMap : UnitSphere → ModelSpace :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x.1 (Fin.castSucc i) / (1 + x.1 (Fin.last n))

/-- The north-pole stereographic projection restricted to its natural domain. -/
def stereographicNorth : northPoleComplement n → ModelSpace :=
  fun x ↦ stereographicNorthMap n x.1

/-- The south-pole stereographic projection restricted to its natural domain. -/
def stereographicSouth : southPoleComplement n → ModelSpace :=
  fun x ↦ stereographicSouthMap n x.1

/-- The explicit vector formula for the inverse of stereographic projection from the north pole. -/
def stereographicNorthInvVector (u : ModelSpace) : AmbientSpace :=
  (‖u‖ ^ 2 + 1)⁻¹ •
    (WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace)

/-- The explicit vector formula for the inverse of stereographic projection from the south pole. -/
def stereographicSouthInvVector (u : ModelSpace) : AmbientSpace :=
  (‖u‖ ^ 2 + 1)⁻¹ •
    (WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (1 - ‖u‖ ^ 2)) : AmbientSpace)

/-- The explicit inverse vector for north-pole stereographic projection lies on the unit sphere. -/
theorem stereographicNorthInvVector_mem_unitSphere (u : ModelSpace) :
    stereographicNorthInvVector n u ∈ UnitSphere := sorry

/-- The explicit inverse vector for south-pole stereographic projection lies on the unit sphere. -/
theorem stereographicSouthInvVector_mem_unitSphere (u : ModelSpace) :
    stereographicSouthInvVector n u ∈ UnitSphere := sorry

/-- The explicit inverse of north-pole stereographic projection as a point of the sphere. -/
def stereographicNorthInv (u : ModelSpace) : UnitSphere :=
  ⟨stereographicNorthInvVector n u, stereographicNorthInvVector_mem_unitSphere n u⟩

/-- The explicit inverse of south-pole stereographic projection as a point of the sphere. -/
def stereographicSouthInv (u : ModelSpace) : UnitSphere :=
  ⟨stereographicSouthInvVector n u, stereographicSouthInvVector_mem_unitSphere n u⟩

/-- The inverse of north-pole stereographic projection never lands at the north pole. -/
theorem stereographicNorthInv_ne_northPole (u : ModelSpace) :
    stereographicNorthInv n u ≠ northPolePoint n := sorry

/-- The inverse of south-pole stereographic projection never lands at the south pole. -/
theorem stereographicSouthInv_ne_southPole (u : ModelSpace) :
    stereographicSouthInv n u ≠ southPolePoint n := sorry

/-- The explicit inverse of north-pole stereographic projection as a map into the open complement
of the north pole. -/
def stereographicNorthInvToOpen (u : ModelSpace) : northPoleComplement n :=
  ⟨stereographicNorthInv n u, stereographicNorthInv_ne_northPole n u⟩

/-- The explicit inverse formula really is the coordinate formula displayed in the text. -/
theorem stereographicNorthInv_apply (u : ModelSpace) :
    ((stereographicNorthInv n u : UnitSphere) : AmbientSpace) = stereographicNorthInvVector n u :=
  sorry

/-- North-pole stereographic projection inverts its explicit inverse on the complement of the north
pole. -/
theorem stereographicNorth_left_inv {x : UnitSphere}
    (hx : x ∈ (northPoleComplement n : Set UnitSphere)) :
    stereographicNorthInv n (stereographicNorthMap n x) = x := sorry

/-- The explicit inverse inverts north-pole stereographic projection on all of `ℝ^n`. -/
theorem stereographicNorth_right_inv (u : ModelSpace) :
    stereographicNorthMap n (stereographicNorthInv n u) = u := sorry

/-- South-pole stereographic projection inverts its explicit inverse on the complement of the south
pole. -/
theorem stereographicSouth_left_inv {x : UnitSphere}
    (hx : x ∈ (southPoleComplement n : Set UnitSphere)) :
    stereographicSouthInv n (stereographicSouthMap n x) = x := sorry

/-- The explicit inverse inverts south-pole stereographic projection on all of `ℝ^n`. -/
theorem stereographicSouth_right_inv (u : ModelSpace) :
    stereographicSouthMap n (stereographicSouthInv n u) = u := sorry

/-- The explicit north-pole stereographic formula is continuous away from the north pole. -/
theorem continuousOn_stereographicNorthMap :
    ContinuousOn (stereographicNorthMap n) (northPoleComplement n : Set UnitSphere) := sorry

/-- The explicit inverse to north-pole stereographic projection is continuous. -/
theorem continuous_stereographicNorthInv :
    Continuous (stereographicNorthInv n) := sorry

/-- The explicit south-pole stereographic formula is continuous away from the south pole. -/
theorem continuousOn_stereographicSouthMap :
    ContinuousOn (stereographicSouthMap n) (southPoleComplement n : Set UnitSphere) := sorry

/-- The explicit inverse to south-pole stereographic projection is continuous. -/
theorem continuous_stereographicSouthInv :
    Continuous (stereographicSouthInv n) := sorry

/-- The north-pole stereographic chart as an open partial homeomorphism. -/
def stereographicNorthChart : OpenPartialHomeomorph UnitSphere ModelSpace where
  toFun := stereographicNorthMap n
  invFun := stereographicNorthInv n
  source := northPoleComplement n
  target := Set.univ
  map_source' := fun _ _ ↦ Set.mem_univ _
  map_target' := fun _ _ ↦ stereographicNorthInv_ne_northPole n _
  left_inv' := fun _ hx ↦ stereographicNorth_left_inv n hx
  right_inv' := fun _ _ ↦ stereographicNorth_right_inv n _
  open_source := (northPoleComplement n).2
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_stereographicNorthMap n
  continuousOn_invFun := (continuous_stereographicNorthInv n).continuousOn

/-- The south-pole stereographic chart as an open partial homeomorphism. -/
def stereographicSouthChart : OpenPartialHomeomorph UnitSphere ModelSpace where
  toFun := stereographicSouthMap n
  invFun := stereographicSouthInv n
  source := southPoleComplement n
  target := Set.univ
  map_source' := fun _ _ ↦ Set.mem_univ _
  map_target' := fun _ _ ↦ stereographicSouthInv_ne_southPole n _
  left_inv' := fun _ hx ↦ stereographicSouth_left_inv n hx
  right_inv' := fun _ _ ↦ stereographicSouth_right_inv n _
  open_source := (southPoleComplement n).2
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_stereographicSouthMap n
  continuousOn_invFun := (continuous_stereographicSouthInv n).continuousOn

/-- The chosen chart in the two-chart stereographic atlas: use the south-pole chart at the north
pole and the north-pole chart everywhere else. -/
def stereographicSphereChartAt (x : UnitSphere) : OpenPartialHomeomorph UnitSphere ModelSpace :=
  if x = northPolePoint n then stereographicSouthChart n else stereographicNorthChart n

/-- Every point lies in the source of its chosen chart in the two-chart stereographic atlas. -/
theorem mem_stereographicSphereChartAt_source (x : UnitSphere) :
    x ∈ (stereographicSphereChartAt n x).source := sorry

/-- The chosen chart at each point belongs to the two-chart stereographic atlas. -/
theorem stereographicSphereChartAt_mem_atlas (x : UnitSphere) :
    stereographicSphereChartAt n x ∈
      {f | f = stereographicNorthChart n ∨ f = stereographicSouthChart n} := sorry

/-- The charted-space structure on the sphere generated by the north- and south-pole stereographic
charts. -/
abbrev stereographicSphereChartedSpace : ChartedSpace ModelSpace UnitSphere where
  atlas := {f | f = stereographicNorthChart n ∨ f = stereographicSouthChart n}
  chartAt := stereographicSphereChartAt n
  mem_chart_source := mem_stereographicSphereChartAt_source n
  chart_mem_atlas := stereographicSphereChartAt_mem_atlas n

/-- Problem 1-7 (1): for a point away from the north pole, the explicit stereographic coordinates
are the coordinates of the intersection of the line through the north pole and the point with the
equatorial hyperplane. -/
theorem stereographicNorth_eq_line_intersection (x : northPoleComplement n) :
    AffineMap.lineMap (northPoleVec n) (((x : UnitSphere) : AmbientSpace))
        (1 / (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n)))) =
      equatorialInclusion n (stereographicNorth n x) := sorry

/-- Problem 1-7 (2): for a point away from the south pole, the south-pole stereographic
coordinates are the coordinates of the intersection of the line through the south pole and the
point with the equatorial hyperplane. -/
theorem stereographicSouth_eq_line_intersection (x : southPoleComplement n) :
    AffineMap.lineMap (southPoleVec n) (((x : UnitSphere) : AmbientSpace))
        (1 / (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n)))) =
      equatorialInclusion n (stereographicSouth n x) := sorry

/-- Problem 1-7 (3): stereographic projection from the north pole is bijective. -/
theorem stereographicNorth_bijective :
    Function.Bijective (stereographicNorth n) := sorry

/-- Problem 1-7 (4): the inverse of north-pole stereographic projection is given by the explicit
formula `u ↦ (2u, ‖u‖² - 1) / (‖u‖² + 1)`. -/
theorem stereographicNorth_inverse_formula (u : ModelSpace) :
    ((stereographicNorthInv n u : UnitSphere) : AmbientSpace) =
      (‖u‖ ^ 2 + 1)⁻¹ •
        (WithLp.toLp 2
          (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace) := sorry

/-- Problem 1-7 (5): the transition map from north-pole to south-pole stereographic coordinates is
the inversion `u ↦ ‖u‖⁻² • u` on `ℝ^n \ {0}`. -/
theorem stereographic_transition (u : ModelSpace) (hu : u ≠ 0) :
    stereographicSouthMap n (stereographicNorthInv n u) = (‖u‖ ^ 2)⁻¹ • u := sorry

/-- Problem 1-7 (6): the two explicit stereographic charts define a smooth structure on `S^n`. -/
theorem stereographic_two_chart_isManifold :
    letI : ChartedSpace ModelSpace UnitSphere := stereographicSphereChartedSpace n
    IsManifold (𝓡 n) ∞ UnitSphere := sorry

/-- Problem 1-7 (7): the smooth structure defined by the two stereographic charts has the same
maximal smooth atlas as the standard sphere smooth structure from Example 1.31. -/
theorem stereographic_two_chart_same_smooth_structure :
    (letI := stereographicSphereChartedSpace n
      ; (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere) =
      (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere := sorry

end Problem17
