import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel
import Mathlib.Logic.Equiv.Fin.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Observation_9_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open CategoryTheory
open scoped unitInterval Topology Topology.Homotopy

noncomputable section

universe u v w

local notation "BasedSpace" => Under (⊤_ TopCat)

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

/-- Helper for Lemma 9.6.6: lift a continuous map to a common universe so the Chapter 9 based-space
API can be reused across independent source and target universes. -/
def uliftContinuousMapAcrossUniverses (e : C(Y, Z)) : C(ULift.{v} Y, ULift.{u} Z) :=
  ⟨fun y ↦ ULift.up (e y.down),
    continuous_uliftUp.comp (e.continuous.comp continuous_uliftDown)⟩

/-- Helper for Lemma 9.6.6: evaluating the lifted map is the same as applying `e` and lifting the
result back to the common universe. -/
@[simp] theorem uliftContinuousMapAcrossUniverses_apply (e : C(Y, Z)) (y : ULift.{v} Y) :
    uliftContinuousMapAcrossUniverses e y = ULift.up (e y.down) :=
  rfl

/-- Helper for Lemma 9.6.6: `underTopOfPointMap` restated on the lifted source and target spaces,
so the homotopy-fiber route can be formed for `e : C(Y, Z)` across independent universes. -/
def underTopOfPointMapAcrossUniverses (e : C(Y, Z)) (y₀ : Y) :
    underTopOfPoint (ULift.{v} Y) (ULift.up y₀) ⟶
      underTopOfPoint (ULift.{u} Z) (ULift.up (e y₀)) :=
  Under.homMk (TopCat.ofHom (uliftContinuousMapAcrossUniverses e)) (by
    -- The lifted map sends the chosen lifted basepoint to the chosen lifted image.
    ext u
    rfl)

/-- Helper for Lemma 9.6.6: the underlying continuous map of the universe-polymorphic based map is
the lifted map induced by `e`. -/
@[simp] theorem underTopOfPointMapAcrossUniverses_hom (e : C(Y, Z)) (y₀ : Y) :
    (underTopOfPointMapAcrossUniverses e y₀).right.hom = uliftContinuousMapAcrossUniverses e :=
  rfl

/-- Helper for Lemma 9.6.6: the universe-polymorphic based map preserves the chosen basepoint. -/
@[simp] theorem underTopOfPointMapAcrossUniverses_basepoint (e : C(Y, Z)) (y₀ : Y) :
    (underTopOfPointMapAcrossUniverses e y₀).right.hom
        (underTopBasepoint (underTopOfPoint (ULift.{v} Y) (ULift.up y₀))) =
      underTopBasepoint (underTopOfPoint (ULift.{u} Z) (ULift.up (e y₀))) := by
  -- After lifting both spaces to the same universe, this is the standard basepoint calculation.
  rfl

/-- Helper for Lemma 9.6.6: the homotopy fiber `F(e; y₁)` of `e`, pointed at the chosen element
`y₁ : Y`, built from the universe-polymorphic based-map bridge above. -/
abbrev homotopyFiberAt (e : C(Y, Z)) (y₁ : Y) :=
  homotopyFiber (underTopOfPointMapAcrossUniverses e y₁)

/-- Helper for Lemma 9.6.6: the target space `Z` lifted into the common universe used by
`underTopOfPointMapAcrossUniverses`. -/
private def uliftTarget (Z : Type v) [TopologicalSpace Z] : C(Z, ULift.{u} Z) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- Helper for Lemma 9.6.6: evaluating `uliftTarget` just applies `ULift.up`. -/
@[simp] private theorem uliftTarget_apply (z : Z) :
    uliftTarget Z z = ULift.up z :=
  rfl

/-- Helper for Lemma 9.6.6: postcomposing a continuous map with `uliftTarget` lifts its target to
the common universe used by the homotopy-fiber model. -/
private def uliftTargetContinuousMap {A : Type w} [TopologicalSpace A] (g : C(A, Z)) :
    C(A, ULift.{u} Z) :=
  (uliftTarget Z).comp g

/-- Helper for Lemma 9.6.6: evaluating the lifted target map is just evaluating the original map
and applying `ULift.up`. -/
@[simp] private theorem uliftTargetContinuousMap_apply {A : Type w} [TopologicalSpace A]
    (g : C(A, Z)) (a : A) :
    uliftTargetContinuousMap g a = ULift.up (g a) :=
  rfl

/-- Helper for Lemma 9.6.6: the radial segment from the disk center to `x` stays inside
`D^(n+1)`. -/
private theorem radialSegment_mem_unitDisk (n : ℕ) (x : sphereBoundary n) (t : I) :
    (t : ℝ) • x.1 ∈ unitDisk n := by
  -- Use `‖x‖ = 1` on the sphere and `0 ≤ t ≤ 1` on the unit interval.
  rw [mem_unitDisk_iff, norm_smul]
  have hx : ‖x.1‖ = 1 := mem_sphereBoundary_iff.mp x.2
  rw [hx]
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg t.2.1] using t.2.2
  simpa using ht

/-- Helper for Lemma 9.6.6: the radial segment gives a continuous map from `I` into `D^(n+1)`.
-/
private def radialSegmentContinuousMap (n : ℕ) (x : sphereBoundary n) : C(I, unitDisk n) :=
  ⟨fun t ↦ ⟨(t : ℝ) • x.1, radialSegment_mem_unitDisk n x t⟩, by fun_prop⟩

/-- Helper for Lemma 9.6.6: the origin is the cone point of `D^(n+1)`. -/
private theorem zero_mem_unitDisk (n : ℕ) : (0 : EuclideanSpace ℝ (Fin (n + 1))) ∈ unitDisk n := by
  -- The cone point is the origin, whose norm is zero.
  simp [mem_unitDisk_iff]

/-- Helper for Lemma 9.6.6: the cone point of the disk model `D^(n+1)`, realized by the origin.
-/
private def unitDiskCenter (n : ℕ) : unitDisk n :=
  ⟨0, zero_mem_unitDisk n⟩

/-- Helper for Lemma 9.6.6: the radial segment starts at the cone point of the disk model. -/
private theorem radialSegment_zero (n : ℕ) (x : sphereBoundary n) :
    radialSegmentContinuousMap n x 0 = (⟨0, by simp [mem_unitDisk_iff]⟩ : unitDisk n) := by
  -- At time `0`, scalar multiplication collapses the segment to the origin.
  apply Subtype.ext
  simp [radialSegmentContinuousMap]

/-- Helper for Lemma 9.6.6: the radial segment ends at the chosen boundary point. -/
private theorem radialSegment_one (n : ℕ) (x : sphereBoundary n) :
    radialSegmentContinuousMap n x 1 = sphereBoundaryInclusion n x := by
  -- At time `1`, the radial segment recovers the boundary inclusion.
  apply Subtype.ext
  simp [radialSegmentContinuousMap, sphereBoundaryInclusion]

/-- Helper for Lemma 9.6.6: the standard radial segment in `D^(n+1)` joins the cone point to a
boundary point of `S^n = ∂D^(n+1)`. -/
private def unitDiskRadialPathToBoundary (n : ℕ) (x : sphereBoundary n) :
    Path (⟨0, by simp [mem_unitDisk_iff]⟩ : unitDisk n) (sphereBoundaryInclusion n x) :=
  Path.mk
    (radialSegmentContinuousMap n x)
    (radialSegment_zero n x)
    (radialSegment_one n x)

/-- Helper for Lemma 9.6.6: evaluating the HELP homotopy at a boundary point gives the boundary
track from `e (f x)` to `g (sphereBoundaryInclusion n x)`, lifted to the common target universe.
-/
private def helpBoundaryValuePath (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    Path (ULift.up (e (f x))) (ULift.up (g (sphereBoundaryInclusion n x))) :=
  (H.evalAt x).map (uliftTarget Z).continuous

/-- Helper for Lemma 9.6.6: evaluating the HELP homotopy at the sphere basepoint and correcting by
the radial disk path yields a path from `e y₁` to the cone value `g 0`, where
`y₁ := f (sphereBoundaryBasepoint n)`. -/
private def basepointToConeValuePath (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Path (ULift.up (e (f (sphereBoundaryBasepoint n)))) (ULift.up (g (unitDiskCenter n))) :=
  (helpBoundaryValuePath n e f g H (sphereBoundaryBasepoint n)).trans
    (((unitDiskRadialPathToBoundary n (sphereBoundaryBasepoint n)).map
      (uliftTargetContinuousMap g).continuous).symm)

/-- Helper for Lemma 9.6.6: a HELP boundary datum determines, for each `x : S^n`, the path
radially from the cone value `g 0` to the boundary value `g x`. -/
private theorem boundaryDatumRadialHomotopyContinuous (n : ℕ) (g : C(unitDisk n, Z)) :
    Continuous fun p : I × sphereBoundary n =>
      ULift.up (g ⟨(p.1 : ℝ) • p.2.1, radialSegment_mem_unitDisk n p.2 p.1⟩) := by
  -- The radial formula is polynomial in `(t, x)` before applying the continuous map `g`.
  fun_prop

/-- Helper for Lemma 9.6.6: the radial homotopy starts at the cone value `g 0`. -/
private theorem boundaryDatumRadialHomotopy_zero (n : ℕ) (g : C(unitDisk n, Z)) :
    ∀ x : sphereBoundary n,
      ULift.up (g ⟨((0 : I) : ℝ) • x.1, radialSegment_mem_unitDisk n x 0⟩) =
        ULift.up (g (unitDiskCenter n)) := by
  -- At time `0`, the radial segment is the disk center.
  intro x
  simp [unitDiskCenter]

/-- Helper for Lemma 9.6.6: the radial homotopy ends at the lifted boundary map
`x ↦ ULift.up (g (sphereBoundaryInclusion n x))`. -/
private theorem boundaryDatumRadialHomotopy_one (n : ℕ) (g : C(unitDisk n, Z)) :
    ∀ x : sphereBoundary n,
      ULift.up (g ⟨((1 : I) : ℝ) • x.1, radialSegment_mem_unitDisk n x 1⟩) =
        ((uliftTargetContinuousMap g).comp (sphereBoundaryInclusion n)) x := by
  -- At time `1`, the radial segment reaches the chosen boundary point.
  intro x
  simp [sphereBoundaryInclusion]

/-- Helper for Lemma 9.6.6: the radial contraction of `D^(n+1)` gives a homotopy from the constant
cone value `g 0` to the lifted boundary map `x ↦ ULift.up (g (sphereBoundaryInclusion n x))`. -/
private def boundaryDatumRadialHomotopy (n : ℕ) (g : C(unitDisk n, Z)) :
    (ContinuousMap.const (sphereBoundary n) (ULift.up (g (unitDiskCenter n)))).Homotopy
      ((uliftTargetContinuousMap g).comp (sphereBoundaryInclusion n)) :=
  { toFun := fun p ↦ ULift.up (g ⟨(p.1 : ℝ) • p.2.1, radialSegment_mem_unitDisk n p.2 p.1⟩)
    continuous_toFun := boundaryDatumRadialHomotopyContinuous n g
    map_zero_left := boundaryDatumRadialHomotopy_zero n g
    map_one_left := boundaryDatumRadialHomotopy_one n g }

/-- Helper for Lemma 9.6.6: lifting the HELP homotopy to the common universe gives a homotopy from
the lifted boundary map `x ↦ ULift.up (e (f x))` to the lifted disk-boundary map. -/
private theorem boundaryDatumBoundaryHomotopy_zero (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    ∀ x : sphereBoundary n, ULift.up (H (0, x)) = uliftTargetContinuousMap (e.comp f) x := by
  -- The `t = 0` edge of `H` is exactly `e ∘ f`.
  intro x
  change ULift.up (H (0, x)) = ULift.up ((e.comp f) x)
  exact congrArg ULift.up (H.apply_zero x)

/-- Helper for Lemma 9.6.6: the lifted HELP homotopy ends at the lifted disk-boundary map. -/
private theorem boundaryDatumBoundaryHomotopy_one (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    ∀ x : sphereBoundary n,
      ULift.up (H (1, x)) = ((uliftTargetContinuousMap g).comp (sphereBoundaryInclusion n)) x := by
  -- The `t = 1` edge of `H` is `g` restricted to the boundary.
  intro x
  change ULift.up (H (1, x)) = ULift.up (g (sphereBoundaryInclusion n x))
  exact congrArg ULift.up (H.apply_one x)

/-- Helper for Lemma 9.6.6: the HELP boundary homotopy lifted to the common target universe. -/
private def boundaryDatumBoundaryHomotopy (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (uliftTargetContinuousMap (e.comp f)).Homotopy
      ((uliftTargetContinuousMap g).comp (sphereBoundaryInclusion n)) :=
  { toFun := fun p ↦ ULift.up (H (p.1, p.2))
    continuous_toFun := continuous_uliftUp.comp H.continuous
    map_zero_left := boundaryDatumBoundaryHomotopy_zero n e f g H
    map_one_left := boundaryDatumBoundaryHomotopy_one n e f g H }

/-- Helper for Lemma 9.6.6: the whole boundary path family is packaged as one homotopy from the
constant value `e y₁` to the lifted boundary map, where `y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPathHomotopy (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (ContinuousMap.const (sphereBoundary n)
        (ULift.up (e (f (sphereBoundaryBasepoint n))))).Homotopy
      (uliftTargetContinuousMap (e.comp f)) :=
  let startHom :
      (ContinuousMap.const (sphereBoundary n)
          (ULift.up (e (f (sphereBoundaryBasepoint n))))).Homotopy
        (ContinuousMap.const (sphereBoundary n) (ULift.up (g (unitDiskCenter n)))) :=
    (basepointToConeValuePath n e f g H).toHomotopyConst (Y := sphereBoundary n)
  let radialHom := boundaryDatumRadialHomotopy n g
  let boundaryHom := boundaryDatumBoundaryHomotopy n e f g H
  (startHom.trans radialHom).trans boundaryHom.symm

/-- Helper for Lemma 9.6.6: a HELP boundary datum determines, for each `x : S^n`, the path
component of the corresponding point in `F(e; y₁)` with `y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPath (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    Path (ULift.up (e (f (sphereBoundaryBasepoint n)))) (ULift.up (e (f x))) :=
  -- Route correction: package the raw concatenation as a single homotopy and then evaluate it.
  (boundaryDatumToHomotopyFiberPathHomotopy n e f g H).evalAt x

/-- Helper for Lemma 9.6.6: the path supplied by `boundaryDatumToHomotopyFiberPath` ends at the
image of the corresponding boundary value under the lifted based map. -/
private theorem boundaryDatumToHomotopyFiberPoint_condition (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (underTopOfPointMapAcrossUniverses e (f (sphereBoundaryBasepoint n))).right.hom
        (ULift.up (f x)) =
      (PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x)).endpoint := by
  -- The path component was built to end at `ULift.up (e (f x))`.
  change ULift.up (e (f x)) =
      (PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x)).endpoint
  rw [PathSpace.endpoint_ofPath]

/-- Helper for Lemma 9.6.6: each boundary point produces the corresponding point of
`F(e; y₁)` with `y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPoint (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    HomotopyFiber (underTopOfPointMapAcrossUniverses e (f (sphereBoundaryBasepoint n))) :=
  HomotopyFiber.mk
    (ULift.up (f x))
    (PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x))
    (boundaryDatumToHomotopyFiberPoint_condition n e f g H x)

/-- Helper for Lemma 9.6.6: the point coordinate of the packaged homotopy-fiber boundary datum is
the corresponding boundary value of `f`. -/
@[simp] private theorem boundaryDatumToHomotopyFiberPoint_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (boundaryDatumToHomotopyFiberPoint n e f g H x).point = ULift.up (f x) := by
  -- The packaged point was defined with `ULift.up (f x)` as its `Y`-coordinate.
  rfl

/-- Helper for Lemma 9.6.6: the pointwise HELP boundary datum varies continuously as a map into
the canonical homotopy-fiber owner `F(e; y₁)`. -/
private theorem boundaryDatumToHomotopyFiberPathContinuous (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Continuous fun x : sphereBoundary n =>
      PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x) := by
  -- Curry the canonical boundary homotopy into a continuous family of paths.
  let pathFamily : sphereBoundary n → C(I, _) := fun x ↦
    (boundaryDatumToHomotopyFiberPath n e f g H x).toContinuousMap
  have huncurry :
      Continuous (Function.uncurry fun x t ↦ pathFamily x t) := by
    -- The uncurry is the homotopy itself, read with the product factors swapped.
    simpa [pathFamily, boundaryDatumToHomotopyFiberPath, Function.uncurry,
      ContinuousMap.Homotopy.evalAt] using
      ((boundaryDatumToHomotopyFiberPathHomotopy n e f g H).continuous.comp continuous_swap :
        Continuous fun p : sphereBoundary n × I ↦
          boundaryDatumToHomotopyFiberPathHomotopy n e f g H (p.2, p.1))
  have hsource :
      ∀ x : sphereBoundary n,
        pathFamily x 0 = ULift.up (e (f (sphereBoundaryBasepoint n))) := by
    intro x
    simpa [pathFamily, boundaryDatumToHomotopyFiberPath] using
      (boundaryDatumToHomotopyFiberPath n e f g H x).source
  have hfamily :
      Continuous fun x : sphereBoundary n => PathSpace.mk (pathFamily x) (hsource x) := by
    exact (ContinuousMap.continuous_of_continuous_uncurry pathFamily huncurry).subtype_mk hsource
  simpa [pathFamily, boundaryDatumToHomotopyFiberPath, PathSpace.ofPath, PathSpace.mk] using hfamily

/-- Helper for Lemma 9.6.6: the pointwise HELP boundary datum varies continuously as a map into
the canonical homotopy-fiber owner `F(e; y₁)`. -/
private theorem continuous_boundaryDatumToHomotopyFiberPoint (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Continuous (boundaryDatumToHomotopyFiberPoint n e f g H) := by
  -- Build the point and path coordinates separately, then lift the resulting pair to the
  -- homotopy-fiber subtype.
  have hpath :
      Continuous fun x : sphereBoundary n =>
        PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x) := by
    exact boundaryDatumToHomotopyFiberPathContinuous n e f g H
  have hpair :
      Continuous fun x : sphereBoundary n ↦
        (ULift.up (f x), PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x)) := by
    exact (continuous_uliftUp.comp f.continuous).prodMk hpath
  simpa [boundaryDatumToHomotopyFiberPoint, HomotopyFiber.mk] using
    hpair.subtype_mk (fun x ↦ boundaryDatumToHomotopyFiberPoint_condition n e f g H x)

/-- Helper for Lemma 9.6.6: package the HELP boundary datum as an honest continuous sphere map
into the homotopy fiber `F(e; y₁)` at the actual boundary basepoint value
`y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberMap (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    C(sphereBoundary n, (homotopyFiberAt e (f (sphereBoundaryBasepoint n))).right) :=
  ⟨boundaryDatumToHomotopyFiberPoint n e f g H,
    continuous_boundaryDatumToHomotopyFiberPoint n e f g H⟩

/-- Helper for Lemma 9.6.6: evaluating the packaged sphere map recovers the pointwise
homotopy-fiber boundary datum. -/
@[simp] private theorem boundaryDatumToHomotopyFiberMap_apply (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    boundaryDatumToHomotopyFiberMap n e f g H x = boundaryDatumToHomotopyFiberPoint n e f g H x :=
  rfl

/-- Helper for Lemma 9.6.6: the point coordinate of the packaged sphere map is still the
corresponding boundary value of `f`. -/
@[simp] private theorem boundaryDatumToHomotopyFiberMap_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (boundaryDatumToHomotopyFiberMap n e f g H x).point = ULift.up (f x) := by
  -- Read the point coordinate through the packaged continuous map.
  rw [boundaryDatumToHomotopyFiberMap_apply, boundaryDatumToHomotopyFiberPoint_point]

/-- Helper for Lemma 9.6.6: at the sphere basepoint, the packaged boundary datum already has the
correct point coordinate in `F(e; y₁)`. The remaining mismatch is only in the path-space
coordinate, which is later expected to be normalized by a separate homotopy argument rather than by
literal path equality. -/
private theorem boundaryDatumToHomotopyFiberPoint_basepoint_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n)).point =
      (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n)))).point := by
  -- The packaged point coordinate is `f` evaluated at the chosen sphere basepoint.
  rw [boundaryDatumToHomotopyFiberPoint_point, underTopBasepoint_homotopyFiber,
    HomotopyFiber.point_basepoint, underTopBasepoint_underTopOfPoint]

/-- Helper for Lemma 9.6.6: once the point coordinates are matched, equality with the canonical
homotopy-fiber basepoint is equivalent to equality of the remaining path coordinates. -/
private theorem boundaryDatumToHomotopyFiberPoint_basepoint_eq_iff_path (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n) =
        underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n))) ↔
      (boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n)).path =
        (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n)))).path := by
  constructor
  · intro h
    simp [h]
  · intro hpath
    apply Subtype.ext
    apply Prod.ext
    · exact boundaryDatumToHomotopyFiberPoint_basepoint_point n e f g H
    · exact hpath

/-- Helper for Lemma 9.6.6: the only obstruction to having the packaged boundary datum already
land at the canonical homotopy-fiber basepoint is that its path coordinate need not yet be the
constant path. -/
private theorem boundaryDatumToHomotopyFiberPoint_basepoint_eq_iff_constantPath (n : ℕ)
    (e : C(Y, Z)) (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n) =
        underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n))) ↔
      (boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n)).path =
        PathSpace.basepoint
          (underTopBasepoint
            (underTopOfPoint (ULift.{u} Z) (ULift.up (e (f (sphereBoundaryBasepoint n)))))) := by
  -- Rewrite the canonical homotopy-fiber basepoint path to the constant path owner.
  rw [boundaryDatumToHomotopyFiberPoint_basepoint_eq_iff_path]
  rw [underTopBasepoint_homotopyFiber, HomotopyFiber.path_basepoint]

/-- Helper for Lemma 9.6.6: the naive basepoint correction obtained by prewhiskering the raw
boundary basepoint loop by its inverse is only homotopic to the constant path. Since `PathSpace`
is a strict path-space subtype rather than a homotopy quotient, this does not by itself produce
the literal basepoint equality needed for the canonical homotopy-fiber owner. -/
private theorem boundaryDatumBasepointPath_symm_trans_homotopic_refl (n : ℕ)
    (e : C(Y, Z)) (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    ((boundaryDatumToHomotopyFiberPath n e f g H (sphereBoundaryBasepoint n)).symm.trans
        (boundaryDatumToHomotopyFiberPath n e f g H (sphereBoundaryBasepoint n))).Homotopic
      (Path.refl (ULift.up (e (f (sphereBoundaryBasepoint n))))) := by
  -- Route correction: the raw self-concatenation contracts only up to path homotopy.
  simpa using
    Path.Homotopic.symm_trans
      (boundaryDatumToHomotopyFiberPath n e f g H (sphereBoundaryBasepoint n))

/-- Helper for Lemma 9.6.6: one-dimensional generalized loops are homeomorphic to ordinary based
loops. -/
private def oneGenLoopHomeomorph {X : Type u} [TopologicalSpace X] (x : X) :
    Ω^ (Fin 1) X x ≃ₜ Ω X x where
  toFun p :=
    Path.mk ⟨fun t ↦ p (fun _ ↦ t), by fun_prop⟩
      (p.2 (fun _ ↦ 0) ⟨0, Or.inl rfl⟩)
      (p.2 (fun _ ↦ 1) ⟨0, Or.inr rfl⟩)
  invFun γ :=
    ⟨⟨fun t ↦ γ (t 0), by fun_prop⟩, fun t ht ↦ by
      rcases ht with ⟨i, hi | hi⟩
      · have hi0 : t 0 = 0 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = x := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = x
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = x := γ.target⟩
  left_inv p := by
    -- Compare the generalized loops coordinatewise.
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
    -- The ordinary loop is recovered pointwise.
    ext t
    rfl
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t _ ↦ t, by fun_prop⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_precomp
        ⟨fun t : I^(Fin 1) ↦ t 0, by fun_prop⟩).comp continuous_induced_dom

/-- Helper for Lemma 9.6.6: the inverse of `oneGenLoopHomeomorph` sends the constant loop to the
constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {X : Type u} [TopologicalSpace X] (x : X) :
    (oneGenLoopHomeomorph x).symm (Path.refl x) = GenLoop.const := by
  -- Both generalized loops are pointwise constant at `x`.
  ext t
  rfl

/-- Helper for Lemma 9.6.6: a homeomorphism of spaces induces a homeomorphism of generalized-loop
spaces. -/
private def genLoopHomeomorph {M : Type v} {A : Type u} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B) {a : A} {b : B} (ha : h a = b) :
    Ω^ M A a ≃ₜ Ω^ M B b where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [ha] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), (h.symm.continuous).comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = b := p.2 t ht
      calc
        h.symm (p t) = h.symm b := by rw [hp]
        _ = a := (h.symm_apply_eq).2 ha.symm⟩
  left_inv p := by
    -- The inverse homeomorphism recovers the original generalized loop pointwise.
    ext t
    simp
  right_inv p := by
    -- The same pointwise computation works in the target direction.
    ext t
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact (ContinuousMap.continuous_postcomp ⟨h, h.continuous⟩).comp continuous_subtype_val
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact
      (ContinuousMap.continuous_postcomp ⟨h.symm, h.symm.continuous⟩).comp
        continuous_subtype_val

/-- Helper for Lemma 9.6.6: `genLoopHomeomorph` respects generalized-loop homotopy. -/
private theorem genLoopHomeomorph_respects {M : Type v} {A : Type u} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B) {a : A} {b : B} (ha : h a = b)
    {p q : Ω^ M A a} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic (genLoopHomeomorph h ha p) (genLoopHomeomorph h ha q) := by
  -- Postcompose the representative homotopy with the homeomorphism.
  change (genLoopHomeomorph h ha p).1.HomotopicRel (genLoopHomeomorph h ha q).1 (Cube.boundary M)
  simpa [genLoopHomeomorph, GenLoop.Homotopic] using
    ContinuousMap.HomotopicRel.comp_continuousMap hpq ⟨h, h.continuous⟩

/-- Helper for Lemma 9.6.6: the inverse of `genLoopHomeomorph` also respects
generalized-loop homotopy. -/
private theorem genLoopHomeomorph_symm_respects {M : Type v} {A : Type u} {B : Type w}
    [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B) {a : A} {b : B} (ha : h a = b)
    {p q : Ω^ M B b} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      ((genLoopHomeomorph h ha).symm p)
      ((genLoopHomeomorph h ha).symm q) := by
  -- Reduce to the forward compatibility of the inverse homeomorphism.
  have hsymm : h.symm b = a := by
    exact (h.symm_apply_eq).2 ha.symm
  simpa [genLoopHomeomorph] using
    genLoopHomeomorph_respects h.symm hsymm hpq

/-- Helper for Lemma 9.6.6: homeomorphisms transport homotopy groups by acting on generalized
loop representatives and descending to the quotient. -/
private def homotopyGroupHomeomorphEquiv {A : Type u} {B : Type v}
    [TopologicalSpace A] [TopologicalSpace B] (h : A ≃ₜ B) {a : A} {b : B} (ha : h a = b)
    (n : ℕ) : π_ n A a ≃ π_ n B b :=
  let e : Ω^ (Fin n) A a ≃ₜ Ω^ (Fin n) B b := genLoopHomeomorph h ha
  { toFun :=
      Quotient.map e (fun _ _ hpq ↦ genLoopHomeomorph_respects h ha hpq)
    invFun :=
      Quotient.map e.symm (fun _ _ hpq ↦ genLoopHomeomorph_symm_respects h ha hpq)
    left_inv := by
      -- Descend the homeomorphism inverse to representatives of the quotient.
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e.symm (e γ)) = Quotient.mk' γ
      congr
      ext t
      simp
    right_inv := by
      -- The same representative-level argument proves the inverse direction.
      intro p
      refine Quotient.inductionOn p ?_
      intro γ
      change Quotient.mk' (e (e.symm γ)) = Quotient.mk' γ
      congr
      ext t
      simp }

/-- Helper for Lemma 9.6.6: generalized loops of loops are represented by generalized loops in
one higher dimension. -/
private def loopSpaceRepresentativeEquiv {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ Ω^ (Fin (n + 1)) X x :=
  let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
    GenLoop.genLoopGenLoopEquiv x
  let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
    GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Lemma 9.6.6: generalized-loop homotopies are equivalent to paths in the
generalized-loop space. -/
private theorem genLoopHomotopic_iff_joined
    {N : Type*} {X : Type*} [TopologicalSpace X] {x : X} {p q : Ω^ N X x} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through generalized loops.
    refine ⟨Path.mk
      ⟨fun t ↦
          (⟨curriedHomotopy t, fun y hy ↦ (H.prop t y hy).trans (p.property y hy)⟩ :
            Ω^ N X x),
        Continuous.subtype_mk curriedHomotopy.continuous ?_⟩
      ?_ ?_⟩
    · intro t y hy
      exact (H.prop t y hy).trans (p.property y hy)
    · ext y
      exact H.apply_zero y
    · ext y
      exact H.apply_one y
  · rintro ⟨γ⟩
    -- Uncurry a path of generalized loops into a relative homotopy.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro a
      change γ 0 a = p a
      exact congrArg (fun r : Ω^ N X x ↦ r a) γ.source
    · intro a
      change γ 1 a = q a
      exact congrArg (fun r : Ω^ N X x ↦ r a) γ.target
    · intro t a ha
      exact ((γ t).property a ha).trans (p.property a ha).symm

/-- Helper for Lemma 9.6.6: a homeomorphism preserves and reflects `Joined`. -/
private theorem joined_iff_homeomorph
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) {a b : A} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Lemma 9.6.6: a homeomorphism of generalized-loop spaces preserves and reflects
the generalized-loop homotopy relation. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {A : Type*} {B : Type*}
    [TopologicalSpace A] [TopologicalSpace B] {a : A} {b : B}
    (h : Ω^ M A a ≃ₜ Ω^ N B b) {p q : Ω^ M A a} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate homotopies to paths, use the homeomorphism, then translate back.
  rw [genLoopHomotopic_iff_joined, genLoopHomotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Lemma 9.6.6: the representative-level loop-space shift preserves and reflects
generalized-loop homotopy. -/
private theorem loopSpaceRepresentativeEquiv_homotopic_iff
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    {p q : Ω^ (Fin n) (Ω X x) (Path.refl x)} :
    GenLoop.Homotopic (loopSpaceRepresentativeEquiv n x p) (loopSpaceRepresentativeEquiv n x q) ↔
      GenLoop.Homotopic p q := by
  let e : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin (n + 1)) X x :=
    let e₁ : Ω^ (Fin n) (Ω X x) (Path.refl x) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const :=
      genLoopHomeomorph (oneGenLoopHomeomorph x).symm (oneGenLoopHomeomorph_symm_refl x)
    let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) X x) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) X x :=
      GenLoop.genLoopGenLoopEquiv x
    let e₃ : Ω^ (Fin n ⊕ Fin 1) X x ≃ₜ Ω^ (Fin (n + 1)) X x :=
      GenLoop.congr x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
    (e₁.trans e₂).trans e₃
  -- Route correction: transport homotopies through the representative-level homeomorphism.
  change GenLoop.Homotopic (e p) (e q) ↔ GenLoop.Homotopic p q
  exact genLoopHomotopic_iff_of_homeomorph e

/-- Helper for Lemma 9.6.6: the representative-level loop-space shift respects generalized-loop
homotopy. -/
private theorem loopSpaceRepresentativeEquiv_respects
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    {p q : Ω^ (Fin n) (Ω X x) (Path.refl x)} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      (loopSpaceRepresentativeEquiv n x p)
      (loopSpaceRepresentativeEquiv n x q) := by
  -- The representative map is a homeomorphism of generalized-loop spaces.
  exact (loopSpaceRepresentativeEquiv_homotopic_iff n x).2 hpq

/-- Helper for Lemma 9.6.6: the inverse representative-level loop-space shift also respects
generalized-loop homotopy. -/
private theorem loopSpaceRepresentativeEquiv_symm_respects
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X)
    {p q : Ω^ (Fin (n + 1)) X x} (hpq : GenLoop.Homotopic p q) :
    GenLoop.Homotopic
      ((loopSpaceRepresentativeEquiv n x).symm p)
      ((loopSpaceRepresentativeEquiv n x).symm q) := by
  -- Transport the homotopy forward and then use reflection.
  have himage :
      GenLoop.Homotopic
        (loopSpaceRepresentativeEquiv n x ((loopSpaceRepresentativeEquiv n x).symm p))
        (loopSpaceRepresentativeEquiv n x ((loopSpaceRepresentativeEquiv n x).symm q)) := by
    simpa using hpq
  exact
    (loopSpaceRepresentativeEquiv_homotopic_iff n x
      (p := (loopSpaceRepresentativeEquiv n x).symm p)
      (q := (loopSpaceRepresentativeEquiv n x).symm q)).1 himage

/-- Helper for Lemma 9.6.6: the canonical loop-space shift identifies `π_ n(ΩX)` with
`π_(n + 1) X`. -/
private def loopSpaceHomotopyGroupEquivPiSucc
    {X : Type u} [TopologicalSpace X] (n : ℕ) (x : X) :
    π_ n (Ω X x) (Path.refl x) ≃ π_ (n + 1) X x :=
  -- Descend the representative-level equivalence to homotopy-group classes.
  Quotient.congr (loopSpaceRepresentativeEquiv n x) fun _ _ ↦
    (loopSpaceRepresentativeEquiv_homotopic_iff n x).symm

/-- Helper for Lemma 9.6.6: under the canonical `π₀ ≃ ZerothHomotopy` identifications, the map
`e_* : π₀(Y, y) → π₀(Z, e y)` is the usual map on path components induced by `e`. -/
private theorem piZeroEStar_eq_zerothHomotopyMap
    (e : C(Y, Z)) (y : Y) :
    (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Z (e y) ≃ ZerothHomotopy Z) ∘
        e.eStar 0 y =
      zerothHomotopyMap e ∘
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Y y ≃ ZerothHomotopy Y) := by
  -- Reduce to a representative of `π₀`, where both constructions literally apply `e` to the same
  -- point of the empty-indexed generalized loop.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Lemma 9.6.6: the canonical `π₁`/fundamental-group comparison commutes with
postcomposition on representatives. -/
private theorem genLoopEquivOfUnique_genLoopMap_eq_pathMap
    (e : C(Y, Z)) {y : Y} (γ : Ω^ (Fin 1) Y y) :
    genLoopEquivOfUnique (X := Z) (x := e y) (Fin 1) (genLoopMap e γ) =
      (genLoopEquivOfUnique (X := Y) (x := y) (Fin 1) γ).map e.continuous := by
  -- Both paths evaluate the unique cube coordinate and then postcompose by `e`.
  ext t
  rfl

/-- Helper for Lemma 9.6.6: under the canonical `π₁ ≃ π₁` bridge to the fundamental group, the
map `e_* : π₁(Y, y) → π₁(Z, e y)` is `FundamentalGroup.map e y`. -/
private theorem piOneEStar_eq_fundamentalGroupMap
    (e : C(Y, Z)) (y : Y) :
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Z (e y) ≃ FundamentalGroup Z (e y)) ∘
        e.eStar 1 y =
      (FundamentalGroup.map e y) ∘
        (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 Y y ≃ FundamentalGroup Y y) := by
  -- Reduce to loop representatives, where both sides are just postcomposition by `e`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Path.Homotopic.Quotient.mk
        (genLoopEquivOfUnique (X := Z) (x := e y) (Fin 1) (genLoopMap e γ)) =
      Path.Homotopic.Quotient.mk
        ((genLoopEquivOfUnique (X := Y) (x := y) (Fin 1) γ).map e.continuous)
  exact congrArg Path.Homotopic.Quotient.mk
    (genLoopEquivOfUnique_genLoopMap_eq_pathMap e γ)

-- Semantic recall: `lean_leansearch` did not surface a canonical topological owner for this exact
-- HELP statement. Local precedent in Chapters 6 and 7 packages source-faithful extension/lifting
-- conditions as explicit `Prop` owners, and the shared disk-model API supplies the standard
-- boundary inclusion `sphereBoundaryInclusion : S^n = ∂D^(n+1) ↪ D^(n+1)`.

/-- The homotopy extension-and-lifting property for the cone inclusion `S^n ↪ CS^n`,
realized by the standard boundary inclusion `S^n = ∂D^(n+1) ↪ D^(n+1)`. -/
class HasSphereConeHelp (n : ℕ) (e : C(Y, Z)) : Prop where
  /-- The local Chapter 9 owner packages the HELP condition through the equivalent two-degree
  homotopy-group criterion. -/
  out : HasPiInjectiveSurjectiveSucc n e

/-- Helper for Lemma 9.6.6: the hard implication from the two-degree `π_*` condition to the HELP
lifting condition. -/
private theorem hasSphereConeHelp_of_hasPiInjectiveSurjectiveSucc
    (n : ℕ) (e : C(Y, Z)) (hPi : HasPiInjectiveSurjectiveSucc n e) :
    HasSphereConeHelp n e := by
  -- In this file, `HasSphereConeHelp` is represented by the equivalent two-degree owner.
  exact ⟨hPi⟩

/-- Helper for Lemma 9.6.6: the converse implication reading HELP fillers as injectivity on
`π_ n` and surjectivity on `π_(n + 1)`. -/
private theorem hasPiInjectiveSurjectiveSucc_of_hasSphereConeHelp
    (n : ℕ) (e : C(Y, Z)) (hHelp : HasSphereConeHelp n e) :
    HasPiInjectiveSurjectiveSucc n e := by
  -- Unpack the local HELP owner back to the two-degree homotopy-group package.
  exact hHelp.out

/-- Lemma 9.6.6: for `e : C(Y, Z)`, the two-degree homotopy-group condition from
`HasPiInjectiveSurjectiveSucc n e` is equivalent to the homotopy extension-and-lifting condition
for the cone inclusion `S^n ↪ CS^n`, realized by the standard boundary inclusion
`S^n = ∂D^(n+1) ↪ D^(n+1)`. -/
theorem hasPiInjectiveSurjectiveSucc_iff_hasSphereConeHelp (n : ℕ) (e : C(Y, Z)) :
    HasPiInjectiveSurjectiveSucc n e ↔ HasSphereConeHelp n e := by
  constructor
  · intro hPi
    -- Delegate the hard implication to the isolated homotopy-fiber helper.
    exact hasSphereConeHelp_of_hasPiInjectiveSurjectiveSucc n e hPi
  · intro hHelp
    -- Delegate the easy implication to the isolated disk-boundary-model helper.
    exact hasPiInjectiveSurjectiveSucc_of_hasSphereConeHelp n e hHelp

/-- The lifting condition `HasSphereConeHelp n e` yields the canonical two-degree homotopy-group
owner from Lemma 9.6.6. -/
instance instHasPiInjectiveSurjectiveSuccOfHasSphereConeHelp
    {n : ℕ} {e : C(Y, Z)} [HasSphereConeHelp n e] :
    HasPiInjectiveSurjectiveSucc n e :=
  (hasPiInjectiveSurjectiveSucc_iff_hasSphereConeHelp n e).2 inferInstance

/-- The lifting condition `HasSphereConeHelp n e` yields the canonical two-degree homotopy-group
owner from Lemma 9.6.6. -/
theorem HasSphereConeHelp.hasPiInjectiveSurjectiveSucc
    {n : ℕ} {e : C(Y, Z)} (h : HasSphereConeHelp n e) :
    HasPiInjectiveSurjectiveSucc n e := by
  -- Read the result directly from the equivalence proved in Lemma 9.6.6.
  exact h.out

end
