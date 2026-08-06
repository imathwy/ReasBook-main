import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.RelativeHelp

universe u v w uA

open Set
open scoped TopCat Topology unitInterval Topology.Homotopy

noncomputable section

-- Semantic recall via `lean_leansearch`: no single canonical mathlib theorem surfaced for this
-- relative HELP statement, so the source is recorded directly using the local owners
-- `Topology.RelCWComplex.dimLE` and `IsNEquivalence`.

variable {W : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace W] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The canonical inclusion of the base `A` into the ambient subspace `X` of a relative CW
complex. -/
abbrev relCWComplexBaseInclusion (X : Set W) {A : Set W} [Topology.RelCWComplex X A] : C(A, X) :=
  ContinuousMap.inclusion Topology.RelCWComplex.base_subset_complex

/-- Helper for Theorem 10.3.1: an `n`-equivalence provides sphere-cone HELP in every smaller
degree. -/
private theorem isNEquivalence_of_le
    {n m : ℕ} (e : C(Y, Z)) [IsNEquivalence n e] (hmn : m ≤ n) :
    IsNEquivalence m e := by
  refine
    { injectiveBelow := ?_
      surjectiveUpTo := ?_ }
  · intro y q hq
    -- Restrict the ambient injectivity range from `q < n` to the smaller degree `m ≤ n`.
    exact IsNEquivalence.injective (inferInstance : IsNEquivalence n e) y
      (Nat.lt_of_lt_of_le hq hmn)
  · intro y q hq
    -- Restrict the ambient surjectivity range from `q ≤ n` to the smaller degree `m ≤ n`.
    exact IsNEquivalence.surjective (inferInstance : IsNEquivalence n e) y
      (Nat.le_trans hq hmn)

/-- Helper for Theorem 10.3.1: the two-degree Chapter 9 `π_*` package is available in every
smaller degree of an `n`-equivalence. -/
private theorem hasPiInjectiveSurjectiveSucc_of_isNEquivalence_of_succ_le
    {n m : ℕ} (e : C(Y, Z)) [IsNEquivalence n e] (hmn : m + 1 ≤ n) :
    HasPiInjectiveSurjectiveSucc m e := by
  -- First truncate the ambient `n`-equivalence to degree `m + 1`.
  let _ : IsNEquivalence (m + 1) e :=
    isNEquivalence_of_le e hmn
  -- Then use the canonical Chapter 9 instance converting `(m + 1)`-equivalence data.
  infer_instance

/-- Helper for Theorem 10.3.1: every cell dimension allowed by an `n`-equivalence carries the
sphere-cone HELP package from Lemma 9.6.6. -/
private theorem hasSphereConeHelp_of_isNEquivalence_of_succ_le
    {n m : ℕ} (e : C(Y, Z)) [IsNEquivalence n e] (hmn : m + 1 ≤ n) :
    HasSphereConeHelp m e := by
  -- First convert the truncated `n`-equivalence into the Chapter 9 two-degree `π_*` owner.
  let hPi : HasPiInjectiveSurjectiveSucc m e :=
    hasPiInjectiveSurjectiveSucc_of_isNEquivalence_of_succ_le e hmn
  -- Then rewrite that owner through Lemma 9.6.6 into sphere-cone HELP.
  exact (hasPiInjectiveSurjectiveSucc_iff_hasSphereConeHelp m e).1 hPi

/-- Helper for Theorem 10.3.1: in a relative CW complex of dimension at most `n`, every point of
`X` already lies either in the base `A` or in a closed relative cell of dimension at most `n`. -/
private theorem mem_base_or_mem_closedCell_of_dimLE
    {X A : Set W} [T2Space W] [Topology.RelCWComplex X A] {n : ℕ}
    {x : W} (h_dim : Topology.RelCWComplex.dimLE X n) (hx : x ∈ X) :
    x ∈ A ∨
      ∃ (m : ℕ) (_ : m ≤ n) (j : Topology.RelCWComplex.cell X m),
        x ∈ Topology.RelCWComplex.closedCell m j := by
  have hCover :
      (A ∪ ⋃ (m : ℕ) (_ : m ≤ n) (j : Topology.RelCWComplex.cell X m),
          Topology.RelCWComplex.closedCell m j) = X :=
    (Topology.RelCWComplex.dimLE_iff_base_union_iUnion_closedCell X n).1 h_dim
  have hxCover :
      x ∈ A ∪ ⋃ (m : ℕ) (_ : m ≤ n) (j : Topology.RelCWComplex.cell X m),
        Topology.RelCWComplex.closedCell m j := by
    rw [hCover]
    exact hx
  rcases hxCover with hxA | hxCells
  · exact Or.inl hxA
  · simp only [mem_iUnion] at hxCells
    rcases hxCells with ⟨m, hm, j, hxj⟩
    exact Or.inr ⟨m, hm, j, hxj⟩

/-- Helper for Theorem 10.3.1: the target space `Z` lifted into the common universe used by the
homotopy-fiber model. -/
private def uliftTarget : C(Z, ULift.{u} Z) :=
  ⟨ULift.up, continuous_uliftUp⟩

/-- Helper for Theorem 10.3.1: postcomposing a continuous map with `uliftTarget` lifts its target
to the common universe used by `homotopyFiberAt`. -/
private def uliftTargetContinuousMap {A : Type uA} [TopologicalSpace A] (g : C(A, Z)) :
    C(A, ULift.{u} Z) :=
  uliftTarget.comp g

/-- Helper for Theorem 10.3.1: the radial segment from the disk center to `x` stays inside
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

/-- Helper for Theorem 10.3.1: the radial segment gives a continuous map from `I` into
`D^(n+1)`. -/
private def radialSegmentContinuousMap (n : ℕ) (x : sphereBoundary n) : C(I, unitDisk n) :=
  ⟨fun t ↦ ⟨(t : ℝ) • x.1, radialSegment_mem_unitDisk n x t⟩, by fun_prop⟩

/-- Helper for Theorem 10.3.1: the cone point of the disk model `D^(n+1)`, realized by the
origin. -/
private def unitDiskCenter (n : ℕ) : unitDisk n :=
  ⟨0, by simp [mem_unitDisk_iff]⟩

/-- Helper for Theorem 10.3.1: the radial segment starts at the cone point of the disk model. -/
private theorem radialSegment_zero (n : ℕ) (x : sphereBoundary n) :
    radialSegmentContinuousMap n x 0 = unitDiskCenter n := by
  -- At time `0`, scalar multiplication collapses the segment to the origin.
  apply Subtype.ext
  simp [radialSegmentContinuousMap, unitDiskCenter]

/-- Helper for Theorem 10.3.1: the radial segment ends at the chosen boundary point. -/
private theorem radialSegment_one (n : ℕ) (x : sphereBoundary n) :
    radialSegmentContinuousMap n x 1 = sphereBoundaryInclusion n x := by
  -- At time `1`, the radial segment recovers the boundary inclusion.
  apply Subtype.ext
  simp [radialSegmentContinuousMap, sphereBoundaryInclusion]

/-- Helper for Theorem 10.3.1: the standard radial segment in `D^(n+1)` joins the cone point to a
boundary point of `S^n = ∂D^(n+1)`. -/
private def unitDiskRadialPathToBoundary (n : ℕ) (x : sphereBoundary n) :
    Path (unitDiskCenter n) (sphereBoundaryInclusion n x) :=
  Path.mk
    (radialSegmentContinuousMap n x)
    (radialSegment_zero n x)
    (radialSegment_one n x)

/-- Helper for Theorem 10.3.1: evaluating the boundary homotopy at a sphere point gives the
corresponding path in the lifted target. -/
private def helpBoundaryValuePath (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    Path (ULift.up (e (f x))) (ULift.up (g (sphereBoundaryInclusion n x))) :=
  (H.evalAt x).map uliftTarget.continuous

/-- Helper for Theorem 10.3.1: evaluating the boundary homotopy at the chosen sphere basepoint
and correcting by the radial disk path yields a path from `e y₁` to the cone value `g 0`. -/
private def basepointToConeValuePath (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Path (ULift.up (e (f (sphereBoundaryBasepoint n)))) (ULift.up (g (unitDiskCenter n))) :=
  (helpBoundaryValuePath n e f g H (sphereBoundaryBasepoint n)).trans
    (((unitDiskRadialPathToBoundary n (sphereBoundaryBasepoint n)).map
      (uliftTargetContinuousMap (A := unitDisk n) g).continuous).symm)

/-- Helper for Theorem 10.3.1: the radial contraction of `D^(n+1)` gives a homotopy from the
constant cone value `g 0` to the lifted boundary map. -/
private def boundaryDatumRadialHomotopy (n : ℕ) (g : C(unitDisk n, Z)) :
    (ContinuousMap.const (sphereBoundary n) (ULift.up (g (unitDiskCenter n)))).Homotopy
      ((uliftTargetContinuousMap (A := unitDisk n) g).comp (sphereBoundaryInclusion n)) :=
  { toFun := fun p ↦ ULift.up (g ⟨(p.1 : ℝ) • p.2.1, radialSegment_mem_unitDisk n p.2 p.1⟩)
    continuous_toFun := by
      -- The radial formula is continuous before applying the disk map `g`.
      fun_prop
    map_zero_left := by
      -- At time `0`, the radial segment is the cone point.
      intro x
      simp [unitDiskCenter]
    map_one_left := by
      -- At time `1`, the radial segment reaches the boundary inclusion.
      intro x
      have h :=
        congrArg (fun y : unitDisk n ↦ g y) (radialSegment_one n x)
      exact congrArg ULift.up h }

/-- Helper for Theorem 10.3.1: lifting the boundary homotopy to the common universe gives a
homotopy from the lifted boundary map `x ↦ ULift.up (e (f x))` to the lifted disk-boundary map.
-/
private def boundaryDatumBoundaryHomotopy (n : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary n, Y))
    (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (uliftTargetContinuousMap (A := sphereBoundary n) (e.comp f)).Homotopy
      ((uliftTargetContinuousMap (A := unitDisk n) g).comp (sphereBoundaryInclusion n)) :=
  { toFun := fun p ↦ ULift.up (H (p.1, p.2))
    continuous_toFun := continuous_uliftUp.comp H.continuous
    map_zero_left := by
      -- The `t = 0` edge of `H` is exactly `e ∘ f`.
      intro x
      change ULift.up (H (0, x)) = ULift.up ((e.comp f) x)
      exact congrArg ULift.up (H.apply_zero x)
    map_one_left := by
      -- The `t = 1` edge of `H` is the boundary restriction of `g`.
      intro x
      change ULift.up (H (1, x)) = ULift.up (g (sphereBoundaryInclusion n x))
      exact congrArg ULift.up (H.apply_one x) }

/-- Helper for Theorem 10.3.1: the whole boundary path family is packaged as one homotopy from
the constant value `e y₁` to the lifted boundary map, where
`y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPathHomotopy (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (ContinuousMap.const (sphereBoundary n)
        (ULift.up (e (f (sphereBoundaryBasepoint n))))).Homotopy
      (uliftTargetContinuousMap (A := sphereBoundary n) (e.comp f)) :=
  let startHom :
      (ContinuousMap.const (sphereBoundary n)
          (ULift.up (e (f (sphereBoundaryBasepoint n))))).Homotopy
        (ContinuousMap.const (sphereBoundary n) (ULift.up (g (unitDiskCenter n)))) :=
    (basepointToConeValuePath n e f g H).toHomotopyConst (Y := sphereBoundary n)
  -- Concatenate the constant-to-center path, the radial contraction, and the given boundary
  -- homotopy to obtain the full homotopy-fiber path family.
  ((startHom.trans (boundaryDatumRadialHomotopy n g)).trans
    (boundaryDatumBoundaryHomotopy n e f g H).symm)

/-- Helper for Theorem 10.3.1: the packaged boundary datum determines the path coordinate of the
corresponding point in `F(e; y₁)` with `y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPath (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    Path (ULift.up (e (f (sphereBoundaryBasepoint n)))) (ULift.up (e (f x))) :=
  -- Evaluate the packaged homotopy at the chosen sphere point.
  (boundaryDatumToHomotopyFiberPathHomotopy n e f g H).evalAt x

/-- Helper for Theorem 10.3.1: each boundary point produces the corresponding point of
`F(e; y₁)` with `y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberPoint (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (homotopyFiberAt e (f (sphereBoundaryBasepoint n))).right :=
  HomotopyFiber.mk
    (ULift.up (f x))
    (PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x))
    (by
      -- The packaged path was built to end at `ULift.up (e (f x))`.
      change ULift.up (e (f x)) =
          (PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x)).endpoint
      rw [PathSpace.endpoint_ofPath])

/-- Helper for Theorem 10.3.1: the point coordinate of the packaged homotopy-fiber boundary datum
is the corresponding boundary value of `f`. -/
@[simp] private theorem boundaryDatumToHomotopyFiberPoint_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (boundaryDatumToHomotopyFiberPoint n e f g H x).point = ULift.up (f x) := by
  -- The packaged point was defined with `ULift.up (f x)` as its `Y`-coordinate.
  rfl

/-- Helper for Theorem 10.3.1: the path supplied by `boundaryDatumToHomotopyFiberPath` ends at the
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

/-- Helper for Theorem 10.3.1: the path coordinate varies continuously as a path-space-valued
family. -/
private theorem boundaryDatumToHomotopyFiberPathContinuous (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Continuous fun x : sphereBoundary n =>
      PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x) := by
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
    -- Curry the continuous homotopy into a continuous family of based paths.
    exact (ContinuousMap.continuous_of_continuous_uncurry pathFamily huncurry).subtype_mk hsource
  simpa [pathFamily, boundaryDatumToHomotopyFiberPath, PathSpace.ofPath, PathSpace.mk] using hfamily

/-- Helper for Theorem 10.3.1: the pointwise boundary datum varies continuously as a map into the
canonical homotopy-fiber owner `F(e; y₁)`. -/
private theorem continuous_boundaryDatumToHomotopyFiberPoint (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Continuous (boundaryDatumToHomotopyFiberPoint n e f g H) := by
  have hpath :
      Continuous fun x : sphereBoundary n =>
        PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x) := by
    exact boundaryDatumToHomotopyFiberPathContinuous n e f g H
  have hpair :
      Continuous fun x : sphereBoundary n ↦
        (ULift.up (f x), PathSpace.ofPath (boundaryDatumToHomotopyFiberPath n e f g H x)) := by
    exact (continuous_uliftUp.comp f.continuous).prodMk hpath
  -- Build the point and path coordinates separately, then lift the resulting pair to the
  -- homotopy-fiber subtype.
  simpa [boundaryDatumToHomotopyFiberPoint, HomotopyFiber.mk] using
    hpair.subtype_mk (fun x ↦ boundaryDatumToHomotopyFiberPoint_condition n e f g H x)

/-- Helper for Theorem 10.3.1: package the boundary datum as an honest continuous sphere map into
the homotopy fiber `F(e; y₁)` at the actual boundary basepoint value
`y₁ := f (sphereBoundaryBasepoint n)`. -/
private def boundaryDatumToHomotopyFiberMap (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    C(sphereBoundary n, (homotopyFiberAt e (f (sphereBoundaryBasepoint n))).right) :=
  ⟨boundaryDatumToHomotopyFiberPoint n e f g H,
    continuous_boundaryDatumToHomotopyFiberPoint n e f g H⟩

/-- Helper for Theorem 10.3.1: evaluating the packaged sphere map recovers the pointwise
homotopy-fiber boundary datum. -/
@[simp] private theorem boundaryDatumToHomotopyFiberMap_apply (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    boundaryDatumToHomotopyFiberMap n e f g H x = boundaryDatumToHomotopyFiberPoint n e f g H x :=
  rfl

/-- Helper for Theorem 10.3.1: the point coordinate of the packaged sphere map is still the
corresponding boundary value of `f`. -/
@[simp] private theorem boundaryDatumToHomotopyFiberMap_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) (x : sphereBoundary n) :
    (boundaryDatumToHomotopyFiberMap n e f g H x).point = ULift.up (f x) := by
  -- Read the point coordinate through the packaged continuous map.
  rw [boundaryDatumToHomotopyFiberMap_apply, boundaryDatumToHomotopyFiberPoint_point]

/-- Helper for Theorem 10.3.1: at the sphere basepoint, the packaged boundary datum already has
the correct point coordinate in `F(e; y₁)`. -/
private theorem boundaryDatumToHomotopyFiberPoint_basepoint_point (n : ℕ) (e : C(Y, Z))
    (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (boundaryDatumToHomotopyFiberPoint n e f g H (sphereBoundaryBasepoint n)).point =
      (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n)))).point := by
  -- The packaged point coordinate is `f` evaluated at the chosen sphere basepoint.
  rw [boundaryDatumToHomotopyFiberPoint_point, underTopBasepoint_homotopyFiber,
    HomotopyFiber.point_basepoint, underTopBasepoint_underTopOfPoint]

/-- Helper for Theorem 10.3.1: once the point coordinates are matched, equality with the canonical
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

/-- Helper for Theorem 10.3.1: if a path is followed by the reverse of a comparison path and then
that comparison path, the detour cancels up to homotopy. -/
private theorem transSymmCancel_homotopic {X : Type*} [TopologicalSpace X] {x y : X}
    (a b : Path x y) :
    ((a.trans b.symm).trans b).Homotopic a := by
  -- Reassociate the concatenation so the middle `b.symm.trans b` contracts first.
  refine (Path.Homotopic.trans_assoc a b.symm b).trans ?_
  -- Replace the contracted middle loop by the constant path and remove the trailing constant.
  refine (Path.Homotopic.hcomp (Path.Homotopic.refl a) (Path.Homotopic.symm_trans b)).trans ?_
  exact Path.Homotopic.trans_refl a

/-- Helper for Theorem 10.3.1: the packaged boundary basepoint loop is null-homotopic. This is
the executable replacement for the failed strict-normalization route. -/
private theorem boundaryDatumToHomotopyFiberBasepointPath_homotopic_refl (n : ℕ)
    (e : C(Y, Z)) (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    (boundaryDatumToHomotopyFiberPath n e f g H (sphereBoundaryBasepoint n)).Homotopic
      (Path.refl (ULift.up (e (f (sphereBoundaryBasepoint n))))) := by
  let a :=
    helpBoundaryValuePath n e f g H (sphereBoundaryBasepoint n)
  let b :=
    ((unitDiskRadialPathToBoundary n (sphereBoundaryBasepoint n)).map
      (uliftTargetContinuousMap (A := unitDisk n) g).continuous)
  have hcancel :
      ((a.trans b.symm).trans b).Homotopic a := by
    -- Reassociate so the middle `b.symm.trans b` contracts, then remove the trailing constant.
    refine (Path.Homotopic.trans_assoc a b.symm b).trans ?_
    refine (Path.Homotopic.hcomp (Path.Homotopic.refl a) (Path.Homotopic.symm_trans b)).trans ?_
    exact Path.Homotopic.trans_refl a
  have hcollapse :
      (((a.trans b.symm).trans b).trans a.symm).Homotopic
        (Path.refl (ULift.up (e (f (sphereBoundaryBasepoint n))))) := by
    -- First cancel the radial detour, then contract the remaining `a.trans a.symm` loop.
    exact (Path.Homotopic.hcomp hcancel (Path.Homotopic.refl a.symm)).trans
      (Path.Homotopic.trans_symm a)
  -- Expand the packaged basepoint path into the explicit four-term composite used above.
  simpa [boundaryDatumToHomotopyFiberPath, boundaryDatumToHomotopyFiberPathHomotopy,
    basepointToConeValuePath, boundaryDatumRadialHomotopy, boundaryDatumBoundaryHomotopy,
    helpBoundaryValuePath, a, b] using hcollapse

/-- Helper for Theorem 10.3.1: a homotopy between two loop coordinates at the same source point
produces a path between the corresponding points of the homotopy fiber. -/
private theorem homotopyFiberPoint_joined_of_pathHomotopy
    (e : C(Y, Z)) (y₀ : Y)
    {γ₀ γ₁ : Path (ULift.up (e y₀)) (ULift.up (e y₀))}
    (hγ : γ₀.Homotopic γ₁) :
    Joined
      ((HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₀) (by
          rw [PathSpace.endpoint_ofPath]
          rfl)) : (homotopyFiberAt e y₀).right)
      ((HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₁) (by
          rw [PathSpace.endpoint_ofPath]
          rfl)) : (homotopyFiberAt e y₀).right) := by
  rcases hγ with ⟨H⟩
  let pathFamily := fun s : I ↦ (H.eval s).toContinuousMap
  have huncurry : Continuous (Function.uncurry fun s t ↦ pathFamily s t) := by
    -- Curry the path homotopy itself so that the homotopy parameter indexes the path family.
    simpa [pathFamily, Function.uncurry, Path.Homotopy.eval] using H.toHomotopy.continuous
  have hsource :
      ∀ s : I, pathFamily s 0 = ULift.up (e y₀) := by
    intro s
    -- Every slice of a path homotopy starts at the common source point.
    simpa [pathFamily, Path.Homotopy.eval] using H.source s
  let pathLift : C(I, PathSpace (ULift.up (e y₀))) :=
    { toFun := fun s ↦ ⟨pathFamily s, hsource s⟩
      continuous_toFun := by
        -- Package the continuous path family into the based path-space owner.
        exact
          (ContinuousMap.continuous_of_continuous_uncurry pathFamily huncurry).subtype_mk
            hsource }
  have hendpoint :
      ∀ s : I,
        uliftContinuousMapAcrossUniverses e (ULift.up y₀) = (pathLift s).endpoint := by
    intro s
    -- The endpoint of each slice remains fixed at the image of the common source point.
    change ULift.up (e y₀) = (pathLift s).endpoint
    change ULift.up (e y₀) = pathFamily s 1
    simpa [pathFamily, Path.Homotopy.eval] using H.target s
  let fiberPath :
      Path
        (((HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₀) (by
            rw [PathSpace.endpoint_ofPath]
            rfl)) : (homotopyFiberAt e y₀).right))
        (((HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₁) (by
            rw [PathSpace.endpoint_ofPath]
            rfl)) : (homotopyFiberAt e y₀).right)) :=
    Path.mk
      { toFun := fun s ↦ HomotopyFiber.mk (ULift.up y₀) (pathLift s) (hendpoint s)
        continuous_toFun := by
          -- Keep the source coordinate fixed and vary only the path coordinate.
          exact (continuous_const.prodMk pathLift.continuous).subtype_mk hendpoint }
      (by
        -- At time `0`, the homotopy recovers the initial loop coordinate.
        change
          (HomotopyFiber.mk (ULift.up y₀) (pathLift 0) (hendpoint 0) :
              (homotopyFiberAt e y₀).right) =
            (HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₀) (by
              rw [PathSpace.endpoint_ofPath]
              rfl) : (homotopyFiberAt e y₀).right)
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply ContinuousMap.ext
          intro t
          change (H.eval 0) t = γ₀ t
          rw [H.eval_zero])
      (by
        -- At time `1`, the homotopy recovers the terminal loop coordinate.
        change
          (HomotopyFiber.mk (ULift.up y₀) (pathLift 1) (hendpoint 1) :
              (homotopyFiberAt e y₀).right) =
            (HomotopyFiber.mk (ULift.up y₀) (PathSpace.ofPath γ₁) (by
              rw [PathSpace.endpoint_ofPath]
              rfl) : (homotopyFiberAt e y₀).right)
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · apply Subtype.ext
          apply ContinuousMap.ext
          intro t
          change (H.eval 1) t = γ₁ t
          rw [H.eval_one])
  exact ⟨fiberPath⟩

/-- Helper for Theorem 10.3.1: the packaged boundary datum is joined to the canonical
homotopy-fiber basepoint at the sphere basepoint. This replaces the brittle equality target by the
path-level bridge actually needed for basepoint transport. -/
private theorem boundaryDatumToHomotopyFiberBasepoint_joined (n : ℕ)
    (e : C(Y, Z)) (f : C(sphereBoundary n, Y)) (g : C(unitDisk n, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    Joined
      (boundaryDatumToHomotopyFiberMap n e f g H (sphereBoundaryBasepoint n))
      (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint n)))) := by
  let y₀ := f (sphereBoundaryBasepoint n)
  let γ₀ := boundaryDatumToHomotopyFiberPath n e f g H (sphereBoundaryBasepoint n)
  let γ₁ := Path.refl (ULift.up (e y₀))
  have hγ :
      γ₀.Homotopic γ₁ := by
    -- Route correction: use the solved nullhomotopy of the packaged basepoint loop directly in
    -- the homotopy fiber owner instead of normalizing the subtype equality by hand.
    simpa [y₀, γ₀, γ₁] using
      boundaryDatumToHomotopyFiberBasepointPath_homotopic_refl n e f g H
  -- Package the point-fixed loop homotopy as a path between the two homotopy-fiber points.
  simpa [y₀, γ₀, γ₁, boundaryDatumToHomotopyFiberMap, boundaryDatumToHomotopyFiberPoint,
    underTopBasepoint_homotopyFiber, HomotopyFiber.basepoint, PathSpace.ofPath, PathSpace.basepoint,
    PathSpace.mk] using homotopyFiberPoint_joined_of_pathHomotopy e y₀ hγ

/-- Helper for Theorem 10.3.1: `π_ q X x` can be read as path components of the Section 9.5
sphere-evaluation fiber over `x`. -/
private noncomputable def homotopyGroupEquivSphereBasepointFiberZeroth
    {X : Type u} [TopologicalSpace X] (q : ℕ) (x : X) :
    π_ q X x ≃ ZerothHomotopy (sphereBasepointFiber q x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace q x)
  -- Compare `π_q` with the iterated loop-space owner and then transport through the sphere-fiber
  -- model.
  (homotopyGroupEquivZerothHomotopyGenLoop q x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Theorem 10.3.1: a path between basepoints transports the path components of the
Section 9.5 sphere-evaluation fibers. -/
private noncomputable def homotopyGroupFiberZerothEquivOfPath
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    ZerothHomotopy (sphereBasepointFiber q x) ≃ ZerothHomotopy (sphereBasepointFiber q x') :=
  sphereBasepointFiberZerothEquivOfPathClass q (Path.Homotopic.Quotient.mk β)

/-- Helper for Theorem 10.3.1: a path between basepoints induces an equivalence on homotopy
groups. -/
private noncomputable def homotopyGroupBasepointChangeEquiv
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    π_ q X x ≃ π_ q X x' :=
  -- Compare both homotopy groups with the common sphere-fiber model and translate along `β`.
  (homotopyGroupEquivSphereBasepointFiberZeroth q x).trans
    ((homotopyGroupFiberZerothEquivOfPath q β).trans
      (homotopyGroupEquivSphereBasepointFiberZeroth q x').symm)

/-- Helper for Theorem 10.3.1: subsingleton homotopy groups transport along a path between
basepoints. -/
private theorem homotopyGroupSubsingleton_of_path
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x')
    [Subsingleton (π_ q X x)] :
    Subsingleton (π_ q X x') := by
  let e := homotopyGroupBasepointChangeEquiv q β
  -- Pull the subsingleton structure across the basepoint-change equivalence.
  exact Equiv.subsingleton e.symm

/-- Helper for Theorem 10.3.1: subsingleton homotopy groups transport along a joined witness
between basepoints. -/
private theorem homotopyGroupSubsingleton_of_joined
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (m : ℕ) {x x' : X}
    (hjoin : Joined x x') (hπ : Subsingleton (π_ m X x)) :
    Subsingleton (π_ m X x') := by
  rcases hjoin with ⟨β⟩
  let _ : Subsingleton (π_ m X x) := hπ
  -- Choose a path from the `Joined` witness and transport the subsingleton structure along it.
  exact homotopyGroupSubsingleton_of_path m β

/-- Helper for Theorem 10.3.1: the concrete boundary sphere maps continuously into the canonical
TopCat sphere model by `ULift.up`. -/
private def sphereBoundaryToTopCatSphere (n : ℕ) : C(sphereBoundary n, (𝕊 n : TopCat)) :=
  ⟨ULift.up, Homeomorph.ulift.symm.continuous_toFun⟩

/-- Helper for Theorem 10.3.1: the canonical TopCat sphere model maps continuously back to the
concrete boundary sphere by `ULift.down`. -/
private def topCatSphereToSphereBoundary (n : ℕ) : C((𝕊 n : TopCat), sphereBoundary n) :=
  ⟨ULift.down, Homeomorph.ulift.continuous_toFun⟩

/-- Helper for Theorem 10.3.1: the transported boundary map lands in the Section 9.5
sphere-evaluation fiber because it preserves the chosen sphere basepoint. -/
private theorem sphereBoundaryBasedMapToSphereFiber_mem
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x) :
    k₀.comp (topCatSphereToSphereBoundary n) ∈ sphereBasepointFiber n x := by
  -- Read the transported map at the canonical TopCat sphere basepoint.
  refine (mem_sphereBasepointFiber_iff n x _).2 ?_
  simpa [topCatSphereToSphereBoundary, sphereBasepoint, sphereBoundaryBasepoint] using hk₀

/-- Helper for Theorem 10.3.1: a based map on the concrete boundary sphere defines a point of the
Section 9.5 sphere-evaluation fiber after transporting through `ULift`. -/
private def sphereBoundaryBasedMapToSphereFiber
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x) :
    sphereBasepointFiber n x :=
  ⟨k₀.comp (topCatSphereToSphereBoundary n),
    sphereBoundaryBasedMapToSphereFiber_mem n x k₀ hk₀⟩

/-- Helper for Theorem 10.3.1: trivial `π_ n(X, x)` makes every point of the Section 9.5 sphere
fiber path-connected to the constant based sphere map. -/
private theorem joinedConstSphereFiberOfSubsingletonHomotopyGroup
    {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X) (f : sphereBasepointFiber n x)
    (hπ : Subsingleton (π_ n X x)) :
    Joined f ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩ := by
  let e := homotopyGroupEquivSphereBasepointFiberZeroth n x
  have hsub : Subsingleton (ZerothHomotopy (sphereBasepointFiber n x)) := by
    let _ : Subsingleton (π_ n X x) := hπ
    exact Equiv.subsingleton e.symm
  let ηf : ZerothHomotopy (sphereBasepointFiber n x) := Quotient.mk _ f
  let ηc : ZerothHomotopy (sphereBasepointFiber n x) :=
    Quotient.mk _ ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩
  have hη : ηf = ηc := Subsingleton.elim _ _
  -- Equality in the path-component quotient is exactly the `Joined` relation.
  exact Quotient.exact hη

/-- Helper for Theorem 10.3.1: a path in the Section 9.5 sphere fiber uncarries to a concrete
homotopy from the boundary map to the constant map at the chosen basepoint. -/
private noncomputable def sphereBoundaryHomotopyToConstantOfJoinedFiberPoints
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x)
    (hjoin :
      Joined (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
        ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩) :
    k₀.Homotopy (ContinuousMap.const _ x) := by
  classical
  let γ : Path
      (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
      ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩ :=
    Classical.choice hjoin
  -- Local instance justification (compact-open transport): the path-space uncurry construction
  -- uses the TopCat sphere model, whose compactness is transferred from `sphereBoundary n`.
  letI : CompactSpace (𝕊 n : TopCat) := by
    simpa using
      Homeomorph.compactSpace
        (Homeomorph.ulift.symm : sphereBoundary n ≃ₜ (𝕊 n : TopCat))
  -- Local instance justification (compact-open transport): the same transported sphere model must
  -- be Hausdorff so that the compact-open mapping space carries the expected topology.
  letI : T2Space (𝕊 n : TopCat) := by
    simpa using
      Homeomorph.t2Space
        (Homeomorph.ulift.symm : sphereBoundary n ≃ₜ (𝕊 n : TopCat))
  let γmaps : C(I, C(𝕊 n, X)) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(sphereBasepointFiber n x, C(𝕊 n, X))).comp
      γ.toContinuousMap
  let transportDomain : C(I × sphereBoundary n, I × (𝕊 n : TopCat)) :=
    ⟨fun p ↦ (p.1, ULift.up p.2), by fun_prop⟩
  let transported : C(I × sphereBoundary n, X) :=
    γmaps.uncurry.comp transportDomain
  refine ⟨transported, ?_, ?_⟩
  · -- Evaluate the lifted path at time `0` and undo the `ULift` transport of the sphere model.
    intro y
    change ((γ 0).1) (ULift.up y) = k₀ y
    have hsource :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦
          q.1 (ULift.up y))
        γ.source
    simpa [transported, transportDomain, γmaps, sphereBoundaryBasedMapToSphereFiber, sphereBasepoint,
      sphereBoundaryBasepoint] using hsource
  · -- At time `1`, the path in the sphere fiber lands at the constant based map.
    intro y
    change ((γ 1).1) (ULift.up y) = x
    have htarget :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦
          q.1 (ULift.up y))
        γ.target
    simpa [transported, transportDomain, γmaps] using htarget

/-- Helper for Theorem 10.3.1: the radial cone quotient formula lands in the disk model. -/
private theorem sphereBoundaryConeQuotientMap_mem (n : ℕ) (p : I × sphereBoundary n) :
    (1 - (p.1 : ℝ)) • p.2.1 ∈ unitDisk n := by
  rw [mem_unitDisk_iff, norm_smul]
  have hp_nonneg : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
  have hp_le : 1 - (p.1 : ℝ) ≤ 1 := by
    linarith [p.1.2.1]
  rw [mem_sphereBoundary_iff.mp p.2.2, Real.norm_of_nonneg hp_nonneg]
  simpa using hp_le

/-- Helper for Theorem 10.3.1: the radial cone quotient formula is continuous. -/
private theorem continuous_sphereBoundaryConeQuotientMap (n : ℕ) :
    Continuous fun p : I × sphereBoundary n ↦
      (⟨(1 - (p.1 : ℝ)) • p.2.1, sphereBoundaryConeQuotientMap_mem n p⟩ : unitDisk n) := by
  fun_prop

/-- Helper for Theorem 10.3.1: the radial cone quotient collapses the top slice
`{1} × sphereBoundary n` to the disk center and keeps the bottom slice as the boundary
inclusion. -/
private def sphereBoundaryConeQuotientMap (n : ℕ) : C(I × sphereBoundary n, unitDisk n) :=
  ⟨fun p ↦
      ⟨(1 - (p.1 : ℝ)) • p.2.1, sphereBoundaryConeQuotientMap_mem n p⟩,
    continuous_sphereBoundaryConeQuotientMap n⟩

/-- Helper for Theorem 10.3.1: the radial cone quotient restricts on the bottom slice to the
standard boundary inclusion. -/
@[simp] private theorem sphereBoundaryConeQuotientMap_zero
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (0, x) = sphereBoundaryInclusion n x := by
  apply Subtype.ext
  change (1 - ((0 : I) : ℝ)) • (x :
      EuclideanSpace ℝ (Fin (n + 1))) =
    (x : EuclideanSpace ℝ (Fin (n + 1)))
  simp

/-- Helper for Theorem 10.3.1: the radial cone quotient collapses the top slice to the disk
center. -/
@[simp] private theorem sphereBoundaryConeQuotientMap_one
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (1, x) = unitDiskCenter n := by
  apply Subtype.ext
  change (1 - ((1 : I) : ℝ)) • (x :
      EuclideanSpace ℝ (Fin (n + 1))) = 0
  simp [unitDiskCenter]

/-- Helper for Theorem 10.3.1: the radial cone quotient map from `I × sphereBoundary n` onto
`unitDisk n` is surjective. -/
private theorem sphereBoundaryConeQuotientMap_surjective (n : ℕ) :
    Function.Surjective (sphereBoundaryConeQuotientMap n) := by
  intro y
  by_cases hy0 : (y : EuclideanSpace ℝ (Fin (n + 1))) = 0
  · refine ⟨(1, sphereBoundaryBasepoint n), ?_⟩
    rw [sphereBoundaryConeQuotientMap_one]
    apply Subtype.ext
    simpa [unitDiskCenter, hy0]
  · have hy_norm_nonzero : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hy0
    have hy_mem : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := mem_unitDisk_iff.mp y.2
    let x : sphereBoundary n :=
      ⟨‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ •
          (y : EuclideanSpace ℝ (Fin (n + 1))), by
        rw [mem_sphereBoundary_iff, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        field_simp [hy_norm_nonzero]⟩
    let t : I :=
      ⟨1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖, by
        constructor
        · linarith [hy_mem]
        · linarith [norm_nonneg (y : EuclideanSpace ℝ (Fin (n + 1)))]⟩
    refine ⟨(t, x), ?_⟩
    apply Subtype.ext
    change (1 - (t : ℝ)) • (x : EuclideanSpace ℝ (Fin (n + 1))) =
      (y : EuclideanSpace ℝ (Fin (n + 1)))
    dsimp [t, x]
    rw [show 1 - (1 - ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖) =
        ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ by ring, smul_smul]
    rw [mul_inv_cancel₀ hy_norm_nonzero, one_smul]

/-- Helper for Theorem 10.3.1: a nullhomotopy of a boundary sphere map is constant on the fibers
of the radial cone quotient and therefore descends to a disk map. -/
private theorem sphereBoundaryHomotopy_factorsThrough_coneQuotient
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    {k₀ : C(sphereBoundary n, X)}
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap (sphereBoundaryConeQuotientMap n) := by
  intro p q hpq
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  change H (t, a) = H (s, b)
  have hvec :
      (1 - (t : ℝ)) • (a : EuclideanSpace ℝ (Fin (n + 1))) =
        (1 - (s : ℝ)) • (b : EuclideanSpace ℝ (Fin (n + 1))) := by
    exact congrArg Subtype.val hpq
  have hscale : 1 - (t : ℝ) = 1 - (s : ℝ) := by
    have hnorm := congrArg norm hvec
    rw [norm_smul, norm_smul, mem_sphereBoundary_iff.mp a.2, mem_sphereBoundary_iff.mp b.2,
      Real.norm_of_nonneg (sub_nonneg.mpr t.2.2),
      Real.norm_of_nonneg (sub_nonneg.mpr s.2.2)] at hnorm
    simpa using hnorm
  by_cases htop : 1 - (t : ℝ) = 0
  · have hs_top : 1 - (s : ℝ) = 0 := by simpa [hscale] using htop
    have ht : t = 1 := by
      have htval : (t : ℝ) = 1 := by linarith
      exact Subtype.ext htval
    have hs : s = 1 := by
      have hsval : (s : ℝ) = 1 := by linarith
      exact Subtype.ext hsval
    rw [ht, hs, H.apply_one, H.apply_one]
    simp
  · have hab_val : (a : EuclideanSpace ℝ (Fin (n + 1))) =
        (b : EuclideanSpace ℝ (Fin (n + 1))) := by
      apply (smul_right_injective (M := EuclideanSpace ℝ (Fin (n + 1))) htop)
      simpa [hscale] using hvec
    have hab : a = b := Subtype.ext hab_val
    have hts : t = s := Subtype.ext <| by linarith
    rw [hts, hab]

/-- Helper for Theorem 10.3.1: a nullhomotopy of a boundary sphere map descends along the radial
cone quotient to a continuous filler on `unitDisk n`. -/
private noncomputable def unitDiskLiftOfSphereBoundaryHomotopyToConstant
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    C(unitDisk n, X) :=
  let q := sphereBoundaryConeQuotientMap n
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (sphereBoundaryConeQuotientMap_surjective n) q.continuous
  hq.lift H.toContinuousMap
    (sphereBoundaryHomotopy_factorsThrough_coneQuotient n x H)

/-- Helper for Theorem 10.3.1: the descended disk filler restricts on the boundary to the
original sphere map. -/
private theorem unitDiskLiftOfSphereBoundaryHomotopyToConstant_comp
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    (unitDiskLiftOfSphereBoundaryHomotopyToConstant n x k₀ H).comp
        (sphereBoundaryInclusion n) = k₀ := by
  let q := sphereBoundaryConeQuotientMap n
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (sphereBoundaryConeQuotientMap_surjective n) q.continuous
  let hfactor := sphereBoundaryHomotopy_factorsThrough_coneQuotient n x H
  ext y
  -- Evaluate the descended equality on the bottom slice `t = 0`.
  have hdesc :=
    congrArg (fun f : C(I × sphereBoundary n, X) ↦ f (0, y))
      (hq.lift_comp H.toContinuousMap hfactor)
  change (unitDiskLiftOfSphereBoundaryHomotopyToConstant n x k₀ H)
      (sphereBoundaryConeQuotientMap n (0, y)) = H (0, y) at hdesc
  simpa [unitDiskLiftOfSphereBoundaryHomotopyToConstant,
    sphereBoundaryConeQuotientMap_zero] using hdesc

/-- Helper for Theorem 10.3.1: if `π_ n(X, x)` is trivial, then every based sphere map
`(sphereBoundary n, sphereBoundaryBasepoint n) ⟶ (X, x)` extends across `unitDisk n`. -/
private theorem exists_unitDiskLift_of_subsingletonHomotopyGroup_atBasepoint
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X))
    (hk₀ : k₀ (sphereBoundaryBasepoint n) = x)
    (hπ : Subsingleton (π_ n X x)) :
    ∃ k : C(unitDisk n, X), k.comp (sphereBoundaryInclusion n) = k₀ := by
  have hjoin :
      Joined
        ((sphereBoundaryBasedMapToSphereFiber (X := X) n x k₀ hk₀ :
          sphereBasepointFiber (X := X) n x))
        ((⟨ContinuousMap.const (TopCat.sphere.{0} n) x, by simp [mem_sphereBasepointFiber_iff]⟩ :
          sphereBasepointFiber (X := X) n x)) := by
    -- Trivial `π_ n` makes the based boundary datum path-connected to the constant datum.
    simpa using
      joinedConstSphereFiberOfSubsingletonHomotopyGroup
        (X := X) n x
        (sphereBoundaryBasedMapToSphereFiber (X := X) n x k₀ hk₀) hπ
  let H :
      k₀.Homotopy (ContinuousMap.const (sphereBoundary n) x) :=
    sphereBoundaryHomotopyToConstantOfJoinedFiberPoints n x k₀ hk₀ hjoin
  refine ⟨unitDiskLiftOfSphereBoundaryHomotopyToConstant n x k₀ H, ?_⟩
  -- Descend the nullhomotopy along the cone quotient and read off its boundary restriction.
  exact unitDiskLiftOfSphereBoundaryHomotopyToConstant_comp n x k₀ H

/-- Helper for Theorem 10.3.1: in a group-exact pair `A ⟶ B ⟶ C`, a trivial source forces the
middle map to be injective. -/
private theorem injective_of_mulExact_of_subsingleton_source
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (hfg : Function.MulExact f g)
    [Subsingleton A] :
    Function.Injective g := by
  intro x y hxy
  -- Compare `x` and `y` through the kernel element `x * y⁻¹`.
  have hkernel : g (x * y⁻¹) = 1 := by
    rw [g.map_mul, g.map_inv, hxy, mul_inv_cancel]
  rcases (hfg _).mp hkernel with ⟨a, ha⟩
  have hfa : f a = 1 := by
    -- The trivial source group collapses every source element to `1`.
    calc
      f a = f (1 : A) := by
        congr
        exact Subsingleton.elim _ _
      _ = 1 := f.map_one
  have hquotient : x * y⁻¹ = 1 := by
    calc
      x * y⁻¹ = f a := ha.symm
      _ = 1 := hfa
  -- Cancel the trivial quotient element to recover equality of `x` and `y`.
  calc
    x = x * 1 := by simp
    _ = x * (y⁻¹ * y) := by rw [inv_mul_cancel]
    _ = (x * y⁻¹) * y := by simp [mul_assoc]
    _ = 1 * y := by rw [hquotient]
    _ = y := by simp

/-- Helper for Theorem 10.3.1: in a group-exact pair `A ⟶ B ⟶ C`, a trivial target forces the
first map to be surjective. -/
private theorem surjective_of_mulExact_of_subsingleton_target
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (hfg : Function.MulExact f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro y
  -- Exactness identifies every target element with an image because the obstruction vanishes.
  have hy : g y = 1 := by
    exact Subsingleton.elim _ _
  exact (hfg _).mp hy

/-- Helper for Theorem 10.3.1: forgetting the path coordinate of `F(e; y₁)` recovers the source
point in `Y`. -/
private noncomputable def homotopyFiberSourceProjection
    (e : C(Y, Z)) (y₁ : Y) :
    C((homotopyFiberAt e y₁).right, Y) where
  toFun q := q.point.down
  continuous_toFun := by
    -- Read the source coordinate of the homotopy-fiber point and then forget the `ULift`.
    simpa [homotopyFiberAt, HomotopyFiber.point] using
      (continuous_uliftDown.comp
        ((continuous_fst.comp continuous_subtype_val).comp
          (continuous_id : Continuous fun q : (homotopyFiberAt e y₁).right ↦ q)))

/-- Helper for Theorem 10.3.1: evaluating the point projection simply reads the stored source
coordinate of a homotopy-fiber point. -/
@[simp] private theorem homotopyFiberSourceProjection_apply
    (e : C(Y, Z)) (y₁ : Y) (q : (homotopyFiberAt e y₁).right) :
    homotopyFiberSourceProjection e y₁ q = q.point.down :=
  rfl

/-
This private extension wrapper was unused. Its old proof transported homotopy groups through a
raw homotopy-fiber topology that is not known to be a May compactly generated space.

/-- Helper for Theorem 10.3.1: once the canonical homotopy-fiber group is known to be trivial,
the packaged boundary sphere map extends across the disk inside the same homotopy fiber. -/
private theorem exists_unitDiskLift_of_boundaryDatumToHomotopyFiberMap
    (m : ℕ) (e : C(Y, Z)) (f : C(sphereBoundary m, Y)) (g : C(unitDisk m, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion m)))
    (hπ :
      Subsingleton
        (π_ m (homotopyFiberAt e (f (sphereBoundaryBasepoint m))).right
          (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint m)))))) :
    ∃ U : C(unitDisk m, (homotopyFiberAt e (f (sphereBoundaryBasepoint m))).right),
      U.comp (sphereBoundaryInclusion m) = boundaryDatumToHomotopyFiberMap m e f g H := by
  let x0 :=
    boundaryDatumToHomotopyFiberMap m e f g H (sphereBoundaryBasepoint m)
  have hjoin :
      Joined x0 (underTopBasepoint (homotopyFiberAt e (f (sphereBoundaryBasepoint m)))) := by
    simpa [x0] using boundaryDatumToHomotopyFiberBasepoint_joined m e f g H
  have hπx0 :
      Subsingleton
        (π_ m (homotopyFiberAt e (f (sphereBoundaryBasepoint m))).right x0) := by
    rcases hjoin with ⟨β⟩
    -- Reverse the joined witness so the canonical basepoint triviality transports to `x0`.
    exact homotopyGroupSubsingleton_of_path m β.symm
  -- Use the general based-sphere extension theorem at the raw packaged basepoint `x0`.
  exact
    exists_unitDiskLift_of_subsingletonHomotopyGroup_atBasepoint
      m x0 (boundaryDatumToHomotopyFiberMap m e f g H) rfl hπx0
-/

/-- Helper for Theorem 10.3.1: the Chapter 9 two-degree `π_*` owner forces the relevant homotopy
fiber homotopy group to be trivial. -/
private theorem subsingletonHomotopyGroup_homotopyFiberAt_of_hasPiInjectiveSurjectiveSucc
    {m : ℕ} (e : C(Y, Z)) (hPi : HasPiInjectiveSurjectiveSucc m e) (y₁ : Y) :
    Subsingleton
      (π_ m (homotopyFiberAt e y₁).right (underTopBasepoint (homotopyFiberAt e y₁))) := by
  -- TODO: specialize the Chapter 9 homotopy-fiber exact sequence at `homotopyFiberAt e y₁`,
  -- use injectivity of `e_* : π_ m(Y, y₁) → π_ m(Z, e y₁)` to force the fiber-inclusion image to
  -- be trivial, then use surjectivity of `e_* : π_(m + 1)(Y, y₁) → π_(m + 1)(Z, e y₁)` to show
  -- every fiber class lies in the image of the boundary map, which is therefore also trivial.
  sorry

/-- Helper for Theorem 10.3.1: `HasSphereConeHelp m e` can be read as an explicit disk filler on
`sphereBoundary m ↪ unitDisk m`, which is the form used by the relative-cell induction. -/
private theorem explicitSphereDiskFiller_of_hasSphereConeHelp
    {m : ℕ} {e : C(Y, Z)} (hHelp : HasSphereConeHelp m e)
    (f : C(sphereBoundary m, Y)) (g : C(unitDisk m, Z))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion m))) :
    ∃ G : C(unitDisk m, Y), ∃ K : (e.comp G).Homotopy g,
      G.comp (sphereBoundaryInclusion m) = f ∧
        ∀ z : I × sphereBoundary m, K (z.1, sphereBoundaryInclusion m z.2) = H z := by
  -- TODO: the remaining geometric work factors through three now-isolated substeps:
  -- 1. collapse the canonical homotopy-fiber group by
  --    `subsingletonHomotopyGroup_homotopyFiberAt_of_hasPiInjectiveSurjectiveSucc`;
  -- 2. transport that triviality to the raw packaged basepoint using
  --    `boundaryDatumToHomotopyFiberBasepoint_joined`;
  -- 3. extend the packaged sphere map across the disk and read its point/path coordinates back as
  --    the desired filler `G` and homotopy `K`.
  sorry

/-- Helper for Theorem 10.3.1: a finite-dimensional relative CW base inclusion should satisfy
`HasRelativeHelp` against an `n`-equivalence whose path-component map is surjective. -/
private theorem relCWComplexBaseInclusion_hasRelativeHelp_of_dimLE_of_isNEquivalence
    {X A : Set W} [T2Space W] [Topology.RelCWComplex X A] (n : ℕ)
    (h_dim : Topology.RelCWComplex.dimLE X n) (e : C(Y, Z)) [IsNEquivalence n e]
    (hπ0 : Function.Surjective (zerothHomotopyMap e)) :
    HasRelativeHelp (relCWComplexBaseInclusion X) e := by
  intro fA fX h_compat
  have hCellHelp : ∀ {m : ℕ}, m + 1 ≤ n → HasSphereConeHelp m e := fun {_} hm ↦
    hasSphereConeHelp_of_isNEquivalence_of_succ_le e hm
  have hExplicitCellHelp :
      ∀ {m : ℕ}, m + 1 ≤ n →
        ∀ (f : C(sphereBoundary m, Y)) (g : C(unitDisk m, Z))
          (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion m))),
          ∃ G : C(unitDisk m, Y), ∃ K : (e.comp G).Homotopy g,
            G.comp (sphereBoundaryInclusion m) = f ∧
              ∀ z : I × sphereBoundary m, K (z.1, sphereBoundaryInclusion m z.2) = H z :=
    fun {_} hm f g H ↦
      explicitSphereDiskFiller_of_hasSphereConeHelp (hCellHelp hm) f g H
  -- Route correction: the missing Chapter 9 blocker is now isolated behind the explicit disk
  -- filler interface consumed by the source proof. What remains after that bridge is the relative
  -- CW assembly: the zero-skeleton base case from `hπ0`, closed-cell descent from the standard
  -- disk model, and the skeleton successor induction via
  -- `Topology.RelCWComplex.skeleton_union_iUnion_closedCell_eq_skeleton_succ`.
  sorry

/-- Theorem 10.3.1: if `(X, A)` is a relative CW complex of dimension at most `n` and
`e : C(Y, Z)` is an `n`-equivalence whose induced map on path components is surjective, then any
compatible maps `A → Y` and `X → Z` admit an extension `X → Y` whose composite with `e` is
homotopic to the given map rel `A`. -/
theorem exists_extensionLift_of_relCWComplex_dimLE_of_isNEquivalence
    {X A : Set W} [T2Space W] [Topology.RelCWComplex X A] (n : ℕ)
    (h_dim : Topology.RelCWComplex.dimLE X n) (e : C(Y, Z)) [IsNEquivalence n e]
    (hπ0 : Function.Surjective (zerothHomotopyMap e))
    (fA : C(A, Y)) (fX : C(X, Z))
    (h_compat : e.comp fA = fX.comp (relCWComplexBaseInclusion X)) :
    ∃ (F : C(X, Y)) (_ : (e.comp F).HomotopyRel fX (range (relCWComplexBaseInclusion X))),
      F.comp (relCWComplexBaseInclusion X) = fA := by
  -- Repackage the statement through the local `HasRelativeHelp` owner for the base inclusion.
  exact
    relCWComplexBaseInclusion_hasRelativeHelp_of_dimLE_of_isNEquivalence
      n h_dim e hπ0 fA fX h_compat

end
