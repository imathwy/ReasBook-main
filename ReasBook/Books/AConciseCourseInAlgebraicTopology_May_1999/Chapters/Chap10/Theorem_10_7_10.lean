import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_6_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyInclusion
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_7_10.TriadMap
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.UnitInterval

universe u v

open CategoryTheory
open Set
open scoped HomotopyClasses TopCat unitInterval Topology Topology.Homotopy

-- Semantic recall via `lean_leansearch`: no dedicated mathlib owner for maps of excisive triads
-- surfaced in the current environment, so this item is stated directly for an ambient
-- `ContinuousMap` together with its induced maps on `A ∩ B`, `A`, and `B`.

namespace Triad

variable {X : Type u} {X' : Type v} [TopologicalSpace X] [TopologicalSpace X']
variable (T : Triad X) (T' : Triad X') (e : C(X, X'))

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

section GenuineWeakEquivalence

variable {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A source-faithful weak-equivalence hypothesis for a continuous map keeps the Chapter 9
all-degree owner `IsWeakEquivalence` and adds the missing bijectivity on path components. -/
def IsGenuineWeakEquivalence (f : C(Y, Z)) : Prop :=
  Function.Bijective (zerothHomotopyMap f) ∧ IsWeakEquivalence f

/-- A genuine weak-equivalence hypothesis includes bijectivity on `π₀`. -/
theorem IsGenuineWeakEquivalence.bijective_zerothHomotopy {f : C(Y, Z)}
    (h : IsGenuineWeakEquivalence f) :
    Function.Bijective (zerothHomotopyMap f) :=
  h.1

/-- A genuine weak-equivalence hypothesis includes the ambient Chapter 9 weak-equivalence owner. -/
theorem IsGenuineWeakEquivalence.isWeakEquivalence {f : C(Y, Z)}
    (h : IsGenuineWeakEquivalence f) :
    IsWeakEquivalence f :=
  h.2

end GenuineWeakEquivalence

/-- Helper for Theorem 10.7.10: the boundary sphere `S^n` includes into any neighborhood of the
boundary image in `D^(n + 1)`. -/
private def sphereBoundaryNeighborhoodInclusion (n : ℕ) {U : Set (unitDisk n)}
    (hU : Set.range (sphereBoundaryInclusion n) ⊆ U) : C(sphereBoundary n, U) where
  toFun x := ⟨sphereBoundaryInclusion n x, hU ⟨x, rfl⟩⟩
  continuous_toFun := (sphereBoundaryInclusion n).continuous.subtype_mk fun x ↦ hU ⟨x, rfl⟩

/-- Helper for Theorem 10.7.10: forgetting the codomain restriction recovers
`sphereBoundaryInclusion n`. -/
@[simp] private theorem subtypeVal_comp_sphereBoundaryNeighborhoodInclusion (n : ℕ)
    {U : Set (unitDisk n)} (hU : Set.range (sphereBoundaryInclusion n) ⊆ U) :
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, unitDisk n)).comp
      (sphereBoundaryNeighborhoodInclusion n hU)) = sphereBoundaryInclusion n :=
  rfl

/-- Helper for Theorem 10.7.10: a boundary-neighborhood lift records that the disk datum already
admits a lift on an open neighborhood of `S^n ⊆ D^(n + 1)`. -/
private def HasBoundaryNeighborhoodLift (n : ℕ) (e : C(X, X')) (f : C(sphereBoundary n, X))
    (g : C(unitDisk n, X')) : Prop :=
  ∃ U : Set (unitDisk n), IsOpen U ∧
    ∃ hU : Set.range (sphereBoundaryInclusion n) ⊆ U,
      ∃ gU : C(U, X),
        e.comp gU = ContinuousMap.restrict U g ∧
          gU.comp (sphereBoundaryNeighborhoodInclusion n hU) = f

/-- Helper for Theorem 10.7.10: a global disk lift is, in particular, a neighborhood lift near
the boundary sphere. -/
private theorem hasBoundaryNeighborhoodLift_of_globalLift
    (n : ℕ) {f : C(sphereBoundary n, X)} {g : C(unitDisk n, X')}
    (G : C(unitDisk n, X)) (hG : e.comp G = g)
    (hBoundary : G.comp (sphereBoundaryInclusion n) = f) :
    HasBoundaryNeighborhoodLift n e f g := by
  -- Use the whole disk as the neighborhood, so the local datum is just the restriction of `G`.
  refine ⟨univ, isOpen_univ, ?_, ContinuousMap.restrict univ G, ?_, ?_⟩
  · intro y hy
    simp
  · -- On the full neighborhood, restricting the composite agrees pointwise with `hG`.
    ext x
    simpa using congrArg (fun h : C(unitDisk n, X') ↦ h x.1) hG
  · -- The restricted lift still matches the given boundary map on the sphere.
    ext x
    simpa [sphereBoundaryNeighborhoodInclusion] using
      congrArg (fun h : C(sphereBoundary n, X) ↦ h x) hBoundary

/-- Helper for Theorem 10.7.10: any boundary-neighborhood lift already forces the boundary datum
to be compatible with `g` after applying `e`. -/
private theorem HasBoundaryNeighborhoodLift.boundaryCompat
    {n : ℕ} {f : C(sphereBoundary n, X)} {g : C(unitDisk n, X')}
    (hNear : HasBoundaryNeighborhoodLift n e f g) :
    e.comp f = g.comp (sphereBoundaryInclusion n) := by
  rcases hNear with ⟨U, _hU_open, hU, gU, hgU, hf⟩
  -- Compare both boundary maps through the neighborhood lift `gU`.
  calc
    e.comp f = e.comp (gU.comp (sphereBoundaryNeighborhoodInclusion n hU)) := by
      rw [hf]
    _ = (e.comp gU).comp (sphereBoundaryNeighborhoodInclusion n hU) := by
      rfl
    _ = (ContinuousMap.restrict U g).comp (sphereBoundaryNeighborhoodInclusion n hU) := by
      rw [hgU]
    _ = g.comp (sphereBoundaryInclusion n) := by
      ext x
      rfl

/-- Helper for Theorem 10.7.10: an explicit disk-filler package for `e` extends any based sphere
map into the homotopy fiber `F(e; y)` across the disk. -/
private theorem homotopyFiberDiskLift_of_explicitSphereConeHelp
    (n : ℕ) (y : X)
    (hFill :
      ∀ (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
        (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          ∃ G : C(unitDisk n, X), ∃ K : (e.comp G).Homotopy g,
            G.comp (sphereBoundaryInclusion n) = f ∧
              ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z) :
    ∀ (u : C(sphereBoundary n, (homotopyFiberAt e y).right)),
      u (sphereBoundaryBasepoint n) = underTopBasepoint (homotopyFiberAt e y) →
        ∃ U : C(unitDisk n, (homotopyFiberAt e y).right),
          U.comp (sphereBoundaryInclusion n) = u := by
  intro u hu
  let pointProjection : C((homotopyFiberAt e y).right, X) :=
    { toFun := fun z ↦ z.point.down
      continuous_toFun := by
        -- Read the source coordinate of the homotopy-fiber point and then forget the `ULift`.
        simpa [homotopyFiberAt, HomotopyFiber.point] using
          (continuous_uliftDown.comp
            ((continuous_fst.comp continuous_subtype_val).comp
              (continuous_id : Continuous fun z : (homotopyFiberAt e y).right ↦ z))) }
  let pathProjection : C((homotopyFiberAt e y).right, PathSpace (ULift.up (e y))) :=
    { toFun := fun z ↦ z.path
      continuous_toFun := by
        -- The path coordinate is the second component of the homotopy-fiber subtype.
        simpa [homotopyFiberAt, HomotopyFiber.path] using
          ((continuous_snd.comp continuous_subtype_val) :
            Continuous fun z : (homotopyFiberAt e y).right ↦ z.1.2) }
  let pathDown : C(PathSpace (ULift.up (e y)), C(I, X')) :=
    { toFun := fun γ ↦ ⟨fun t ↦ (γ t).down, continuous_uliftDown.comp γ.toPath.continuous⟩
      continuous_toFun := by
        -- Forget the basepoint condition on the path and postcompose with `ULift.down`.
        simpa [PathSpace.toPath, PathSpace.ofPath, PathSpace.mk] using
          (ContinuousMap.continuous_postcomp
            (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u} X', X'))).comp
            (continuous_subtype_val :
              Continuous fun γ : PathSpace (ULift.up (e y)) ↦ γ.1) }
  let f : C(sphereBoundary n, X) := pointProjection.comp u
  let d : C(sphereBoundary n, C(I, X')) := pathDown.comp (pathProjection.comp u)
  have hdZero :
      (pathSpaceEvalAt 0 X').comp d = ContinuousMap.const (sphereBoundary n) (e y) := by
    -- The path stored in each homotopy-fiber point starts at the chosen basepoint `e y`.
    ext x
    change ULift.down ((u x).path 0) = e y
    simpa using congrArg ULift.down ((u x).path.2)
  have hdOne : (pathSpaceEvalAt 1 X').comp d = e.comp f := by
    -- The endpoint condition of the homotopy fiber says that the stored path ends at `e (f x)`.
    ext x
    have hx := HomotopyFiber.endpoint_eq (u x)
    change ULift.up (e ((u x).point.down)) = (u x).path.endpoint at hx
    simpa [d, f, pointProjection, pathDown, PathSpace.endpoint] using (congrArg ULift.down hx).symm
  let Hconst : (ContinuousMap.const (sphereBoundary n) (e y)).Homotopy (e.comp f) :=
    ContinuousMap.Homotopy.ofPathSpaceMap d hdZero hdOne
  obtain ⟨G, K, hBoundary, hK⟩ :=
    hFill f (ContinuousMap.const (unitDisk n) (e y)) Hconst.symm
  let liftedPoint : C(unitDisk n, ULift.{v} X) :=
    { toFun := fun x ↦ ULift.up (G x)
      continuous_toFun := continuous_uliftUp.comp G.continuous }
  let liftedComposite : C(unitDisk n, ULift.{u} X') :=
    { toFun := fun x ↦ ULift.up (e (G x))
      continuous_toFun := continuous_uliftUp.comp (e.continuous.comp G.continuous) }
  have hLiftedKZero :
      ∀ x : unitDisk n, ULift.up (K (0, x)) = liftedComposite x := by
    -- Lift the `t = 0` face of `K` into the common target universe.
    intro x
    change ULift.up (K (0, x)) = ULift.up ((e.comp G) x)
    exact congrArg ULift.up (K.apply_zero x)
  have hLiftedKOne :
      ∀ x : unitDisk n, ULift.up (K (1, x)) = ULift.up (e y) := by
    -- Lift the terminal constant face of `K` into the common target universe.
    intro x
    exact congrArg ULift.up (K.apply_one x)
  let liftedK :
      liftedComposite.Homotopy (ContinuousMap.const (unitDisk n) (ULift.up (e y))) :=
    { toFun := fun p ↦ ULift.up (K p)
      continuous_toFun := continuous_uliftUp.comp K.continuous
      map_zero_left := hLiftedKZero
      map_one_left := hLiftedKOne }
  have hPathZero :
      ∀ x : unitDisk n, liftedK.symm.toPathSpaceMap x 0 = ULift.up (e y) := by
    -- After reversing `liftedK`, each point-path starts at the chosen fiber basepoint.
    intro x
    have hx := ContinuousMap.congr_fun liftedK.symm.pathSpaceEvalAtZero_comp_toPathSpaceMap x
    simpa [pathSpaceEvalAtZero, pathSpaceEvalAt] using hx
  let pathLift : C(unitDisk n, PathSpace (ULift.up (e y))) :=
    { toFun := fun x ↦ ⟨liftedK.symm.toPathSpaceMap x, hPathZero x⟩
      continuous_toFun := by
        -- View the reversed homotopy as a path-space-valued map and then lift to the subtype.
        simpa [PathSpace.mk, ContinuousMap.Homotopy.toPathSpaceMap_apply] using
          liftedK.symm.toPathSpaceMap.continuous.subtype_mk hPathZero }
  have hFiberCondition :
      ∀ x : unitDisk n,
        (underTopOfPointMapAcrossUniverses e y).right.hom (liftedPoint x) = (pathLift x).endpoint := by
    -- The reversed lifted homotopy ends exactly at the lifted value `e (G x)`.
    intro x
    change liftedComposite x = (pathLift x).endpoint
    have hx := ContinuousMap.congr_fun (liftedK.symm.pathSpaceEvalAt_comp_toPathSpaceMap 1) x
    simpa [liftedComposite, pathLift, pathSpaceEvalAt, PathSpace.endpoint] using hx
  let U : C(unitDisk n, (homotopyFiberAt e y).right) :=
    { toFun := fun x ↦ HomotopyFiber.mk (liftedPoint x) (pathLift x) (hFiberCondition x)
      continuous_toFun := by
        -- Pair the lifted disk map with its lifted nullhomotopy path family.
        simpa [HomotopyFiber.mk] using
          (liftedPoint.continuous.prodMk pathLift.continuous).subtype_mk hFiberCondition }
  refine ⟨U, ?_⟩
  ext x
  apply Subtype.ext
  apply Prod.ext
  · -- The point coordinate on the boundary is the original sphere-map point stored in `u`.
    change ULift.up (G (sphereBoundaryInclusion n x)) = ULift.up ((u x).point.down)
    exact congrArg ULift.up (ContinuousMap.congr_fun hBoundary x)
  · -- The path coordinate on the boundary is the original homotopy-fiber path stored in `u`.
    apply Subtype.ext
    ext t
    change liftedK.symm.toPathSpaceMap (sphereBoundaryInclusion n x) t = (u x).path t
    change ULift.up (K (σ t, sphereBoundaryInclusion n x)) = (u x).path t
    have htrack :
        K (σ t, sphereBoundaryInclusion n x) = ((u x).path t).down := by
      calc
        K (σ t, sphereBoundaryInclusion n x) = Hconst.symm (σ t, x) := hK (σ t, x)
        _ = Hconst (t, x) := by
          change Hconst (σ (σ t), x) = Hconst (t, x)
          simp
        _ = d x t := by
          simp [Hconst, ContinuousMap.Homotopy.ofPathSpaceMap_apply]
        _ = ((u x).path t).down := by
          rfl
    exact congrArg ULift.up htrack

/-- Helper for Theorem 10.7.10: the concrete boundary sphere maps continuously into the canonical
TopCat sphere model by `ULift.up`. -/
private def sphereBoundaryToTopCatSphere (n : ℕ) : C(sphereBoundary n, (𝕊 n : TopCat)) :=
  ⟨ULift.up, Homeomorph.ulift.symm.continuous_toFun⟩

/-- Helper for Theorem 10.7.10: the canonical TopCat sphere model maps continuously back to the
concrete boundary sphere by `ULift.down`. -/
private def topCatSphereToSphereBoundary (n : ℕ) : C((𝕊 n : TopCat), sphereBoundary n) :=
  ⟨ULift.down, Homeomorph.ulift.continuous_toFun⟩

/-- Helper for Theorem 10.7.10: the concrete zero-sphere `S^0` pointed at `sphereBasepoint 0`. -/
private noncomputable abbrev sZeroBasedSpace : BasedSpace :=
  underTopOfPoint (𝕊 0) (sphereBasepoint 0)

/-- Helper for Theorem 10.7.10: the antipodal first basis vector is a point of `S^0`. -/
private theorem oppositeSphereBasepoint_mem :
    (-EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 1)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
  -- The antipodal first basis vector still has norm one.
  simp

/-- Helper for Theorem 10.7.10: a distinguished non-basepoint of `S^0`. -/
private noncomputable def oppositeSphereBasepoint : 𝕊 0 :=
  ULift.up ⟨-EuclideanSpace.single 0 (1 : ℝ), oppositeSphereBasepoint_mem⟩

/-- Helper for Theorem 10.7.10: the chosen basepoint of `S^0` is distinct from its antipode. -/
private theorem sphereBasepoint_ne_oppositeSphereBasepoint :
    sphereBasepoint 0 ≠ oppositeSphereBasepoint := by
  -- Compare the zeroth Euclidean coordinates of the two concrete sphere points.
  intro h
  have h0 := congrArg (fun z : 𝕊 0 ↦ ((ULift.down z).1 0 : ℝ)) h
  simp [sphereBasepoint, oppositeSphereBasepoint] at h0
  linarith

/-- Helper for Theorem 10.7.10: every point of `S^0` is either the chosen basepoint or its
antipode. -/
private theorem sphereZero_eq_basepoint_or_opposite (z : 𝕊 0) :
    z = sphereBasepoint 0 ∨ z = oppositeSphereBasepoint := by
  -- A point of `S^0` has only one coordinate, whose square must be `1`.
  have hz : ‖((ULift.down z).1 : EuclideanSpace ℝ (Fin 1))‖ = 1 := by
    simpa using (ULift.down z).2
  rw [PiLp.norm_eq_of_L2] at hz
  have hx2 : (((ULift.down z).1 0 : ℝ)) ^ 2 = 1 := by
    simpa [Fin.sum_univ_one] using hz
  have hcases : (((ULift.down z).1 0 : ℝ)) = 1 ∨ (((ULift.down z).1 0 : ℝ)) = -1 := by
    -- Factor `x^2 - 1 = 0` as `(x - 1)(x + 1) = 0`.
    have hmul : ((((ULift.down z).1 0 : ℝ)) - 1) * ((((ULift.down z).1 0 : ℝ)) + 1) = 0 := by
      nlinarith [hx2]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hx | hx
    · left
      linarith
    · right
      linarith
  rcases hcases with hx | hx
  · left
    apply ULift.ext
    apply Subtype.ext
    ext i
    fin_cases i
    simpa [sphereBasepoint] using hx
  · right
    apply ULift.ext
    apply Subtype.ext
    ext i
    fin_cases i
    simpa [oppositeSphereBasepoint] using hx

/-- Helper for Theorem 10.7.10: `S^0` has decidable equality on its two points. -/
private noncomputable instance sZeroDecidableEq : DecidableEq (𝕊 0) :=
  Classical.decEq _

/-- Helper for Theorem 10.7.10: `S^0` is finite, with exactly the basepoint and antipode. -/
private noncomputable instance sZeroFintype : Fintype (𝕊 0) where
  elems := {sphereBasepoint 0, oppositeSphereBasepoint}
  complete z := by
    -- The explicit two-point classification exhausts the zero-sphere.
    rcases sphereZero_eq_basepoint_or_opposite z with h | h <;> simp [h]

/-- Helper for Theorem 10.7.10: the concrete zero-sphere inherits the `T1` topology of the metric
sphere. -/
private instance sZeroT1Space : T1Space (𝕊 0) := by
  -- Transport the separation property across the underlying `ULift` homeomorphism.
  convert Homeomorph.t1Space Homeomorph.ulift.symm
  infer_instance

/-- Helper for Theorem 10.7.10: the two-point sphere `S^0` is discrete. -/
private instance sZeroDiscreteTopology : DiscreteTopology (𝕊 0) := by
  infer_instance

/-- Helper for Theorem 10.7.10: the chosen based owner `sZeroBasedSpace` has decidable equality.
-/
private noncomputable instance sZeroBasedSpaceDecidableEq : DecidableEq sZeroBasedSpace.right := by
  change DecidableEq (𝕊 0)
  infer_instance

/-- Helper for Theorem 10.7.10: the chosen based owner `sZeroBasedSpace` has discrete topology.
-/
private instance sZeroBasedSpaceDiscreteTopology : DiscreteTopology sZeroBasedSpace.right := by
  change DiscreteTopology (𝕊 0)
  infer_instance

/-- Helper for Theorem 10.7.10: the family `(w, z) ↦ if z = sphereBasepoint 0 then * else w`
is continuous on `W × S^0`. -/
private theorem continuousSZeroPointFamily (W : BasedSpace) :
    Continuous fun p : W.right × sZeroBasedSpace.right ↦
      if p.2 = sphereBasepoint 0 then underTopBasepoint W else p.1 := by
  classical
  let s : Set (W.right × sZeroBasedSpace.right) := {p | p.2 = sphereBasepoint 0}
  have hsfrontier : frontier s = ∅ := by
    -- The basepoint slice is clopen because `S^0` is discrete.
    have hsclopen : IsClopen s := by
      refine (isClopen_discrete {sphereBasepoint 0}).preimage continuous_snd
    exact hsclopen.frontier_eq
  have hsagree : ∀ p ∈ frontier s, (underTopBasepoint W : W.right) = p.1 := by
    -- There is no frontier to check.
    intro p hp
    rw [hsfrontier] at hp
    cases hp
  simpa [s] using
    (Continuous.piecewise (s := s)
      (f := fun _ : W.right × sZeroBasedSpace.right ↦ underTopBasepoint W)
      (g := fun p : W.right × sZeroBasedSpace.right ↦ p.1)
      hsagree
      continuous_const
      continuous_fst)

/-- Helper for Theorem 10.7.10: a fixed point of `W` determines the explicit based map
`S^0 → W`. -/
private theorem continuousSZeroPointMap (W : BasedSpace) (w : W.right) :
    Continuous fun z : sZeroBasedSpace.right ↦
      if z = sphereBasepoint 0 then underTopBasepoint W else w := by
  -- Freeze the `W`-coordinate in the continuous two-variable family.
  simpa using
    (continuousSZeroPointFamily W).comp
      (Continuous.prodMk continuous_const continuous_id)

/-- Helper for Theorem 10.7.10: the explicit point-map `S^0 → W` is continuous. -/
private noncomputable def sZeroPointContinuousMap (W : BasedSpace) (w : W.right) :
    C(sZeroBasedSpace.right, W.right) :=
  { toFun := fun z ↦ if z = sphereBasepoint 0 then underTopBasepoint W else w
    continuous_toFun := continuousSZeroPointMap W w }

/-- Helper for Theorem 10.7.10: the explicit point-map sends the chosen basepoint of `S^0` to the
chosen basepoint of `W`. -/
private theorem sZeroPointToBasedMap_w (W : BasedSpace) (w : W.right) :
    sZeroBasedSpace.hom ≫ TopCat.ofHom (sZeroPointContinuousMap W w) = W.hom := by
  -- Evaluating the source terminal map lands at `sphereBasepoint 0`.
  ext u
  have hu : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom u
    rfl
  calc
    (sZeroBasedSpace.hom ≫ TopCat.ofHom (sZeroPointContinuousMap W w)) u =
        sZeroPointContinuousMap W w (sphereBasepoint 0) := rfl
    _ = underTopBasepoint W := by
      change (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else w) =
        underTopBasepoint W
      simp
    _ = W.hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = W.hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom u)) := by
      rw [hu]
    _ = W.hom u := by
      simp

/-- Helper for Theorem 10.7.10: the explicit point-map `S^0 → W` regarded as a based map. -/
private noncomputable def sZeroPointToBasedMap (W : BasedSpace) (w : W.right) :
    sZeroBasedSpace ⟶ W :=
  CategoryTheory.Under.homMk
    (TopCat.ofHom (sZeroPointContinuousMap W w))
    (sZeroPointToBasedMap_w W w)

/-- Helper for Theorem 10.7.10: the explicit point-map has the expected two-point formula. -/
@[simp] private theorem sZeroPointToBasedMap_apply (W : BasedSpace) (w : W.right)
    (z : sZeroBasedSpace.right) :
    (sZeroPointToBasedMap W w).right.hom z =
      if z = sphereBasepoint 0 then underTopBasepoint W else w :=
  rfl

/-- Helper for Theorem 10.7.10: the explicit point-map sends the antipode to the chosen point
`w`. -/
@[simp] private theorem sZeroPointToBasedMap_apply_opposite (W : BasedSpace) (w : W.right) :
    (sZeroPointToBasedMap W w).right.hom oppositeSphereBasepoint = w := by
  -- The antipode is not the chosen basepoint, so the explicit formula takes the `else` branch.
  rw [sZeroPointToBasedMap_apply]
  split_ifs with h
  · exact (sphereBasepoint_ne_oppositeSphereBasepoint h.symm).elim
  · rfl

/-- Helper for Theorem 10.7.10: every based map `S^0 → W` sends the chosen basepoint of `S^0` to
the chosen basepoint of `W`. -/
@[simp] private theorem basedMap_apply_sZeroBasepoint {W : BasedSpace} (f : sZeroBasedSpace ⟶ W) :
    f.right.hom (sphereBasepoint 0) = underTopBasepoint W := by
  -- Evaluate the `Under` commutativity condition at the unique terminal point.
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (CategoryTheory.Under.w f)
  simpa [sZeroBasedSpace] using hw

/-- Helper for Theorem 10.7.10: a based map out of `S^0` is determined by its value at the
antipode. -/
private theorem sZeroPointToBasedMap_eq_of_eval {W : BasedSpace} (f : sZeroBasedSpace ⟶ W) :
    sZeroPointToBasedMap W (f.right.hom oppositeSphereBasepoint) = f := by
  -- A map out of the two-point space `S^0` is determined by its values on the basepoint and the
  -- antipode.
  ext z
  rcases sphereZero_eq_basepoint_or_opposite z with rfl | rfl
  · rw [sZeroPointToBasedMap_apply, basedMap_apply_sZeroBasepoint]
    simp
  · rw [sZeroPointToBasedMap_apply_opposite]

/-- Helper for Theorem 10.7.10: the quotient relation on based maps already collapses to a single
based homotopy because based homotopy is an equivalence relation. -/
private theorem basedHomotopyRel_of_setoid {A B : BasedSpace} {u v : A ⟶ B}
    (h : (basedHomotopySetoid A B).r u v) :
    basedHomotopyRel u v := by
  -- Unfold the equivalence-closure relation and collapse it using the standard homotopy rules.
  rw [basedHomotopySetoid_iff] at h
  induction h with
  | rel _ _ huv =>
      exact huv
  | refl u =>
      exact ContinuousMap.HomotopicRel.refl u.right.hom
  | symm _ _ _ huv =>
      exact ContinuousMap.HomotopicRel.symm huv
  | trans _ _ _ _ _ huv hvw =>
      exact ContinuousMap.HomotopicRel.trans huv hvw

/-- Helper for Theorem 10.7.10: evaluating a based homotopy between maps `S^0 → W` at the
antipode produces a path between the corresponding points of `W`. -/
private theorem joinedEvalOpposite_of_basedHomotopy
    {W : BasedSpace} {f g : sZeroBasedSpace ⟶ W}
    (hfg : basedHomotopyRel f g) :
    Joined (f.right.hom oppositeSphereBasepoint) (g.right.hom oppositeSphereBasepoint) := by
  obtain ⟨Hfg⟩ := hfg
  -- Evaluate the underlying ordinary homotopy at the antipode to obtain a path in `W`.
  refine ⟨Path.mk
    (Hfg.toHomotopy.toContinuousMap.comp
      ((ContinuousMap.id I).prodMk
        (ContinuousMap.const I oppositeSphereBasepoint)))
    ?_ ?_⟩
  · change Hfg.toHomotopy (0, oppositeSphereBasepoint) =
        f.right.hom oppositeSphereBasepoint
    exact Hfg.toHomotopy.map_zero_left oppositeSphereBasepoint
  · change Hfg.toHomotopy (1, oppositeSphereBasepoint) =
        g.right.hom oppositeSphereBasepoint
    exact Hfg.toHomotopy.map_one_left oppositeSphereBasepoint

/-- Helper for Theorem 10.7.10: the class of a based map `S^0 → W` depends only on the path
component of its value at the antipode. -/
private theorem sZeroBasedHomotopyClassToZerothHomotopy_wellDefined
    {W : BasedSpace} {f g : sZeroBasedSpace ⟶ W}
    (hfg : (basedHomotopySetoid sZeroBasedSpace W).r f g) :
    (⟦f.right.hom oppositeSphereBasepoint⟧ : ZerothHomotopy W.right) =
      ⟦g.right.hom oppositeSphereBasepoint⟧ := by
  -- Collapse the setoid relation to an actual based homotopy, then evaluate at the antipode.
  exact Quotient.sound
    (joinedEvalOpposite_of_basedHomotopy (basedHomotopyRel_of_setoid hfg))

/-- Helper for Theorem 10.7.10: evaluating a based homotopy class `S^0 → W` at the antipode gives
the corresponding path component of `W`. -/
private noncomputable def sZeroBasedHomotopyClassToZerothHomotopy (W : BasedSpace) :
    Ho*[sZeroBasedSpace, W] → ZerothHomotopy W.right :=
  Quotient.lift
    (fun f : sZeroBasedSpace ⟶ W ↦
      (Quotient.mk _ (f.right.hom oppositeSphereBasepoint) :
        ZerothHomotopy W.right))
    (fun _ _ hfg ↦ sZeroBasedHomotopyClassToZerothHomotopy_wellDefined hfg)

/-- Helper for Theorem 10.7.10: a path in `W` between points `w₀` and `w₁` induces a based
homotopy between the corresponding explicit point-maps `S^0 → W`. -/
private theorem sZeroPointToBasedMap_homotopic_of_joined {W : BasedSpace}
    {w₀ w₁ : W.right} (hww : Joined w₀ w₁) :
    basedHomotopyRel (sZeroPointToBasedMap W w₀) (sZeroPointToBasedMap W w₁) := by
  rcases hww with ⟨γ⟩
  -- The basepoint branch stays fixed, while the antipodal branch follows the given path `γ`.
  refine ⟨{
    toHomotopy := {
      toFun := fun p : I × sZeroBasedSpace.right ↦
        if p.2 = sphereBasepoint 0 then underTopBasepoint W else γ p.1
      continuous_toFun := by
        simpa using
          (continuousSZeroPointFamily W).comp
            (Continuous.prodMk (γ.continuous.comp continuous_fst) continuous_snd)
      map_zero_left := ?_
      map_one_left := ?_ }
    prop' := ?_ }⟩
  · intro z
    -- At time `0` the moving branch starts at `w₀`.
    symm
    rw [sZeroPointToBasedMap_apply]
    simp [γ.source]
  · intro z
    -- At time `1` the moving branch ends at `w₁`.
    symm
    rw [sZeroPointToBasedMap_apply]
    simp [γ.target]
  · intro t z hz
    -- The relative condition holds because the basepoint branch is fixed for all `t`.
    rcases Set.mem_singleton_iff.mp hz with rfl
    change (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else γ t) =
      (if sphereBasepoint 0 = sphereBasepoint 0 then underTopBasepoint W else w₀)
    simp

/-- Helper for Theorem 10.7.10: a point of `W` determines the corresponding based homotopy class
`S^0 → W`. -/
private noncomputable def zerothHomotopyToSZeroBasedHomotopyClass (W : BasedSpace) :
    ZerothHomotopy W.right → Ho*[sZeroBasedSpace, W] :=
  Quotient.lift
    (fun w : W.right ↦
      ((Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) (sZeroPointToBasedMap W w)) :
        Ho*[sZeroBasedSpace, W]))
    (fun _ _ hww ↦ by
      -- The path between `w₀` and `w₁` gives the required based homotopy between the point-maps.
      exact Quotient.sound (Relation.EqvGen.rel _ _
        (sZeroPointToBasedMap_homotopic_of_joined hww)))

/-- Helper for Theorem 10.7.10: the two-point owner `S^0` models path components of the codomain
by evaluation at the antipode. -/
private noncomputable def sZeroBasedHomotopyClassesEquivZerothHomotopy
    (W : BasedSpace) :
    Ho*[sZeroBasedSpace, W] ≃ ZerothHomotopy W.right where
  toFun := sZeroBasedHomotopyClassToZerothHomotopy W
  invFun := zerothHomotopyToSZeroBasedHomotopyClass W
  left_inv := by
    intro a
    -- Reduce to a represented class and replace it by the explicit point-map determined by the
    -- antipodal value.
    refine Quotient.inductionOn a ?_
    intro f
    change
      ((Quotient.mk (basedHomotopySetoid sZeroBasedSpace W)
        (sZeroPointToBasedMap W (f.right.hom oppositeSphereBasepoint))) :
          Ho*[sZeroBasedSpace, W]) =
        Quotient.mk (basedHomotopySetoid sZeroBasedSpace W) f
    rw [sZeroPointToBasedMap_eq_of_eval]
  right_inv := by
    intro a
    -- Reduce to a represented path component and evaluate the corresponding explicit point-map at
    -- the antipode.
    refine Quotient.inductionOn a ?_
    intro w
    change
      (⟦(sZeroPointToBasedMap W w).right.hom oppositeSphereBasepoint⟧ :
          ZerothHomotopy W.right) = ⟦w⟧
    rw [sZeroPointToBasedMap_apply_opposite]

/-- Helper for Theorem 10.7.10: the `S^0`/`π₀` comparison is natural under postcomposition by a
based map. -/
private theorem sZeroBasedHomotopyClassesEquivZerothHomotopyNatural
    {W W' : BasedSpace} (g : W ⟶ W') :
    (sZeroBasedHomotopyClassesEquivZerothHomotopy W').toFun ∘
        (basedHomotopyClassesPostcompose sZeroBasedSpace g).toFun =
      zerothHomotopyMap g.right.hom ∘
        (sZeroBasedHomotopyClassesEquivZerothHomotopy W).toFun := by
  -- On a represented class `[f]`, both sides return the path component of `g (f(opp))`.
  funext a
  refine Quotient.inductionOn a ?_
  intro f
  change (⟦(f ≫ g).right.hom oppositeSphereBasepoint⟧ : ZerothHomotopy W'.right) =
    zerothHomotopyMap g.right.hom ⟦f.right.hom oppositeSphereBasepoint⟧
  rw [zerothHomotopyMap_mk]
  rfl

/-- Helper for Theorem 10.7.10: the Section 9.5 sphere-fiber owner identifies `π_ n(X, x)` with
the path components of `sphereBasepointFiber n x`. -/
private noncomputable def homotopyGroupEquivSphereBasepointFiberZeroth
    {W : Type*} [TopologicalSpace W] (n : ℕ) (x : W) :
    π_ n W x ≃ ZerothHomotopy (sphereBasepointFiber n x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace n x)
  (homotopyGroupEquivZerothHomotopyGenLoop n x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Theorem 10.7.10: a based map on the concrete boundary sphere gives a point of the
canonical Section 9.5 sphere-evaluation fiber after transporting through `Homeomorph.ulift`. -/
private noncomputable def sphereBoundaryBasedMapToSphereFiber
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (k₀ : C(sphereBoundary n, W)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x) :
    sphereBasepointFiber n x :=
  ⟨k₀.comp (topCatSphereToSphereBoundary n),
    (mem_sphereBasepointFiber_iff n x _).2 <| by
      -- The chosen TopCat sphere basepoint is the `ULift` of `sphereBoundaryBasepoint n`.
      simpa [sphereBasepoint, sphereBoundaryBasepoint] using hk₀⟩

/-- Helper for Theorem 10.7.10: if `π_ n(W, x)` is trivial, then every point of the Section 9.5
sphere fiber lies in the same path component as the constant based sphere map. -/
private theorem joinedConstSphereFiber_of_subsingletonHomotopyGroup
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W) (f : sphereBasepointFiber n x)
    (hπ : Subsingleton (π_ n W x)) :
    Joined f ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩ := by
  let e := homotopyGroupEquivSphereBasepointFiberZeroth n x
  have hsub : Subsingleton (ZerothHomotopy (sphereBasepointFiber n x)) := by
    let _ : Subsingleton (π_ n W x) := hπ
    exact Equiv.subsingleton e.symm
  let ηf : ZerothHomotopy (sphereBasepointFiber n x) := Quotient.mk _ f
  let ηc : ZerothHomotopy (sphereBasepointFiber n x) :=
    Quotient.mk _ ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩
  have hη : ηf = ηc := Subsingleton.elim _ _
  -- Equality in the path-component quotient is exactly the `Joined` relation.
  exact Quotient.exact hη

/-- Helper for Theorem 10.7.10: a path in the Section 9.5 sphere fiber uncarries to an honest
homotopy on the concrete boundary sphere. -/
private noncomputable def sphereBoundaryHomotopyToConstant_of_joinedFiberPoints
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (k₀ : C(sphereBoundary n, W)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x)
    (hjoin :
      Joined (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
        ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩) :
    k₀.Homotopy (ContinuousMap.const _ x) := by
  classical
  let γ : Path
      (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
      ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩ :=
    Classical.choice hjoin
  letI : CompactSpace (𝕊 n : TopCat) := by
    simpa using
      Homeomorph.compactSpace
        (Homeomorph.ulift.symm : sphereBoundary n ≃ₜ (𝕊 n : TopCat))
  letI : T2Space (𝕊 n : TopCat) := by
    simpa using
      Homeomorph.t2Space
        (Homeomorph.ulift.symm : sphereBoundary n ≃ₜ (𝕊 n : TopCat))
  let γmaps : C(I, C(𝕊 n, W)) :=
    (⟨Subtype.val, continuous_subtype_val⟩ : C(sphereBasepointFiber n x, C(𝕊 n, W))).comp
      γ.toContinuousMap
  let transportDomain : C(I × sphereBoundary n, I × (𝕊 n : TopCat)) :=
    ⟨fun p ↦ (p.1, ULift.up p.2), by fun_prop⟩
  let transported : C(I × sphereBoundary n, W) :=
    γmaps.uncurry.comp transportDomain
  refine ⟨transported, ?_, ?_⟩
  · intro y
    -- Evaluate the path at time `0` and undo the `ULift` transport of the sphere model.
    change ((γ 0).1) (ULift.up y) = k₀ y
    have hsource :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦ q.1 (ULift.up y))
        γ.source
    simpa [transported, transportDomain, γmaps, sphereBoundaryBasedMapToSphereFiber, sphereBasepoint,
      sphereBoundaryBasepoint] using hsource
  · intro y
    -- At time `1`, the path lands at the constant based map.
    change ((γ 1).1) (ULift.up y) = x
    have htarget :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦ q.1 (ULift.up y))
        γ.target
    simpa [transported, transportDomain, γmaps] using htarget

/-- Helper for Theorem 10.7.10: the radial cone map collapses the top slice
`{1} × sphereBoundary n` to the disk center and keeps the bottom slice as the boundary
inclusion. -/
private def sphereBoundaryConeQuotientMap (n : ℕ) : C(I × sphereBoundary n, unitDisk n) where
  toFun p := by
    refine ⟨(1 - (p.1 : ℝ)) • p.2.1, ?_⟩
    rw [mem_unitDisk_iff, norm_smul]
    have hp_nonneg : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
    have hp_le : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    rw [mem_sphereBoundary_iff.mp p.2.2, Real.norm_of_nonneg hp_nonneg]
    simpa using hp_le
  continuous_toFun := by
    fun_prop

/-- Helper for Theorem 10.7.10: the cone quotient restricts on the bottom slice to the boundary
inclusion. -/
@[simp] private theorem sphereBoundaryConeQuotientMap_zero
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (0, x) = sphereBoundaryInclusion n x := by
  apply Subtype.ext
  change (1 - ((0 : I) : ℝ)) • (x : V[n]) = (x : V[n])
  simp

/-- Helper for Theorem 10.7.10: the cone quotient collapses the top slice to the disk center. -/
@[simp] private theorem sphereBoundaryConeQuotientMap_one
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (1, x) =
      (⟨0, by simp [mem_unitDisk_iff]⟩ : unitDisk n) := by
  apply Subtype.ext
  change (1 - ((1 : I) : ℝ)) • (x : V[n]) = 0
  simp

/-- Helper for Theorem 10.7.10: the cone quotient `I × S^n → D^(n+1)` is surjective. -/
private theorem sphereBoundaryConeQuotientMap_surjective (n : ℕ) :
    Function.Surjective (sphereBoundaryConeQuotientMap n) := by
  intro y
  by_cases hy0 : (y : V[n]) = 0
  · refine ⟨(1, sphereBoundaryBasepoint n), ?_⟩
    rw [sphereBoundaryConeQuotientMap_one]
    apply Subtype.ext
    simpa [hy0]
  · have hy_norm_nonzero : ‖(y : V[n])‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hy0
    have hy_mem : ‖(y : V[n])‖ ≤ 1 := mem_unitDisk_iff.mp y.2
    let x : sphereBoundary n := by
      refine ⟨‖(y : V[n])‖⁻¹ • (y : V[n]), ?_⟩
      rw [mem_sphereBoundary_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      field_simp [hy_norm_nonzero]
    let t : I := ⟨1 - ‖(y : V[n])‖, by
      constructor
      · linarith [hy_mem]
      · linarith [norm_nonneg (y : V[n])]⟩
    refine ⟨(t, x), ?_⟩
    apply Subtype.ext
    change (1 - (t : ℝ)) • (x : V[n]) = (y : V[n])
    dsimp [t, x]
    rw [show 1 - (1 - ‖(y : V[n])‖) = ‖(y : V[n])‖ by ring, smul_smul]
    rw [mul_inv_cancel₀ hy_norm_nonzero, one_smul]

/-- Helper for Theorem 10.7.10: a boundary nullhomotopy is constant on the fibers of the cone
quotient and therefore descends to the disk. -/
private theorem sphereBoundaryHomotopy_factorsThrough_coneQuotient
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    {k₀ : C(sphereBoundary n, W)}
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap (sphereBoundaryConeQuotientMap n) := by
  intro p q hpq
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  change H (t, a) = H (s, b)
  have hvec : (1 - (t : ℝ)) • (a : V[n]) = (1 - (s : ℝ)) • (b : V[n]) := by
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
  · have hab_val : (a : V[n]) = (b : V[n]) := by
      apply (smul_right_injective (M := V[n]) htop)
      simpa [hscale] using hvec
    have hab : a = b := Subtype.ext hab_val
    have hts : t = s := Subtype.ext <| by linarith
    rw [hts, hab]

/-- Helper for Theorem 10.7.10: a nullhomotopy of a boundary sphere map descends along the cone
quotient to a continuous filler on `unitDisk n`. -/
private noncomputable def unitDiskLift_of_sphereBoundaryHomotopyToConstant
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (k₀ : C(sphereBoundary n, W))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    C(unitDisk n, W) :=
  let q := sphereBoundaryConeQuotientMap n
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (sphereBoundaryConeQuotientMap_surjective n) q.continuous
  -- Descend the nullhomotopy across the compact cone quotient `I × S^n → D^(n+1)`.
  hq.lift H.toContinuousMap
    (sphereBoundaryHomotopy_factorsThrough_coneQuotient n x H)

/-- Helper for Theorem 10.7.10: the descended disk filler restricts on the boundary to the
original sphere map. -/
private theorem unitDiskLift_of_sphereBoundaryHomotopyToConstant_comp
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (k₀ : C(sphereBoundary n, W))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    (unitDiskLift_of_sphereBoundaryHomotopyToConstant n x k₀ H).comp
        (sphereBoundaryInclusion n) = k₀ := by
  let q := sphereBoundaryConeQuotientMap n
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (sphereBoundaryConeQuotientMap_surjective n) q.continuous
  let hfactor := sphereBoundaryHomotopy_factorsThrough_coneQuotient n x H
  ext y
  -- Evaluate the descended equality on the bottom slice `t = 0`.
  have hdesc :=
    congrArg
      (fun f : C(I × sphereBoundary n, W) ↦ f (0, y))
      (hq.lift_comp H.toContinuousMap hfactor)
  change (unitDiskLift_of_sphereBoundaryHomotopyToConstant n x k₀ H)
      (sphereBoundaryConeQuotientMap n (0, y)) = H (0, y) at hdesc
  simpa [unitDiskLift_of_sphereBoundaryHomotopyToConstant, sphereBoundaryConeQuotientMap_zero]
    using hdesc

/-- Helper for Theorem 10.7.10: the straight segment from a boundary point to the distinguished
boundary basepoint stays inside the unit disk. -/
private theorem segmentToBoundaryBasepoint_mem_unitDisk (n : ℕ) (x : sphereBoundary n) (t : I) :
    (1 - (t : ℝ)) • x.1 + (t : ℝ) • (sphereBoundaryBasepoint n).1 ∈ unitDisk n := by
  -- The closed disk is convex, so the norm of the convex combination is at most `1`.
  rw [mem_unitDisk_iff]
  calc
    ‖(1 - (t : ℝ)) • x.1 + (t : ℝ) • (sphereBoundaryBasepoint n).1‖
        ≤ ‖(1 - (t : ℝ)) • x.1‖ + ‖(t : ℝ) • (sphereBoundaryBasepoint n).1‖ := by
          simpa using norm_add_le ((1 - (t : ℝ)) • x.1) ((t : ℝ) • (sphereBoundaryBasepoint n).1)
    _ = (1 - (t : ℝ)) * ‖x.1‖ + (t : ℝ) * ‖(sphereBoundaryBasepoint n).1‖ := by
          rw [norm_smul, norm_smul,
            Real.norm_of_nonneg (sub_nonneg.mpr t.2.2),
            Real.norm_of_nonneg t.2.1]
    _ = 1 := by
          rw [mem_sphereBoundary_iff.mp x.2, mem_sphereBoundary_iff.mp (sphereBoundaryBasepoint n).2]
          ring

/-- Helper for Theorem 10.7.10: contracting the boundary sphere inside the disk to the chosen
boundary basepoint gives a homotopy that fixes that basepoint throughout. -/
private noncomputable def sphereBoundaryToBasepointHomotopy
    (n : ℕ) {W : Type*} [TopologicalSpace W] (U : C(unitDisk n, W)) :
    (U.comp (sphereBoundaryInclusion n)).Homotopy
      (ContinuousMap.const (sphereBoundary n) (U (sphereBoundaryInclusion n (sphereBoundaryBasepoint n)))) :=
  { toFun := fun p ↦
      U ⟨(1 - (p.1 : ℝ)) • p.2.1 + (p.1 : ℝ) • (sphereBoundaryBasepoint n).1,
        segmentToBoundaryBasepoint_mem_unitDisk n p.2 p.1⟩
    continuous_toFun := by
      -- The linear contraction is continuous before postcomposition with `U`.
      fun_prop
    map_zero_left := by
      intro x
      change U ⟨(1 - ((0 : I) : ℝ)) • x.1 + ((0 : I) : ℝ) • (sphereBoundaryBasepoint n).1,
          segmentToBoundaryBasepoint_mem_unitDisk n x 0⟩ =
        U (sphereBoundaryInclusion n x)
      simp [sphereBoundaryInclusion]
    map_one_left := by
      intro x
      change U ⟨(1 - ((1 : I) : ℝ)) • x.1 + ((1 : I) : ℝ) • (sphereBoundaryBasepoint n).1,
          segmentToBoundaryBasepoint_mem_unitDisk n x 1⟩ =
        U (sphereBoundaryInclusion n (sphereBoundaryBasepoint n))
      simp [sphereBoundaryInclusion] }

/-- Helper for Theorem 10.7.10: the basepoint stays fixed throughout the boundary contraction
coming from a disk extension. -/
private theorem sphereBoundaryToBasepointHomotopy_basepoint
    (n : ℕ) {W : Type*} [TopologicalSpace W] (U : C(unitDisk n, W)) :
    ∀ t : I, sphereBoundaryToBasepointHomotopy n U (t, sphereBoundaryBasepoint n) =
      U (sphereBoundaryInclusion n (sphereBoundaryBasepoint n)) := by
  -- Along the distinguished boundary point, the contraction is constant.
  intro t
  change U ⟨(1 - (t : ℝ)) • (sphereBoundaryBasepoint n).1 + (t : ℝ) • (sphereBoundaryBasepoint n).1,
      segmentToBoundaryBasepoint_mem_unitDisk n (sphereBoundaryBasepoint n) t⟩ =
    U (sphereBoundaryInclusion n (sphereBoundaryBasepoint n))
  apply congrArg U
  apply Subtype.ext
  calc
    (1 - (t : ℝ)) • (sphereBoundaryBasepoint n).1 + (t : ℝ) • (sphereBoundaryBasepoint n).1
        = ((1 - (t : ℝ)) + (t : ℝ)) • (sphereBoundaryBasepoint n).1 := by
            rw [← add_smul]
    _ = (sphereBoundaryBasepoint n).1 := by
          ring_nf
          simp
    _ = ↑((sphereBoundaryInclusion n) (sphereBoundaryBasepoint n)) := by
          rfl

/-- Helper for Theorem 10.7.10: a disk extension of a based boundary map yields a path in the
Section 9.5 sphere fiber from that map to the constant based map. -/
private theorem joinedConstSphereFiber_of_unitDiskExtension
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (k₀ : C(sphereBoundary n, W)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x)
    (U : C(unitDisk n, W))
    (hU : U.comp (sphereBoundaryInclusion n) = k₀) :
    Joined (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
      ⟨ContinuousMap.const (TopCat.sphere.{0} n) x, by simp [mem_sphereBasepointFiber_iff]⟩ := by
  let Hraw := sphereBoundaryToBasepointHomotopy n U
  have hbase :
      U (sphereBoundaryInclusion n (sphereBoundaryBasepoint n)) = x := by
    -- The extension agrees with the given based boundary map at the chosen basepoint.
    simpa [hk₀] using
      congrArg (fun h : C(sphereBoundary n, W) ↦ h (sphereBoundaryBasepoint n)) hU
  have hHbase : ∀ t : I, Hraw (t, sphereBoundaryBasepoint n) = x := by
    -- The raw contraction already fixes the distinguished boundary basepoint, and that endpoint is
    -- exactly `x` by the boundary extension equation.
    intro t
    simpa [hbase] using sphereBoundaryToBasepointHomotopy_basepoint (n := n) U t
  let γ : Path
      (sphereBoundaryBasedMapToSphereFiber n x k₀ hk₀)
      ⟨ContinuousMap.const (TopCat.sphere.{0} n) x, by simp [mem_sphereBasepointFiber_iff]⟩ :=
    Path.mk
      { toFun := fun t ↦
          ⟨⟨fun y ↦ Hraw (t, ULift.down y), by
              let slice : (𝕊 n : TopCat) → I × sphereBoundary n := fun s ↦ (t, ULift.down s)
              have hslice : Continuous slice := by
                fun_prop
              -- Each time-slice of the homotopy is a continuous sphere map.
              simpa [slice] using Hraw.continuous.comp hslice⟩,
            by
              -- The boundary contraction fixes the distinguished basepoint at every time.
              rw [mem_sphereBasepointFiber_iff]
              simpa [sphereBasepoint, sphereBoundaryBasepoint] using hHbase t⟩
        continuous_toFun := by
          have huncurry :
              Continuous fun p : I × (𝕊 n : TopCat) ↦ Hraw (p.1, ULift.down p.2) := by
            exact Hraw.continuous.comp (by fun_prop)
          have hfamily :
              Continuous fun t : I ↦
                (⟨fun y ↦ Hraw (t, ULift.down y), by
                    let slice : (𝕊 n : TopCat) → I × sphereBoundary n := fun y ↦ (t, ULift.down y)
                    have hslice : Continuous slice := by
                      fun_prop
                    simpa [slice] using Hraw.continuous.comp hslice⟩ :
                  C((𝕊 n : TopCat), W)) := by
            exact ContinuousMap.continuous_of_continuous_uncurry _ huncurry
          -- Lift the family of maps to the based-map fiber using the fixed-basepoint equation.
          exact hfamily.subtype_mk (fun t ↦ by
            rw [mem_sphereBasepointFiber_iff]
            simpa [sphereBasepoint, sphereBoundaryBasepoint] using hHbase t) }
      (by
        apply Subtype.ext
        ext y
        change Hraw (0, ULift.down y) = k₀ (ULift.down y)
        simpa [hU] using Hraw.apply_zero (ULift.down y))
      (by
        apply Subtype.ext
        ext y
        change Hraw (1, ULift.down y) = x
        simpa [hbase] using Hraw.apply_one (ULift.down y))
  exact ⟨γ⟩

/-- Helper for Theorem 10.7.10: if every based sphere map into `X` extends across the disk, then
`π_ n(X, x)` is trivial. -/
private theorem subsingletonHomotopyGroup_of_unitDiskExtensions
    (n : ℕ) {W : Type*} [TopologicalSpace W] (x : W)
    (hExtend :
      ∀ (k₀ : C(sphereBoundary n, W)),
        k₀ (sphereBoundaryBasepoint n) = x →
          ∃ U : C(unitDisk n, W), U.comp (sphereBoundaryInclusion n) = k₀) :
    Subsingleton (π_ n W x) := by
  let e : π_ n W x ≃ ZerothHomotopy (sphereBasepointFiber n x) :=
    homotopyGroupEquivSphereBasepointFiberZeroth n x
  have hfiber :
      Subsingleton (ZerothHomotopy (sphereBasepointFiber n x)) := by
    classical
    refine ⟨fun a b ↦ ?_⟩
    let c : ZerothHomotopy (sphereBasepointFiber n x) :=
      Quotient.mk _ ⟨ContinuousMap.const (TopCat.sphere.{0} n) x,
        by simp [mem_sphereBasepointFiber_iff]⟩
    refine Quotient.inductionOn₂ a b ?_
    intro f g
    let kf : C(sphereBoundary n, W) := f.1.comp (sphereBoundaryToTopCatSphere n)
    have hkf : kf (sphereBoundaryBasepoint n) = x := by
      have hfbase : f.1 (sphereBasepoint n) = x :=
        (mem_sphereBasepointFiber_iff n x f.1).1 f.2
      simpa [kf, sphereBoundaryToTopCatSphere, sphereBasepoint, sphereBoundaryBasepoint] using hfbase
    obtain ⟨Uf, hUf⟩ := hExtend kf hkf
    have hf :
        (Quotient.mk _ f : ZerothHomotopy (sphereBasepointFiber n x)) = c := by
      -- Every represented class is joined to the constant class via its disk extension.
      exact Quotient.sound
        (joinedConstSphereFiber_of_unitDiskExtension n x kf hkf Uf hUf)
    let kg : C(sphereBoundary n, W) := g.1.comp (sphereBoundaryToTopCatSphere n)
    have hkg : kg (sphereBoundaryBasepoint n) = x := by
      have hgbase : g.1 (sphereBasepoint n) = x :=
        (mem_sphereBasepointFiber_iff n x g.1).1 g.2
      simpa [kg, sphereBoundaryToTopCatSphere, sphereBasepoint, sphereBoundaryBasepoint] using hgbase
    obtain ⟨Ug, hUg⟩ := hExtend kg hkg
    have hg :
        (Quotient.mk _ g : ZerothHomotopy (sphereBasepointFiber n x)) = c := by
      -- The same contraction argument applies to the second represented class.
      exact Quotient.sound
        (joinedConstSphereFiber_of_unitDiskExtension n x kg hkg Ug hUg)
    exact hf.trans hg.symm
  let _ : Subsingleton (ZerothHomotopy (sphereBasepointFiber n x)) := hfiber
  exact ⟨fun a b ↦ e.injective (Subsingleton.elim (e a) (e b))⟩

/-- Helper for Theorem 10.7.10: the explicit sphere/disk filler package forces the corresponding
homotopy groups of every homotopy fiber `F(e; y)` to be trivial. -/
private theorem subsingletonHomotopyGroup_homotopyFiberAt_of_explicitSphereConeHelp
    (n : ℕ) (y : X)
    (hFill :
      ∀ (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
        (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          ∃ G : C(unitDisk n, X), ∃ K : (e.comp G).Homotopy g,
            G.comp (sphereBoundaryInclusion n) = f ∧
              ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z) :
    Subsingleton
      (π_ n (homotopyFiberAt e y).right (underTopBasepoint (homotopyFiberAt e y))) := by
  -- Use the already-packaged homotopy-fiber disk-lift theorem, then contract every based sphere
  -- map through the chosen boundary basepoint inside the disk.
  refine
    subsingletonHomotopyGroup_of_unitDiskExtensions
      (n := n) (x := underTopBasepoint (homotopyFiberAt e y)) ?_
  intro u hu
  exact homotopyFiberDiskLift_of_explicitSphereConeHelp (e := e) n y hFill u hu

/-- Helper for Theorem 10.7.10: in a group-exact pair `A ⟶ B ⟶ C`, a trivial source forces the
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
    -- The triviality of the source group collapses every source element to `1`.
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

/-- Helper for Theorem 10.7.10: in a group-exact pair `A ⟶ B ⟶ C`, a trivial target forces the
first map to be surjective. -/
private theorem surjective_of_mulExact_of_subsingleton_target
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B →* C) (hfg : Function.MulExact f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro y
  -- Exactness identifies every target element with the image of a source element because the
  -- target obstruction group is trivial.
  have hy : g y = 1 := by
    exact Subsingleton.elim _ _
  exact (hfg _).mp hy

/-- Helper for Theorem 10.7.10: in a pointed-exact pair `A ⟶ B ⟶ C`, a trivial target pointed
set forces the first map to be surjective. -/
private theorem surjective_of_pointedExact_of_subsingleton_target
    {A B C : Pointed} (f : A ⟶ B) (g : B ⟶ C) (hfg : PointedExact f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro b
  -- Exactness identifies every element of `B` with an image because the target pointed set has
  -- only its distinguished point.
  have hb : g b = C.point := by
    exact Subsingleton.elim _ _
  exact (hfg b).mp hb

/-- Helper for Theorem 10.7.10: trivial `π_ n` in a homotopy fiber already gives the disk
extension step for based sphere maps into that fiber. -/
private theorem homotopyFiberDiskExtension_ofSubsingletonHomotopyGroup
    (n : ℕ) (y : X)
    (k₀ : C(sphereBoundary n, (homotopyFiberAt e y).right))
    (hk₀ : k₀ (sphereBoundaryBasepoint n) = underTopBasepoint (homotopyFiberAt e y))
    (hFiber :
      Subsingleton
        (π_ n (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)))) :
    ∃ k : C(unitDisk n, (homotopyFiberAt e y).right),
      k.comp (sphereBoundaryInclusion n) = k₀ := by
  let x0 : (homotopyFiberAt e y).right := underTopBasepoint (homotopyFiberAt e y)
  have hjoin :
      Joined
        (sphereBoundaryBasedMapToSphereFiber n x0 k₀ hk₀)
        ⟨ContinuousMap.const (TopCat.sphere.{0} n) x0, by simp [mem_sphereBasepointFiber_iff]⟩ := by
    -- Trivial `π_ n` makes the packaged based sphere map path-connected to the constant datum.
    simpa [x0] using
      joinedConstSphereFiber_of_subsingletonHomotopyGroup
        n x0
        (sphereBoundaryBasedMapToSphereFiber n x0 k₀ hk₀)
        hFiber
  let H :
      k₀.Homotopy (ContinuousMap.const (sphereBoundary n) x0) :=
    sphereBoundaryHomotopyToConstant_of_joinedFiberPoints n x0 k₀ hk₀ hjoin
  refine ⟨unitDiskLift_of_sphereBoundaryHomotopyToConstant n x0 k₀ H, ?_⟩
  -- Descend the nullhomotopy along the cone quotient and read off its boundary value.
  exact unitDiskLift_of_sphereBoundaryHomotopyToConstant_comp n x0 k₀ H

/-- Helper for Theorem 10.7.10: on loop representatives, the canonical `π₁` comparison with the
fundamental group commutes with postcomposition by `e`. -/
private theorem genLoopEquivOfUnique_genLoopMap_eq_pathMap
    (y : X) (γ : Ω^ (Fin 1) X y) :
    genLoopEquivOfUnique (X := X') (x := e y) (Fin 1) (genLoopMap e γ) =
      (genLoopEquivOfUnique (X := X) (x := y) (Fin 1) γ).map e.continuous := by
  -- Both paths are evaluated by the unique coordinate and then postcomposed with `e`.
  ext t
  rfl

/-- Helper for Theorem 10.7.10: under the canonical `π₁ ≃ FundamentalGroup` comparison, the
degree-`1` induced map of `e` is `FundamentalGroup.map e y`. -/
private theorem piOneEStar_eq_fundamentalGroupMap
    (y : X) :
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X' (e y) ≃ FundamentalGroup X' (e y)) ∘
        e.eStar 1 y =
      (FundamentalGroup.map e y) ∘
        (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X y ≃ FundamentalGroup X y) := by
  -- Reduce to loop representatives, where both constructions literally postcompose by `e`.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Path.Homotopic.Quotient.mk
        (genLoopEquivOfUnique (X := X') (x := e y) (Fin 1) (genLoopMap e γ)) =
      Path.Homotopic.Quotient.mk
        ((genLoopEquivOfUnique (X := X) (x := y) (Fin 1) γ).map e.continuous)
  exact congrArg Path.Homotopic.Quotient.mk
    (genLoopEquivOfUnique_genLoopMap_eq_pathMap (e := e) y γ)

/-- Helper for Theorem 10.7.10: forgetting the path coordinate of `F(e; y)` recovers the source
point in `X`. -/
private noncomputable def homotopyFiberPointProjection (y : X) :
    C((homotopyFiberAt e y).right, X) where
  toFun q := q.point.down
  continuous_toFun := by
    -- Read the source coordinate of the homotopy-fiber point and then forget the `ULift`.
    simpa [homotopyFiberAt, HomotopyFiber.point] using
      (continuous_uliftDown.comp
        ((continuous_fst.comp continuous_subtype_val).comp
          (continuous_id : Continuous fun q : (homotopyFiberAt e y).right ↦ q)))

/-- Helper for Theorem 10.7.10: evaluating `homotopyFiberPointProjection` just reads the stored
point coordinate. -/
@[simp] private theorem homotopyFiberPointProjection_apply (y : X)
    (q : (homotopyFiberAt e y).right) :
    homotopyFiberPointProjection (e := e) y q = q.point.down :=
  rfl

/-- Helper for Theorem 10.7.10: the homotopy-fiber basepoint projects back to the chosen source
basepoint `y`. -/
@[simp] private theorem homotopyFiberPointProjection_basepoint (y : X) :
    homotopyFiberPointProjection (e := e) y
        (underTopBasepoint (homotopyFiberAt e y)) = y := by
  -- The canonical homotopy-fiber basepoint stores the original source point `y`.
  simp [homotopyFiberPointProjection, underTopBasepoint_homotopyFiber,
    HomotopyFiber.point_basepoint, underTopBasepoint_underTopOfPoint]

/-- Helper for Theorem 10.7.10: trivial `π₀` of `F(e; y)` makes every fiber point path-connected
to the canonical basepoint. -/
private theorem joined_basepoint_of_subsingletonPiZero
    (y : X) (q : (homotopyFiberAt e y).right)
    (hq :
      Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)))) :
    Joined q (underTopBasepoint (homotopyFiberAt e y)) := by
  let e0 :
      π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)) ≃
        ZerothHomotopy ((homotopyFiberAt e y).right) :=
    HomotopyGroup.pi0EquivZerothHomotopy
  have hsub : Subsingleton (ZerothHomotopy ((homotopyFiberAt e y).right)) := by
    let _ : Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y))) := hq
    exact Equiv.subsingleton e0.symm
  let ηq : ZerothHomotopy ((homotopyFiberAt e y).right) := Quotient.mk _ q
  let η0 : ZerothHomotopy ((homotopyFiberAt e y).right) :=
    Quotient.mk _ (underTopBasepoint (homotopyFiberAt e y))
  have hη : ηq = η0 := Subsingleton.elim _ _
  -- Equality in `ZerothHomotopy` is exactly the existence of a path in the fiber.
  exact Quotient.exact hη

/-- Helper for Theorem 10.7.10: trivial `π₀` of `F(e; y)` makes the ordinary path-component
quotient `ZerothHomotopy (F(e; y))` subsingleton. -/
private theorem subsingletonZerothHomotopy_homotopyFiberAt_of_subsingletonPiZero
    (y : X)
    (hFiber :
      Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)))) :
    Subsingleton (ZerothHomotopy ((homotopyFiberAt e y).right)) := by
  -- Transport the degree-`0` homotopy-group triviality through the canonical `π₀` comparison.
  let e0 :
      π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)) ≃
        ZerothHomotopy ((homotopyFiberAt e y).right) :=
    HomotopyGroup.pi0EquivZerothHomotopy
  let _ :
      Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y))) :=
    hFiber
  exact Equiv.subsingleton e0.symm

/-- Helper for Theorem 10.7.10: if every homotopy fiber has trivial `π₀`, then the ambient map is
injective on path components. -/
private theorem injectiveZerothHomotopy_of_subsingletonHomotopyFiberPiZero
    (hFiber :
      ∀ y : X,
        Subsingleton
          (π_ 0 (homotopyFiberAt e y).right
            (underTopBasepoint (homotopyFiberAt e y)))) :
    Function.Injective (zerothHomotopyMap e) := by
  intro a b hab
  revert hab
  refine Quotient.inductionOn₂ a b ?_
  intro x x' hab
  rcases (Quotient.exact hab : Joined (e x) (e x')) with ⟨β⟩
  let q : (homotopyFiberAt e x').right :=
    HomotopyFiber.mk
      (ULift.up x)
      (PathSpace.ofPath ((β.map continuous_uliftUp).symm))
      (by
        -- The chosen homotopy-fiber path ends at the image of the stored source point `x`.
        change uliftContinuousMapAcrossUniverses e (ULift.up x) =
          (PathSpace.ofPath ((β.map continuous_uliftUp).symm)).endpoint
        rw [PathSpace.endpoint_ofPath]
        rfl)
  have hjoinFiber :
      Joined q (underTopBasepoint (homotopyFiberAt e x')) := by
    -- Trivial `π₀` collapses the chosen fiber point to the canonical homotopy-fiber basepoint.
    exact joined_basepoint_of_subsingletonPiZero (e := e) x' q (hFiber x')
  rcases hjoinFiber with ⟨δ⟩
  refine Quotient.sound ?_
  refine ⟨Path.mk ((homotopyFiberPointProjection (e := e) x').comp δ.toContinuousMap) ?_ ?_⟩
  · -- Projecting the path in the fiber starts at the chosen source point `x`.
    change (HomotopyFiber.point (δ 0)).down = x
    rw [δ.source]
    rfl
  · -- Projecting the path in the fiber ends at the basepoint source `x'`.
    change (HomotopyFiber.point (δ 1)).down = x'
    rw [δ.target]
    simp [underTopBasepoint_homotopyFiber, HomotopyFiber.point_basepoint,
      underTopBasepoint_underTopOfPoint]

/-- Helper for Theorem 10.7.10: after transporting the stage-`0` tail of
`fiberSequenceGeneratedBy (underTopOfPointMapAcrossUniverses e y)` to the public Chapter 9
owners, trivial `π₀(F(e; y))` should force surjectivity of `FundamentalGroup.map e y`. -/
private theorem fundamentalGroupMap_surjective_of_subsingletonHomotopyFiberPiZero
    (y : X)
    (hFiber :
      Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)))) :
    Function.Surjective (FundamentalGroup.map e y) := by
  let _ :
      Subsingleton (ZerothHomotopy ((homotopyFiberAt e y).right)) :=
    subsingletonZerothHomotopy_homotopyFiberAt_of_subsingletonPiZero
      (e := e) y hFiber
  -- TODO: specialize the stage-`2` exactness statement for
  -- `fiberSequenceGeneratedBy (underTopOfPointMapAcrossUniverses e y)` to the sphere `S^0`,
  -- identify the two loop-space terms with `FundamentalGroup X y` and `FundamentalGroup X' (e y)`
  -- via `π₀(Ω-) ≃ π₁(-)`, identify the obstruction term with
  -- `ZerothHomotopy ((homotopyFiberAt e y).right)`, and then apply
  -- `surjective_of_pointedExact_of_subsingleton_target`.
  sorry

/-- Helper for Theorem 10.7.10: if every homotopy fiber `F(e; y)` has trivial `π_ n`, then the
Chapter 9 two-degree owner `HasPiInjectiveSurjectiveSucc n e` follows. -/
private theorem piOneSurjective_of_subsingletonHomotopyFiberPiZero
    (y : X)
    (hFiber :
      Subsingleton
        (π_ 0 (homotopyFiberAt e y).right
          (underTopBasepoint (homotopyFiberAt e y)))) :
    Function.Surjective (e.eStar 1 y) := by
  have hSurjFG :
      Function.Surjective (FundamentalGroup.map e y) :=
    fundamentalGroupMap_surjective_of_subsingletonHomotopyFiberPiZero
      (e := e) y hFiber
  intro b
  let bFG : FundamentalGroup X' (e y) :=
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X' (e y) ≃ FundamentalGroup X' (e y)) b
  rcases hSurjFG bFG with ⟨aFG, haFG⟩
  refine
    ⟨(HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X y ≃ FundamentalGroup X y).symm aFG, ?_⟩
  apply (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X' (e y) ≃ FundamentalGroup X' (e y)).injective
  -- Transport the chosen fundamental-group preimage back through the canonical `π₁` comparison.
  calc
    (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X' (e y) ≃ FundamentalGroup X' (e y))
        (e.eStar 1 y
          ((HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X y ≃ FundamentalGroup X y).symm aFG)) =
      (FundamentalGroup.map e y)
        ((HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X y ≃ FundamentalGroup X y)
          ((HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X y ≃ FundamentalGroup X y).symm aFG)) := by
            exact
              congrFun
                (piOneEStar_eq_fundamentalGroupMap (e := e) y)
                ((HomotopyGroup.pi1EquivFundamentalGroup :
                  π_ 1 X y ≃ FundamentalGroup X y).symm aFG)
    _ = (FundamentalGroup.map e y) aFG := by
          rw [Equiv.apply_symm_apply]
    _ = bFG := haFG
    _ = (HomotopyGroup.pi1EquivFundamentalGroup : π_ 1 X' (e y) ≃ FundamentalGroup X' (e y)) b :=
          rfl

/-- Helper for Theorem 10.7.10: the positive-degree tail of the homotopy-fiber sequence for
`underTopOfPointMapAcrossUniverses e y` should normalize to the public maps
`e.eStarMulHom m y` and `e.eStarMulHom (m + 1) y`. -/
private theorem homotopyFiberTailMulExact
    (m : ℕ) (y : X) :
    ∃ fiberToSource :
        π_ (m + 1) (homotopyFiberAt e y).right
            (underTopBasepoint (homotopyFiberAt e y)) →*
          π_ (m + 1) X y,
      Function.MulExact fiberToSource (e.eStarMulHom m y) ∧
        ∃ targetToFiber :
            π_ (m + 2) X' (e y) →*
              π_ (m + 1) (homotopyFiberAt e y).right
                (underTopBasepoint (homotopyFiberAt e y)),
          Function.MulExact (e.eStarMulHom (m + 1) y) targetToFiber := by
  -- TODO: instantiate the Chapter 8 exactness theorem on
  -- `fiberSequenceGeneratedBy (underTopOfPointMapAcrossUniverses e y)` and transport the loop-tail
  -- maps to the public owners `e.eStarMulHom m y` and `e.eStarMulHom (m + 1) y`.
  sorry

/-- Helper for Theorem 10.7.10: if every homotopy fiber `F(e; y)` has trivial `π_ n`, then the
Chapter 9 two-degree owner `HasPiInjectiveSurjectiveSucc n e` follows. -/
private theorem hasPiInjectiveSurjectiveSucc_of_subsingletonHomotopyGroup_homotopyFiberAt
    (n : ℕ)
    (hFiber :
      ∀ y : X,
        Subsingleton
          (π_ n (homotopyFiberAt e y).right
            (underTopBasepoint (homotopyFiberAt e y)))) :
    HasPiInjectiveSurjectiveSucc n e := by
  -- Route correction: the geometric filler argument has already been normalized to pointwise
  -- triviality of the homotopy-fiber group. The remaining missing step is the Chapter 8/9 exact
  -- sequence bridge from `π_n(F(e; y)) = 0` to injectivity on `π_n` and surjectivity on
  -- `π_(n + 1)`.
  cases n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro y
        let eDom : π_ 0 X y ≃ ZerothHomotopy X := HomotopyGroup.pi0EquivZerothHomotopy
        let eCod : π_ 0 X' (e y) ≃ ZerothHomotopy X' := HomotopyGroup.pi0EquivZerothHomotopy
        have hZero :
            Function.Injective (zerothHomotopyMap e) :=
          injectiveZerothHomotopy_of_subsingletonHomotopyFiberPiZero
            (e := e) hFiber
        have hNat (c : π_ 0 X y) :
            zerothHomotopyMap e (eDom c) = eCod (e.eStar 0 y c) := by
          refine Quotient.inductionOn c ?_
          intro γ
          rfl
        intro a b hab
        apply eDom.injective
        apply hZero
        -- Transport the equality of `e_*` back to path components via the canonical `π₀` model.
        calc
          zerothHomotopyMap e (eDom a) = eCod (e.eStar 0 y a) := hNat a
          _ = eCod (e.eStar 0 y b) := by
            exact congrArg eCod hab
          _ = zerothHomotopyMap e (eDom b) := by
            exact (hNat b).symm
      · intro y
        -- Delegate the degree-`1` surjectivity to the isolated tail-exactness interface.
        exact piOneSurjective_of_subsingletonHomotopyFiberPiZero (e := e) y (hFiber y)
  | succ m =>
      refine ⟨?_, ?_⟩
      · intro y
        rcases homotopyFiberTailMulExact (e := e) m y with
          ⟨fiberToSource, hExactLeft, _targetToFiber, _hExactRight⟩
        let _ :
            Subsingleton
              (π_ (m + 1) (homotopyFiberAt e y).right
                (underTopBasepoint (homotopyFiberAt e y))) :=
          hFiber y
        -- Exactness with a trivial fiber term forces injectivity on the public `(m + 1)`-stage.
        simpa [ContinuousMap.eStarMulHom] using
          injective_of_mulExact_of_subsingleton_source
            fiberToSource (e.eStarMulHom m y) hExactLeft
      · intro y
        rcases homotopyFiberTailMulExact (e := e) m y with
          ⟨_fiberToSource, _hExactLeft, targetToFiber, hExactRight⟩
        let _ :
            Subsingleton
              (π_ (m + 1) (homotopyFiberAt e y).right
                (underTopBasepoint (homotopyFiberAt e y))) :=
          hFiber y
        -- The same exact segment, one step to the left, forces surjectivity on `(m + 2)`.
        simpa [ContinuousMap.eStarMulHom] using
          surjective_of_mulExact_of_subsingleton_target
            (e.eStarMulHom (m + 1) y) targetToFiber hExactRight

/-- Helper for Theorem 10.7.10: an explicit sphere/disk filler package can be repackaged as the
Chapter 9 two-degree homotopy-group owner. -/
private theorem hasPiInjectiveSurjectiveSucc_of_explicitSphereConeHelp
    (n : ℕ)
    (hFill :
      ∀ (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
        (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          ∃ G : C(unitDisk n, X), ∃ K : (e.comp G).Homotopy g,
            G.comp (sphereBoundaryInclusion n) = f ∧
              ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z) :
    HasPiInjectiveSurjectiveSucc n e := by
  -- First read the explicit filler as pointwise triviality of the homotopy-fiber group.
  refine
    hasPiInjectiveSurjectiveSucc_of_subsingletonHomotopyGroup_homotopyFiberAt
      (e := e) n ?_
  intro y
  -- Then hand that pointwise fiber triviality to the isolated Chapter 8/9 exact-sequence bridge.
  exact
    subsingletonHomotopyGroup_homotopyFiberAt_of_explicitSphereConeHelp
      (e := e) n y hFill

/-- Helper for Theorem 10.7.10: once the HELP datum is solved on a boundary neighborhood, the
standard boundary-collar reduction packages it into `HasSphereConeHelp n e`. -/
private theorem hasSphereConeHelp_of_boundaryNeighborhoodLiftReduction
    (n : ℕ)
    (hSolveNearBoundary :
      ∀ (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
        (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          HasBoundaryNeighborhoodLift n e f g →
            ∃ G : C(unitDisk n, X), ∃ K : (e.comp G).Homotopy g,
              G.comp (sphereBoundaryInclusion n) = f ∧
                ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z)
    (hBoundaryNeighborhood :
      ∀ (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
        (_H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))),
          HasBoundaryNeighborhoodLift n e f g) :
    HasSphereConeHelp n e := by
  -- Route correction: first package the neighborhood reduction as an explicit disk filler, then
  -- hand that filler to the Chapter 9 bridge back to `HasPiInjectiveSurjectiveSucc`.
  refine ⟨?_⟩
  exact
    hasPiInjectiveSurjectiveSucc_of_explicitSphereConeHelp
      (e := e) n
      (fun f g H ↦ hSolveNearBoundary f g H (hBoundaryNeighborhood f g H))

/-- Helper for Theorem 10.7.10: a monotone subdivision of `I` separates two disjoint closed bad
sets into strips controlled entirely by the `A'`-side or the `B'`-side. -/
private theorem unitIntervalSubdivisionSeparatesDisjointClosedParts
    {C_A C_B : Set I}
    (hA_closed : IsClosed C_A) (hB_closed : IsClosed C_B) (h_disjoint : Disjoint C_A C_B) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ m, ∀ n ≥ m, t n = 1) ∧
      ∀ n, Icc (t n) (t (n + 1)) ⊆ C_Aᶜ ∨ Icc (t n) (t (n + 1)) ⊆ C_Bᶜ := by
  let c : Bool → Set I := fun b ↦ cond b C_Bᶜ C_Aᶜ
  have hc_open : ∀ b, IsOpen (c b) := by
    -- Each complement is open because the corresponding bad set is closed.
    intro b
    cases b
    · simp [c, cond, hA_closed.isOpen_compl]
    · simp [c, cond, hB_closed.isOpen_compl]
  have hc_cover : univ ⊆ ⋃ b, c b := by
    -- Every point lies outside at least one bad set because the bad sets are disjoint.
    intro x _
    by_cases hxA : x ∈ C_A
    · have hxB : x ∉ C_B := by
        intro hxB
        exact h_disjoint.le_bot ⟨hxA, hxB⟩
      exact Set.mem_iUnion.mpr ⟨true, by simp [c, cond, hxB]⟩
    · exact Set.mem_iUnion.mpr ⟨false, by simp [c, cond, hxA]⟩
  obtain ⟨t, ht0, hmono, htop, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hc_open hc_cover
  -- Read the resulting open-cover subdivision back in terms of the original bad sets.
  refine ⟨t, ht0, hmono, htop, ?_⟩
  intro n
  simpa [c, cond] using hsub n

/-- Helper for Theorem 10.7.10: under `π_ 0 ≃ ZerothHomotopy`, the degree-`0` map induced by a
continuous map is the usual map on path components. -/
private theorem pi0ZerothHomotopyNaturality
    {Y : Type u} {Z : Type v} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Z (f y) ≃ ZerothHomotopy Z).toFun ∘
        f.eStar 0 y =
      zerothHomotopyMap f ∘
        (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 Y y ≃ ZerothHomotopy Y).toFun := by
  -- Reduce to representatives, where both sides literally apply `f` to the same endpoint.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  rfl

/-- Helper for Theorem 10.7.10: the ambient map on path components commutes with the restriction
to the distinguished `A`-subspaces. -/
private theorem zerothHomotopyMap_subspaceA_commutes
    (hMap : T.IsMap T' e) :
    zerothHomotopyMap e ∘ zerothHomotopyInclusion T.subspaceA =
      zerothHomotopyInclusion T'.subspaceA ∘ zerothHomotopyMap (T.mapSubspaceA T' e hMap) := by
  -- On represented path components, both composites are represented by the same ambient point.
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  simp [zerothHomotopyInclusion_mk, zerothHomotopyMap_mk]

/-- Helper for Theorem 10.7.10: the ambient map on path components commutes with the restriction
to the distinguished `B`-subspaces. -/
private theorem zerothHomotopyMap_subspaceB_commutes
    (hMap : T.IsMap T' e) :
    zerothHomotopyMap e ∘ zerothHomotopyInclusion T.subspaceB =
      zerothHomotopyInclusion T'.subspaceB ∘ zerothHomotopyMap (T.mapSubspaceB T' e hMap) := by
  -- On represented path components, both composites are represented by the same ambient point.
  funext q
  refine Quotient.inductionOn q ?_
  intro a
  simp [zerothHomotopyInclusion_mk, zerothHomotopyMap_mk]

/-- Helper for Theorem 10.7.10: excisiveness of the target triad and surjectivity on the two
distinguished pieces imply surjectivity of the ambient map on path components. -/
private theorem surjectiveZerothHomotopy_of_excisiveTriadMap
    (hMap : T.IsMap T' e) (hT' : T'.IsExcisive)
    (hSubspaceA : IsGenuineWeakEquivalence (T.mapSubspaceA T' e hMap))
    (hSubspaceB : IsGenuineWeakEquivalence (T.mapSubspaceB T' e hMap)) :
    Function.Surjective (zerothHomotopyMap e) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro x'
  rcases (Triad.isExcisive_iff_forall.mp hT') x' with hxA | hxB
  · let xA' : T'.subspaceA := ⟨x', interior_subset hxA⟩
    rcases hSubspaceA.bijective_zerothHomotopy.surjective ⟦xA'⟧ with ⟨a, ha⟩
    refine ⟨zerothHomotopyInclusion T.subspaceA a, ?_⟩
    -- Rewrite through the `A`-restriction square and then use the chosen preimage in `A`.
    calc
      zerothHomotopyMap e (zerothHomotopyInclusion T.subspaceA a) =
          zerothHomotopyInclusion T'.subspaceA
            (zerothHomotopyMap (T.mapSubspaceA T' e hMap) a) := by
              simpa using
                congrFun
                  (zerothHomotopyMap_subspaceA_commutes
                    (T := T) (T' := T') (e := e) hMap)
                  a
      _ = zerothHomotopyInclusion T'.subspaceA ⟦xA'⟧ := by rw [ha]
      _ = ⟦x'⟧ := by
          simp [zerothHomotopyInclusion_mk, xA']
  · let xB' : T'.subspaceB := ⟨x', interior_subset hxB⟩
    rcases hSubspaceB.bijective_zerothHomotopy.surjective ⟦xB'⟧ with ⟨b, hb⟩
    refine ⟨zerothHomotopyInclusion T.subspaceB b, ?_⟩
    -- Rewrite through the `B`-restriction square and then use the chosen preimage in `B`.
    calc
      zerothHomotopyMap e (zerothHomotopyInclusion T.subspaceB b) =
          zerothHomotopyInclusion T'.subspaceB
            (zerothHomotopyMap (T.mapSubspaceB T' e hMap) b) := by
              simpa using
                congrFun
                  (zerothHomotopyMap_subspaceB_commutes
                    (T := T) (T' := T') (e := e) hMap)
                  b
      _ = zerothHomotopyInclusion T'.subspaceB ⟦xB'⟧ := by rw [hb]
      _ = ⟦x'⟧ := by
          simp [zerothHomotopyInclusion_mk, xB']

/-- Helper for Theorem 10.7.10: surjectivity on path components is exactly the degree-`0`
surjectivity required for `IsNEquivalence 0`. -/
private theorem isNEquivalenceZero_of_surjectiveZerothHomotopy
    (hSurj : Function.Surjective (zerothHomotopyMap e)) :
    IsNEquivalence 0 e := by
  refine ⟨?_, ?_⟩
  · intro x q hq
    -- There are no negative homotopy groups, so the injective half is vacuous.
    exact False.elim (Nat.not_lt_zero _ hq)
  · intro x q hq
    have hq0 : q = 0 := Nat.eq_zero_of_le_zero hq
    subst hq0
    intro a
    let eDom : π_ 0 X x ≃ ZerothHomotopy X := HomotopyGroup.pi0EquivZerothHomotopy
    let eCod : π_ 0 X' (e x) ≃ ZerothHomotopy X' := HomotopyGroup.pi0EquivZerothHomotopy
    rcases hSurj (eCod a) with ⟨b, hb⟩
    refine ⟨eDom.symm b, ?_⟩
    apply eCod.injective
    -- Transport the chosen ambient path-component preimage back through the `π₀` comparison.
    calc
      eCod (e.eStar 0 x (eDom.symm b)) =
          zerothHomotopyMap e (eDom (eDom.symm b)) := by
            simpa [eDom, eCod] using
              congrFun (pi0ZerothHomotopyNaturality (f := e) (y := x)) (eDom.symm b)
      _ = eCod a := by simpa using hb

/-- Helper for Theorem 10.7.10: degree-`0` HELP yields injectivity of the ambient map on path
components. -/
private theorem injectiveZerothHomotopy_of_hasSphereConeHelpZero
    (hHelp : HasSphereConeHelp 0 e) :
    Function.Injective (zerothHomotopyMap e) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro x b hab
  let eDom : π_ 0 X x ≃ ZerothHomotopy X := HomotopyGroup.pi0EquivZerothHomotopy
  let eCod : π_ 0 X' (e x) ≃ ZerothHomotopy X' := HomotopyGroup.pi0EquivZerothHomotopy
  have hPi : Function.Injective (e.eStar 0 x) :=
    hHelp.hasPiInjectiveSurjectiveSucc.injective x
  have hEq : eDom.symm ⟦x⟧ = eDom.symm b := by
    apply hPi
    apply eCod.injective
    -- Compare both path-component classes after transporting them to `π₀` at the basepoint `x`.
    calc
      eCod (e.eStar 0 x (eDom.symm ⟦x⟧)) =
          zerothHomotopyMap e (eDom (eDom.symm ⟦x⟧)) := by
            simpa [eDom, eCod] using
              congrFun (pi0ZerothHomotopyNaturality (f := e) (y := x)) (eDom.symm ⟦x⟧)
      _ = zerothHomotopyMap e ⟦x⟧ := by rw [Equiv.apply_symm_apply]
      _ = zerothHomotopyMap e b := hab
      _ = zerothHomotopyMap e (eDom (eDom.symm b)) := by rw [Equiv.apply_symm_apply]
      _ = eCod (e.eStar 0 x (eDom.symm b)) := by
            simpa [eDom, eCod] using
              (congrFun (pi0ZerothHomotopyNaturality (f := e) (y := x)) (eDom.symm b)).symm
  simpa using congrArg eDom hEq

/-- Helper for Theorem 10.7.10: all-degree HELP data yields the corresponding all-degree
two-stage homotopy-group owner in the mixed-universe setting of this file. -/
private theorem hasPiInjectiveSurjectiveSuccAllOfHasSphereConeHelpAll
    (hHelp : ∀ n : ℕ, HasSphereConeHelp n e) :
    ∀ n : ℕ, HasPiInjectiveSurjectiveSucc n e := by
  intro n
  -- Convert the HELP witness in degree `n` through Lemma 9.6.6.
  exact (hHelp n).hasPiInjectiveSurjectiveSucc

/-- Helper for Theorem 10.7.10: a `0`-equivalence plus two-stage control up through degree `n`
upgrades to an `(n + 1)`-equivalence, without requiring the source and target universes to match.
-/
private theorem isNEquivalenceSuccOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccUpTo
    (h0 : IsNEquivalence 0 e) :
    ∀ n : ℕ, (∀ m : ℕ, m ≤ n → HasPiInjectiveSurjectiveSucc m e) → IsNEquivalence (n + 1) e := by
  intro n
  induction n with
  | zero =>
      intro hSteps
      refine ⟨?_, ?_⟩
      · intro y q hq
        -- Below degree `1`, only `π₀` occurs, so the stage-`0` injectivity closes the goal.
        cases q with
        | zero =>
            simpa using (hSteps 0 le_rfl).injective y
        | succ q =>
            exact False.elim (Nat.not_lt_zero q (Nat.lt_of_succ_lt_succ hq))
      · intro y q hq
        -- Up through degree `1`, use `h0` in degree `0` and the stage-`0` successor map in
        -- degree `1`.
        cases q with
        | zero =>
            simpa using h0.surjective y (show 0 ≤ 0 by simp)
        | succ q =>
            have hq0 : q = 0 := Nat.eq_zero_of_le_zero (Nat.succ_le_succ_iff.mp hq)
            subst hq0
            simpa using (hSteps 0 le_rfl).surjectiveSucc y
  | succ n ih =>
      intro hSteps
      have hPrev :
          IsNEquivalence (n + 1) e :=
        ih (fun m hm ↦ hSteps m (Nat.le_trans hm (Nat.le_succ _)))
      refine ⟨?_, ?_⟩
      · intro y q hq
        -- Degrees below `n + 2` are handled either by the previous stage or by the new boundary
        -- degree `n + 1`.
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq' | rfl
        · exact hPrev.injective y hq'
        · exact (hSteps (n + 1) le_rfl).injective y
      · intro y q hq
        -- Surjectivity up through `n + 2` splits in the same way.
        rcases Nat.eq_or_lt_of_le hq with rfl | hq'
        · exact (hSteps (n + 1) le_rfl).surjectiveSucc y
        · exact hPrev.surjective y (Nat.le_of_lt_succ hq')

/-- Helper for Theorem 10.7.10: a `0`-equivalence together with HELP in every degree yields a
weak equivalence in the mixed-universe setting of this file. -/
private theorem isWeakEquivalenceOfIsNEquivalenceZeroAndHasSphereConeHelpAll
    (h0 : IsNEquivalence 0 e)
    (hHelp : ∀ n : ℕ, HasSphereConeHelp n e) :
    IsWeakEquivalence e := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero =>
      exact h0
  | succ n =>
      -- Normalize HELP to the two-stage owner and apply the standard stage-by-stage upgrade.
      exact
        isNEquivalenceSuccOfIsNEquivalenceZeroAndHasPiInjectiveSurjectiveSuccUpTo
          (e := e) h0 n
          (fun m _ ↦ hasPiInjectiveSurjectiveSuccAllOfHasSphereConeHelpAll (e := e) hHelp m)

/-- Helper for Theorem 10.7.10: excisiveness of the target triad should provide the boundary
neighborhood lift needed to start the HELP reduction in degree `n`. -/
private theorem hasBoundaryNeighborhoodLift_of_excisiveTriadMap
    (hMap : T.IsMap T' e) (hT : T.IsExcisive) (hT' : T'.IsExcisive)
    (hIntersection : IsGenuineWeakEquivalence (T.mapIntersection T' e hMap))
    (hSubspaceA : IsGenuineWeakEquivalence (T.mapSubspaceA T' e hMap))
    (hSubspaceB : IsGenuineWeakEquivalence (T.mapSubspaceB T' e hMap))
    (n : ℕ) (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
    (_H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n))) :
    HasBoundaryNeighborhoodLift n e f g := by
  -- Route correction: the earlier statement tried to build a literal neighborhood lift from
  -- `hMap` and `hT'` alone, but that is too strong because the boundary compatibility is only
  -- available through the supplied homotopy `H` and the restricted weak-equivalence hypotheses.
  -- TODO: extract the collar-controlled bad sets from `g` using `hT'`, solve the overlap and side
  -- strips with `hIntersection`, `hSubspaceA`, and `hSubspaceB`, and package the resulting local
  -- filler as the required neighborhood lift.
  sorry

/-- Helper for Theorem 10.7.10: once the boundary collar has been subdivided into overlap, `A`,
and `B` pieces, the three restricted weak-equivalence hypotheses should glue to a global disk
filler relative to the boundary sphere. -/
private theorem solveNearBoundary_of_excisiveTriadMap
    (hMap : T.IsMap T' e) (hT : T.IsExcisive) (hT' : T'.IsExcisive)
    (hIntersection : IsGenuineWeakEquivalence (T.mapIntersection T' e hMap))
    (hSubspaceA : IsGenuineWeakEquivalence (T.mapSubspaceA T' e hMap))
    (hSubspaceB : IsGenuineWeakEquivalence (T.mapSubspaceB T' e hMap))
    (n : ℕ) (f : C(sphereBoundary n, X)) (g : C(unitDisk n, X'))
    (H : (e.comp f).Homotopy (g.comp (sphereBoundaryInclusion n)))
    (hNear : HasBoundaryNeighborhoodLift n e f g) :
    ∃ G : C(unitDisk n, X), ∃ K : (e.comp G).Homotopy g,
      G.comp (sphereBoundaryInclusion n) = f ∧
        ∀ z : I × sphereBoundary n, K (z.1, sphereBoundaryInclusion n z.2) = H z := by
  -- TODO: use Remark 10.3.3 on the overlap and side pieces coming from the collar subdivision,
  -- then glue the resulting fillers with `continuous_piecewise` along the common frontier.
  sorry

/-- Helper for Theorem 10.7.10: the source proof's collar subdivision and relative-HELP gluing
produce `HasSphereConeHelp n e` in every degree from the three restricted weak-equivalence
hypotheses. -/
private theorem hasSphereConeHelpAll_of_excisiveTriadMap
    (hMap : T.IsMap T' e) (hT : T.IsExcisive) (hT' : T'.IsExcisive)
    (hIntersection : IsGenuineWeakEquivalence (T.mapIntersection T' e hMap))
    (hSubspaceA : IsGenuineWeakEquivalence (T.mapSubspaceA T' e hMap))
    (hSubspaceB : IsGenuineWeakEquivalence (T.mapSubspaceB T' e hMap)) :
    ∀ n : ℕ, HasSphereConeHelp n e := by
  intro n
  -- Route correction: isolate the boundary-neighborhood reduction from the piecewise relative
  -- HELP gluing so the remaining blocker is a pair of theorem-local interface lemmas.
  refine hasSphereConeHelp_of_boundaryNeighborhoodLiftReduction (e := e) n ?_ ?_
  · intro f g H hNear
    -- Delegate the gluing step to the theorem-local piecewise relative-HELP interface.
    exact
      solveNearBoundary_of_excisiveTriadMap
        (T := T) (T' := T') (e := e)
        hMap hT hT' hIntersection hSubspaceA hSubspaceB n f g H hNear
  · intro f g H
    -- Delegate the initial collar-neighborhood lift to the excisive target-cover interface.
    exact
      hasBoundaryNeighborhoodLift_of_excisiveTriadMap
        (T := T) (T' := T') (e := e)
        hMap hT hT' hIntersection hSubspaceA hSubspaceB n f g H

/-- Theorem 10.7.10: if `e : (X; A, B) ⟶ (X'; A', B')` is a map of excisive triads and the
induced maps on `C = A ∩ B`, `A`, and `B` are weak equivalences, then `e : X ⟶ X'` is a weak
equivalence. Here the source-faithful weak-equivalence surface is formalized by bijectivity on
`π₀` together with the Chapter 9 owner `IsWeakEquivalence`, both for the triad pieces and for the
conclusion on `e`. -/
theorem isWeakEquivalence_of_excisiveTriadMap
    (hMap : T.IsMap T' e) (hT : T.IsExcisive) (hT' : T'.IsExcisive)
    (hIntersection : IsGenuineWeakEquivalence (T.mapIntersection T' e hMap))
    (hSubspaceA : IsGenuineWeakEquivalence (T.mapSubspaceA T' e hMap))
    (hSubspaceB : IsGenuineWeakEquivalence (T.mapSubspaceB T' e hMap)) :
    IsGenuineWeakEquivalence e := by
  let hSurj : Function.Surjective (zerothHomotopyMap e) :=
    surjectiveZerothHomotopy_of_excisiveTriadMap
      (T := T) (T' := T') (e := e) hMap hT' hSubspaceA hSubspaceB
  let hHelpAll : ∀ n : ℕ, HasSphereConeHelp n e :=
    hasSphereConeHelpAll_of_excisiveTriadMap
      (T := T) (T' := T') (e := e) hMap hT hT' hIntersection hSubspaceA hSubspaceB
  let hWeak : IsWeakEquivalence e :=
    isWeakEquivalenceOfIsNEquivalenceZeroAndHasSphereConeHelpAll
      (e := e)
      (isNEquivalenceZero_of_surjectiveZerothHomotopy (e := e) hSurj)
      hHelpAll
  let hInj : Function.Injective (zerothHomotopyMap e) :=
    injectiveZerothHomotopy_of_hasSphereConeHelpZero
      (e := e) (hHelpAll 0)
  -- Assemble the ambient weak equivalence from the HELP package and the `π₀` bijectivity data.
  exact ⟨⟨hInj, hSurj⟩, hWeak⟩

end Triad
