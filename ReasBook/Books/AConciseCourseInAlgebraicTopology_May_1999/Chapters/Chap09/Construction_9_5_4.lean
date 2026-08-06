import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Lemma_7_6_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Observation_9_1_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel

open scoped TopCat Topology Topology.Homotopy unitInterval
open Homeomorph
open Path.Homotopic.Quotient

universe u v

variable {X : Type u} [TopologicalSpace X]

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

noncomputable section

-- Semantic recall via `lean_leansearch`: no current mathlib owner surfaced for the
-- cone-of-sphere model of pair-relative homotopy groups. Chapter 9 already packages the cubical
-- quotient `relativeCubeHomotopyClass`, while `SphereDiskModel` fixes the standard disk-boundary
-- model of `S^(n - 1) ⊂ D^n`; this item therefore adds only the source-facing comparison target.

/-- Helper for Construction 9.5.4: the concrete boundary sphere maps continuously into the
canonical `TopCat` sphere model by `ULift.up`. -/
private def sphereBoundaryToTopCatSphere (n : ℕ) :
    C(sphereBoundary n, (𝕊 n : TopCat)) :=
  ⟨ULift.up, ulift.symm.continuous_toFun⟩

/-- Helper for Construction 9.5.4: the canonical `TopCat` sphere model maps continuously back to
the concrete boundary sphere by `ULift.down`. -/
private def topCatSphereToSphereBoundary (n : ℕ) :
    C((𝕊 n : TopCat), sphereBoundary n) :=
  ⟨ULift.down, ulift.continuous_toFun⟩

/-- Helper for Construction 9.5.4: the Chapter 9 owner `relativeHomotopyGroup n A x` identifies
with the path components of the Section 9.5 sphere-evaluation fiber over `PathToSet.refl x`. -/
private noncomputable def relativeHomotopyGroupEquivSphereFiberZerothPathToSet
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x ≃
      ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :=
  let e :=
    Classical.choice
      (sphereBasepointFiber_homeomorphic_iteratedLoopSpace ((n : ℕ) - 1) (PathToSet.refl x))
  let hPathSpace :
      relativeHomotopyGroup n A x ≃
        ZerothHomotopy (relativePathSpaceIteratedLoopSpace ((n : ℕ) - 1) A x) := by
    -- Re-express the positive degree `n` as `((n : ℕ) - 1) + 1`.
    simpa using
      relativeHomotopyGroupSuccEquivZerothHomotopyIteratedPathSpace ((n : ℕ) - 1) A x
  -- Route correction: compare the relative group with the Section 9.5 fiber owner directly,
  -- rather than reopening the collapsed-cube source geometry.
  hPathSpace.trans (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Construction 9.5.4: a point of the Section 9.5 sphere fiber over
`PathToSet.refl x` yields the corresponding concrete sphere-boundary family of `PathToSet`
points by undoing the `ULift` presentation of `𝕊 ((n : ℕ) - 1)`. -/
private def sphereFiberToSpherePathToSetMap
    (n : ℕ+) (A : Set X) (x : A)
    (f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :
    C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) :=
  f.1.comp (sphereBoundaryToTopCatSphere ((n : ℕ) - 1))

/-- Helper for Construction 9.5.4: the concrete sphere family obtained from a Section 9.5 fiber
point still sends the chosen boundary basepoint to `PathToSet.refl x`. -/
@[simp] private theorem sphereFiberToSpherePathToSetMap_basepoint
    (n : ℕ+) (A : Set X) (x : A)
    (f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :
    sphereFiberToSpherePathToSetMap n A x f (sphereBoundaryBasepoint ((n : ℕ) - 1)) =
      PathToSet.refl x := by
  have hf :
      f.1 (sphereBasepoint ((n : ℕ) - 1)) = PathToSet.refl x :=
    (mem_sphereBasepointFiber_iff ((n : ℕ) - 1) (PathToSet.refl x) f.1).1 f.2
  -- The concrete boundary basepoint is exactly the `ULift`-repackaged sphere basepoint.
  simpa [sphereFiberToSpherePathToSetMap, sphereBoundaryToTopCatSphere, sphereBasepoint,
    sphereBoundaryBasepoint] using hf

/-
The former implementation contained a second, raw compact-open mapping-space construction of
fiber transport here.  It is not used by the disk-boundary comparison below, and its total space
is not a May compactly generated mapping space.  Keep the obsolete development out of the API.

/-- Helper for Construction 9.5.4: evaluation at the chosen sphere basepoint with target
`PathToSet A x.1` is the fibration whose varying fibers control the transport step in the
disk-boundary comparison. -/
private abbrev spherePathToSetEvalMap (n : ℕ+) (A : Set X) (x : A) :
    C(C((𝕊 ((n : ℕ) - 1) : TopCat), PathToSet A x.1), PathToSet A x.1) :=
  sphereMapEvalAtBasepoint ((n : ℕ) - 1) (sphereBasepoint ((n : ℕ) - 1))

/-- Helper for Construction 9.5.4: an actual path in `PathToSet A x.1` transports the path
components of the corresponding sphere-evaluation fibers. -/
private noncomputable def sphereBasepointFiberZerothEquivOfPathLocal
    (n : ℕ+) (A : Set X) (x : A) {γ γ' : PathToSet A x.1} (β : Path γ γ') :
    ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) γ) ≃
      ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) γ') :=
  let e :=
    Classical.choose
      (exists_homotopyEquiv_fiberTranslationPath (spherePathToSetEvalMap n A x) β)
  zerothHomotopyEquivOfHomotopyEquiv e

/-- Helper for Construction 9.5.4: homotopic paths in `PathToSet A x.1` induce the same
transport on path components of the corresponding sphere-evaluation fibers. -/
private theorem sphereBasepointFiberZerothEquivOfPathLocal_eq_of_homotopic
    (n : ℕ+) (A : Set X) (x : A) {γ γ' : PathToSet A x.1} {β₀ β₁ : Path γ γ'}
    (hβ : β₀.Homotopic β₁) :
    sphereBasepointFiberZerothEquivOfPathLocal n A x β₀ =
      sphereBasepointFiberZerothEquivOfPathLocal n A x β₁ := by
  let p := spherePathToSetEvalMap n A x
  let e₀ := Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β₀)
  let e₁ := Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β₁)
  -- Compare the chosen homotopy equivalences through their common Chapter 7 translation class.
  ext η
  change zerothHomotopyMap e₀.toFun η = zerothHomotopyMap e₁.toFun η
  have hs₀ :
      (⟦e₀.toFun⟧ : fiberMapHomotopyClasses p γ γ') =
        fiberTranslationClass p (mk β₀) := by
    dsimp [e₀]
    exact Classical.choose_spec (exists_homotopyEquiv_fiberTranslationPath p β₀)
  have hs₁ :
      (⟦e₁.toFun⟧ : fiberMapHomotopyClasses p γ γ') =
        fiberTranslationClass p (mk β₁) := by
    dsimp [e₁]
    exact Classical.choose_spec (exists_homotopyEquiv_fiberTranslationPath p β₁)
  have hτ₀ :
      IsFiberTranslation p (mk β₀)
        ((⟦e₀.toFun⟧ : fiberMapHomotopyClasses p γ γ')) := by
    rw [hs₀]
    exact isFiberTranslation_fiberTranslationClass p (mk β₀)
  have hτ₁ :
      IsFiberTranslation p (mk β₁)
        ((⟦e₁.toFun⟧ : fiberMapHomotopyClasses p γ γ')) := by
    rw [hs₁]
    exact isFiberTranslation_fiberTranslationClass p (mk β₁)
  have hClass :
      (⟦e₀.toFun⟧ : fiberMapHomotopyClasses p γ γ') =
        (⟦e₁.toFun⟧ : fiberMapHomotopyClasses p γ γ') :=
    fiberTranslationClass_eq_of_homotopic p hβ hτ₀ hτ₁
  have hMaps : ContinuousMap.Homotopic e₀.toFun e₁.toFun := Quotient.exact hClass
  -- Passing to `ZerothHomotopy` forgets the chosen translation representative.
  exact congrFun (zerothHomotopyMap_eq_of_homotopic hMaps) η

/-- Helper for Construction 9.5.4: a path class in `PathToSet A x.1` therefore determines the
induced equivalence on path components of the corresponding sphere-evaluation fibers. -/
private noncomputable def sphereBasepointFiberZerothEquivOfPathClassLocal
    (n : ℕ+) (A : Set X) (x : A) {γ γ' : PathToSet A x.1}
    (α : Path.Homotopic.Quotient γ γ') :
    ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) γ) ≃
      ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) γ') :=
  Quotient.liftOn α
    (fun β : Path γ γ' ↦ sphereBasepointFiberZerothEquivOfPathLocal n A x β)
    (fun _ _ hβ ↦
      sphereBasepointFiberZerothEquivOfPathLocal_eq_of_homotopic n A x hβ)

/-- Helper for Construction 9.5.4: on represented points, the local Section 9.5 transport
equivalence is induced by the explicit Chapter 7 fiber-translation map. -/
private theorem sphereBasepointFiberZerothEquivOfPathLocal_apply_mk
    (n : ℕ+) (A : Set X) (x : A) {γ γ' : PathToSet A x.1}
    (β : Path γ γ') (z : sphereBasepointFiber ((n : ℕ) - 1) γ) :
    sphereBasepointFiberZerothEquivOfPathLocal n A x β ⟦z⟧ =
      ⟦fiberTranslationMapOfPath (spherePathToSetEvalMap n A x) β z⟧ := by
  let p := spherePathToSetEvalMap n A x
  let e := Classical.choose (exists_homotopyEquiv_fiberTranslationPath p β)
  -- Rewrite the chosen Section 9.5 transport equivalence to its induced map on path components.
  change zerothHomotopyMap e.toFun ⟦z⟧ = ⟦fiberTranslationMapOfPath p β z⟧
  have hClass :
      (⟦e.toFun⟧ : fiberMapHomotopyClasses p γ γ') =
        (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p γ γ') := by
    calc
      (⟦e.toFun⟧ : fiberMapHomotopyClasses p γ γ') = fiberTranslationClass p (mk β) := by
        exact Classical.choose_spec (exists_homotopyEquiv_fiberTranslationPath p β)
      _ = (⟦fiberTranslationMapOfPath p β⟧ : fiberMapHomotopyClasses p γ γ') := by
        symm
        exact fiberTranslationMapOfPath_class p β
  have hMaps : ContinuousMap.Homotopic e.toFun (fiberTranslationMapOfPath p β) :=
    Quotient.exact hClass
  -- Passing to path components forgets the particular representative of the transport class.
  calc
    zerothHomotopyMap e.toFun ⟦z⟧ =
        zerothHomotopyMap (fiberTranslationMapOfPath p β) ⟦z⟧ := by
      exact congrFun (zerothHomotopyMap_eq_of_homotopic hMaps) ⟦z⟧
    _ = ⟦fiberTranslationMapOfPath p β z⟧ := by
      rw [zerothHomotopyMap_mk]

/-- Helper for Construction 9.5.4: an explicit lifted path in the total space identifies the
translated source point with the target point on path components of the target fiber. -/
private theorem fiberTranslationPointClass_eq_of_sameProjectedLift
    {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) [IsFibration p] {b b' : B}
    (β : Path b b') (z₀ : fiber p b) (z₁ : fiber p b')
    (γ : Path z₀.1 z₁.1)
    (hγ : p.comp γ.toContinuousMap = β.toContinuousMap) :
    (⟦fiberTranslationMapOfPath p β z₀⟧ : ZerothHomotopy (fiber p b')) = ⟦z₁⟧ := by
  let βconst :
      (ContinuousMap.const (ULift.{u, 0} PUnit) b).Homotopy
        (ContinuousMap.const (ULift.{u, 0} PUnit) b') :=
    β.toHomotopyConst
  let s : C(ULift.{u, 0} PUnit, fiber p b) := ContinuousMap.const _ z₀
  let f₀ : C(ULift.{u, 0} PUnit, fiber p b') :=
    ContinuousMap.const _ (fiberTranslationMapOfPath p β z₀)
  let f₁ : C(ULift.{u, 0} PUnit, fiber p b') := ContinuousMap.const _ z₁
  let restrictSource : C(I × ULift.{u, 0} PUnit, I × fiber p b) :=
    ⟨fun tu ↦ (tu.1, z₀), by fun_prop⟩
  rcases Classical.choose_spec (exists_fiberInclusionHomotopyLiftEndpoint p β) with ⟨Graw, hGraw⟩
  let G₀ : ((fiberInclusion p b).comp s).Homotopy ((fiberInclusion p b').comp f₀) :=
    { toContinuousMap := Graw.toContinuousMap.comp restrictSource
      map_zero_left := by
        intro u
        cases u
        simpa [restrictSource, s] using Graw.apply_zero z₀
      map_one_left := by
        intro u
        cases u
        change Graw (1, z₀) = ((fiberTranslationMapOfPath p β z₀ : fiber p b') : E)
        simpa [fiberTranslationMapOfPath] using Graw.apply_one z₀ }
  let G₁ : ((fiberInclusion p b).comp s).Homotopy ((fiberInclusion p b').comp f₁) :=
    { toContinuousMap := γ.toContinuousMap.comp
        (ContinuousMap.fst : C(I × ULift.{u, 0} PUnit, I))
      map_zero_left := by
        intro u
        cases u
        simpa [s] using γ.source
      map_one_left := by
        intro u
        cases u
        simpa [f₁] using γ.target }
  -- Route correction: compare the translated point with `z₁` through `PUnit`, so the Chapter 7
  -- endpoint-homotopy API applies without reopening the fiber-transport quotient.
  have hG₀ :
      p.comp G₀.toContinuousMap = βconst.toContinuousMap := by
    ext tu
    rcases tu with ⟨t, u⟩
    cases u
    simpa [G₀, restrictSource, s, Path.toHomotopyConst] using
      ContinuousMap.congr_fun hGraw (t, z₀)
  have hG₁ :
      p.comp G₁.toContinuousMap = βconst.toContinuousMap := by
    ext tu
    rcases tu with ⟨t, u⟩
    cases u
    simpa [G₁, Path.toHomotopyConst] using ContinuousMap.congr_fun hγ t
  have hProjected :
      p.comp (G₀.symm.trans G₁).toContinuousMap =
        (βconst.symm.trans βconst).toContinuousMap := by
    -- Projecting the comparison homotopy gives the standard self-canceling loop over `β`.
    ext tu
    change p ((G₀.symm.trans G₁) tu) =
      (βconst.symm.trans βconst) tu
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs with ht
    · simpa [ContinuousMap.Homotopy.symm] using
        ContinuousMap.congr_fun hG₀
          (σ ⟨2 * tu.1, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨tu.1.2.1, ht⟩⟩, tu.2)
    · simpa using
        ContinuousMap.congr_fun hG₁
          ((⟨2 * tu.1 - 1,
              unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, tu.1.2.2⟩⟩),
            tu.2)
  have hProjectedRel :
      (p.comp (G₀.symm.trans G₁).toContinuousMap).HomotopicRel
        ((ContinuousMap.Homotopy.refl (ContinuousMap.const (ULift.{u, 0} PUnit) b')).toContinuousMap)
        (({0, 1} : Set I) ×ˢ (Set.univ : Set (ULift.{u, 0} PUnit))) := by
    -- Rewrite to the canonical contractible loop on the constant base map `b'`.
    rw [hProjected]
    exact homotopySymmTransHomotopicRelRefl βconst
  have hEndpoint : ContinuousMap.Homotopic f₀ f₁ := by
    -- The projected loop contracts relative to the boundary, so the fiber endpoints are homotopic.
    exact fiberEndpointHomotopic_of_projectedHomotopyRelConst p (G₀.symm.trans G₁)
      hProjectedRel
  -- Evaluating the endpoint homotopy on the unique point of `PUnit` gives the desired equality
  -- on path components of the target fiber.
  simpa [f₀, f₁] using
    congrFun (zerothHomotopyMap_eq_of_homotopic hEndpoint) ⟦ULift.up PUnit.unit⟧
-/

/-- The distinguished cone point in the standard disk model `unitDisk ((n : ℕ) - 1)` of
`CS^(n - 1)`, realized by the origin. -/
def diskBoundaryConePoint (n : ℕ+) : unitDisk ((n : ℕ) - 1) :=
  ⟨(0 : V[((n : ℕ) - 1)]), by
    simp [unitDisk, Metric.mem_closedBall]⟩

/-- Helper for Construction 9.5.4: the standard radial parameterization of the cone on
`sphereBoundary ((n : ℕ) - 1)` fills the disk `unitDisk ((n : ℕ) - 1)` by scaling each boundary
vector toward the cone point. -/
private def diskBoundaryConeParameterization (n : ℕ+) :
    C(I × sphereBoundary ((n : ℕ) - 1), unitDisk ((n : ℕ) - 1)) where
  toFun p := by
    refine ⟨(1 - (p.1 : ℝ)) • p.2.1, ?_⟩
    rw [mem_unitDisk_iff, norm_smul]
    have hp_nonneg : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
    have hp_le : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    rw [mem_sphereBoundary_iff.mp p.2.2, Real.norm_of_nonneg hp_nonneg]
    simpa using hp_le
  continuous_toFun := by
    -- The parameterization is built from the coordinate projections and scalar multiplication.
    fun_prop

/-- Helper for Construction 9.5.4: the radial cone parameterization restricts on the bottom slice
`{0} × S^(n - 1)` to the standard sphere-boundary inclusion. -/
@[simp] private theorem diskBoundaryConeParameterization_zero
    (n : ℕ+) (y : sphereBoundary ((n : ℕ) - 1)) :
    diskBoundaryConeParameterization n (0, y) =
      sphereBoundaryInclusion ((n : ℕ) - 1) y := by
  -- At `t = 0`, the radial scaling factor is `1`, so the point stays on the boundary.
  apply Subtype.ext
  change (1 - ((0 : I) : ℝ)) • (y : V[((n : ℕ) - 1)]) = (y : V[((n : ℕ) - 1)])
  simp

/-- Helper for Construction 9.5.4: the radial cone parameterization collapses the top slice
`{1} × S^(n - 1)` to the distinguished cone point of the disk model. -/
@[simp] private theorem diskBoundaryConeParameterization_one
    (n : ℕ+) (y : sphereBoundary ((n : ℕ) - 1)) :
    diskBoundaryConeParameterization n (1, y) = diskBoundaryConePoint n := by
  -- At `t = 1`, the radial scaling factor is `0`, so every boundary point collapses to the
  -- origin.
  apply Subtype.ext
  change (1 - ((1 : I) : ℝ)) • (y : V[((n : ℕ) - 1)]) = (0 : V[((n : ℕ) - 1)])
  simp

/-- Helper for Construction 9.5.4: every point of `unitDisk ((n : ℕ) - 1)` lies on a radial line
from the cone point to some boundary point, so the cone parameterization is surjective. -/
private theorem diskBoundaryConeParameterization_surjective (n : ℕ+) :
    Function.Surjective (diskBoundaryConeParameterization n) := by
  intro y
  by_cases hy0 : (y : V[((n : ℕ) - 1)]) = 0
  · refine ⟨(1, sphereBoundaryBasepoint ((n : ℕ) - 1)), ?_⟩
    rw [diskBoundaryConeParameterization_one]
    apply Subtype.ext
    simp [diskBoundaryConePoint, hy0]
  · have hy_norm_nonzero : ‖(y : V[((n : ℕ) - 1)])‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hy0
    have hy_mem : ‖(y : V[((n : ℕ) - 1)])‖ ≤ 1 := mem_unitDisk_iff.mp y.2
    let z : sphereBoundary ((n : ℕ) - 1) := by
      refine ⟨‖(y : V[((n : ℕ) - 1)])‖⁻¹ • (y : V[((n : ℕ) - 1)]), ?_⟩
      rw [mem_sphereBoundary_iff, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
      field_simp [hy_norm_nonzero]
    let t : I := ⟨1 - ‖(y : V[((n : ℕ) - 1)])‖, by
      constructor
      · linarith [hy_mem]
      · linarith [norm_nonneg (y : V[((n : ℕ) - 1)])]⟩
    refine ⟨(t, z), ?_⟩
    -- Normalize the chosen boundary point so that the radial factor recovers `y`.
    apply Subtype.ext
    change (1 - (t : ℝ)) • (z : V[((n : ℕ) - 1)]) = (y : V[((n : ℕ) - 1)])
    dsimp [t, z]
    rw [show 1 - (1 - ‖(y : V[((n : ℕ) - 1)])‖) = ‖(y : V[((n : ℕ) - 1)])‖ by ring,
      smul_smul]
    rw [mul_inv_cancel₀ hy_norm_nonzero, one_smul]

/-- A map `unitDisk ((n : ℕ) - 1) → X` belongs to the auxiliary cone-point-fixed disk model when
it sends the boundary sphere into `A` and the distinguished cone point to `x`. This is not yet the
source-faithful pointed triple condition of Construction 9.5.4, because the source basepoint lies
on `S^(n - 1)`. -/
private def IsRelativeDiskBoundaryTripleMap (n : ℕ+) (A : Set X) (x : A)
    (f : C(unitDisk ((n : ℕ) - 1), X)) : Prop :=
  (∀ y : sphereBoundary ((n : ℕ) - 1), f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A) ∧
    f (diskBoundaryConePoint n) = x.1

/-- Unfolding `IsRelativeDiskBoundaryTripleMap` recovers the auxiliary cone-point-fixed disk model
conditions. -/
@[simp] private theorem isRelativeDiskBoundaryTripleMap_iff (n : ℕ+) (A : Set X) (x : A)
    (f : C(unitDisk ((n : ℕ) - 1), X)) :
    IsRelativeDiskBoundaryTripleMap n A x f ↔
      (∀ y : sphereBoundary ((n : ℕ) - 1),
        f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A) ∧
        f (diskBoundaryConePoint n) = x.1 := by
  rfl

/-- The auxiliary cone-point-fixed disk-boundary maps. -/
private abbrev relativeDiskBoundaryMap (n : ℕ+) (A : Set X) (x : A) :=
  { f : C(unitDisk ((n : ℕ) - 1), X) // IsRelativeDiskBoundaryTripleMap n A x f }

/-- A relative disk-boundary triple map sends the boundary sphere into `A`. -/
private theorem relativeDiskBoundaryMap_mapsTo_boundary
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x)
    (y : sphereBoundary ((n : ℕ) - 1)) :
    f.1 (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A :=
  f.2.1 y

/-- An auxiliary cone-point-fixed disk-boundary map sends the distinguished cone point to the
basepoint `x`. -/
@[simp] private theorem relativeDiskBoundaryMap_mapsTo_conePoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    f.1 (diskBoundaryConePoint n) = x.1 :=
  f.2.2

/-- Two auxiliary cone-point-fixed disk-boundary maps are equivalent when they are homotopic
through maps of the same auxiliary type. -/
private instance relativeDiskBoundaryMapSetoid (n : ℕ+) (A : Set X) (x : A) :
    Setoid (relativeDiskBoundaryMap n A x) where
  r f g := ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeDiskBoundaryTripleMap n A x)
  iseqv :=
    ⟨fun f ↦ ContinuousMap.HomotopicWith.refl f.1 f.2,
      fun {_ _} hfg ↦ ContinuousMap.HomotopicWith.symm hfg,
      fun {_ _ _} hfg hgh ↦ ContinuousMap.HomotopicWith.trans hfg hgh⟩

/-- The quotient of auxiliary cone-point-fixed disk-boundary maps by homotopy through maps of the
same auxiliary type. -/
private abbrev relativeDiskBoundaryHomotopyClass (n : ℕ+) (A : Set X) (x : A) :=
  Quotient (relativeDiskBoundaryMapSetoid n A x)

/-- A map `unitDisk ((n : ℕ) - 1) → X` is a map of pointed triples
`(CS^(n - 1), S^(n - 1), *) → (X, A, *)` when it sends the boundary sphere into `A` and sends the
chosen basepoint of `S^(n - 1)` to `x`. This is the source-faithful owner for Construction 9.5.4.
-/
def IsRelativeDiskBoundaryPointedTripleMap (n : ℕ+) (A : Set X) (x : A)
    (f : C(unitDisk ((n : ℕ) - 1), X)) : Prop :=
  (∀ y : sphereBoundary ((n : ℕ) - 1), f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A) ∧
    f (sphereBoundaryInclusion ((n : ℕ) - 1) (sphereBoundaryBasepoint ((n : ℕ) - 1))) = x.1

/-- Unfolding `IsRelativeDiskBoundaryPointedTripleMap` recovers the source-faithful pointed triple
conditions for Construction 9.5.4 in the disk-boundary model. -/
@[simp] theorem isRelativeDiskBoundaryPointedTripleMap_iff
    (n : ℕ+) (A : Set X) (x : A) (f : C(unitDisk ((n : ℕ) - 1), X)) :
    IsRelativeDiskBoundaryPointedTripleMap n A x f ↔
      (∀ y : sphereBoundary ((n : ℕ) - 1),
        f (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A) ∧
        f (sphereBoundaryInclusion ((n : ℕ) - 1)
          (sphereBoundaryBasepoint ((n : ℕ) - 1))) = x.1 := by
  rfl

/-- The concrete pointed triple maps
`(CS^(n - 1), S^(n - 1), *) → (X, A, *)`, realized by the standard disk-boundary model with the
chosen basepoint `sphereBoundaryBasepoint ((n : ℕ) - 1)` on `S^(n - 1)`. -/
abbrev relativeDiskBoundaryPointedMap (n : ℕ+) (A : Set X) (x : A) :=
  { f : C(unitDisk ((n : ℕ) - 1), X) // IsRelativeDiskBoundaryPointedTripleMap n A x f }

/-- A pointed disk-boundary triple map sends the boundary sphere into `A`. -/
theorem relativeDiskBoundaryPointedMap_mapsTo_boundary
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x)
    (y : sphereBoundary ((n : ℕ) - 1)) :
    f.1 (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A :=
  f.2.1 y

/-- A pointed disk-boundary triple map sends the chosen basepoint of `S^(n - 1)` to `x`. -/
@[simp] theorem relativeDiskBoundaryPointedMap_mapsTo_basepoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) :
    f.1 (sphereBoundaryInclusion ((n : ℕ) - 1) (sphereBoundaryBasepoint ((n : ℕ) - 1))) = x.1 :=
  f.2.2

/-- Two pointed disk-boundary triple maps are equivalent when they are homotopic through pointed
triple maps of the same type. -/
instance relativeDiskBoundaryPointedMapSetoid (n : ℕ+) (A : Set X) (x : A) :
    Setoid (relativeDiskBoundaryPointedMap n A x) where
  r f g := ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeDiskBoundaryPointedTripleMap n A x)
  iseqv :=
    ⟨fun f ↦ ContinuousMap.HomotopicWith.refl f.1 f.2,
      fun {_ _} hfg ↦ ContinuousMap.HomotopicWith.symm hfg,
      fun {_ _ _} hfg hgh ↦ ContinuousMap.HomotopicWith.trans hfg hgh⟩

/-- The quotient of pointed disk-boundary triple maps
`(CS^(n - 1), S^(n - 1), *) → (X, A, *)` by homotopy through pointed triple maps. -/
abbrev relativeDiskBoundaryPointedHomotopyClass (n : ℕ+) (A : Set X) (x : A) :=
  Quotient (relativeDiskBoundaryPointedMapSetoid n A x)

/-- Helper for Construction 9.5.4: the explicit radial nullhomotopy for a disk-boundary triple map
starts at the boundary restriction. -/
private theorem relativeDiskBoundaryMapBoundaryHomotopy_zero
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    ∀ y : sphereBoundary ((n : ℕ) - 1),
      (f.1.comp (diskBoundaryConeParameterization n)) (0, y) =
        ((f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1))) y) := by
  intro y
  -- At `t = 0`, the cone parameterization lands on the boundary inclusion.
  simpa using congrArg f.1 (diskBoundaryConeParameterization_zero n y)

/-- Helper for Construction 9.5.4: the explicit radial nullhomotopy for a disk-boundary triple map
ends at the constant map `x`. -/
private theorem relativeDiskBoundaryMapBoundaryHomotopy_one
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    ∀ y : sphereBoundary ((n : ℕ) - 1),
      (f.1.comp (diskBoundaryConeParameterization n)) (1, y) = x.1 := by
  intro y
  -- At `t = 1`, every radial line reaches the distinguished cone point.
  simpa using congrArg f.1 (diskBoundaryConeParameterization_one n y).trans
    (relativeDiskBoundaryMap_mapsTo_conePoint n A x f)

/-- Helper for Construction 9.5.4: every disk-boundary triple map restricts on the boundary sphere
to a map into `A` that is homotopic to the constant map at `x` by following the radial cone lines
toward the cone point. -/
private noncomputable def relativeDiskBoundaryMapBoundaryHomotopy
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1))).Homotopy
      (ContinuousMap.const _ x.1) :=
  { toContinuousMap := f.1.comp (diskBoundaryConeParameterization n)
    map_zero_left := relativeDiskBoundaryMapBoundaryHomotopy_zero n A x f
    map_one_left := relativeDiskBoundaryMapBoundaryHomotopy_one n A x f }

/-- Helper for Construction 9.5.4: every homotopy from a sphere-boundary map to the constant map
at `x` is constant on the fibers of `diskBoundaryConeParameterization n`, so it descends to the
disk model. -/
private theorem sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization
    (n : ℕ+) {k₀ : C(sphereBoundary ((n : ℕ) - 1), X)}
    (x : X) (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    Function.FactorsThrough H.toContinuousMap (diskBoundaryConeParameterization n) := by
  intro p q hpq
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  change H (t, a) = H (s, b)
  have hvec :
      (1 - (t : ℝ)) • (a : V[((n : ℕ) - 1)]) =
        (1 - (s : ℝ)) • (b : V[((n : ℕ) - 1)]) := by
    exact congrArg Subtype.val hpq
  have hscale : 1 - (t : ℝ) = 1 - (s : ℝ) := by
    have hnorm := congrArg norm hvec
    rw [norm_smul, norm_smul,
      mem_sphereBoundary_iff.mp a.2, mem_sphereBoundary_iff.mp b.2,
      Real.norm_of_nonneg (sub_nonneg.mpr t.2.2),
      Real.norm_of_nonneg (sub_nonneg.mpr s.2.2)] at hnorm
    simpa using hnorm
  by_cases htop : 1 - (t : ℝ) = 0
  · have hs_top : 1 - (s : ℝ) = 0 := by simpa [hscale] using htop
    have ht : t = 1 := by
      have htval : (t : ℝ) = 1 := by
        linarith
      exact Subtype.ext htval
    have hs : s = 1 := by
      have hsval : (s : ℝ) = 1 := by
        linarith
      exact Subtype.ext hsval
    rw [ht, hs, H.apply_one, H.apply_one]
    simp
  · have hab_val : (a : V[((n : ℕ) - 1)]) = (b : V[((n : ℕ) - 1)]) := by
      apply (smul_right_injective (V[((n : ℕ) - 1)]) htop)
      simpa [hscale] using hvec
    have hab : a = b := Subtype.ext hab_val
    have hts : t = s := by
      apply Subtype.ext
      linarith
    rw [hts, hab]

/-- Helper for Construction 9.5.4: a sphere-boundary homotopy to the constant map at `x`
descends along `diskBoundaryConeParameterization n` to a relative disk-boundary triple map. -/
private theorem exists_relativeDiskBoundaryMap_of_sphereBoundaryHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    (k₀ : C(sphereBoundary ((n : ℕ) - 1), X))
    (hk₀ : ∀ y : sphereBoundary ((n : ℕ) - 1), k₀ y ∈ A)
    (H : k₀.Homotopy (ContinuousMap.const _ x.1)) :
    ∃ f : relativeDiskBoundaryMap n A x,
      f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)) = k₀ := by
  let q := diskBoundaryConeParameterization n
  let hfactor :=
    sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization n x.1 H
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (diskBoundaryConeParameterization_surjective n) q.continuous
  let lifted : C(unitDisk ((n : ℕ) - 1), X) := hq.lift H.toContinuousMap hfactor
  have hlift_boundary :
      lifted.comp (sphereBoundaryInclusion ((n : ℕ) - 1)) = k₀ := by
    ext y
    -- Evaluate the quotient-lift equation on the boundary slice `t = 0`.
    have hdesc :=
      congrArg
        (fun g : C(I × sphereBoundary ((n : ℕ) - 1), X) ↦ g (0, y))
        (hq.lift_comp H.toContinuousMap hfactor)
    change lifted (q (0, y)) = H (0, y) at hdesc
    simpa [lifted, q, diskBoundaryConeParameterization_zero] using hdesc
  have hlift_cone :
      lifted (diskBoundaryConePoint n) = x.1 := by
    -- Evaluate the same descended equality on the collapsed top slice.
    let y₀ : sphereBoundary ((n : ℕ) - 1) := sphereBoundaryBasepoint ((n : ℕ) - 1)
    have hdesc :=
      congrArg
        (fun g : C(I × sphereBoundary ((n : ℕ) - 1), X) ↦ g (1, y₀))
        (hq.lift_comp H.toContinuousMap hfactor)
    change lifted (q (1, y₀)) = H (1, y₀) at hdesc
    simpa [lifted, q, diskBoundaryConeParameterization_one] using hdesc
  have hlift_mem :
      ∀ y : sphereBoundary ((n : ℕ) - 1),
        lifted (sphereBoundaryInclusion ((n : ℕ) - 1) y) ∈ A := by
    intro y
    -- The descended map agrees with the original boundary map on the boundary sphere.
    have hy : lifted (sphereBoundaryInclusion ((n : ℕ) - 1) y) = k₀ y := by
      simpa using ContinuousMap.congr_fun hlift_boundary y
    rw [hy]
    exact hk₀ y
  refine ⟨⟨lifted, hlift_mem, hlift_cone⟩, hlift_boundary⟩

/-- Helper for Construction 9.5.4: a sphere family of `PathToSet` points records its endpoint map
into `A`. -/
private def spherePathToSetEndpointMap
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    C(sphereBoundary ((n : ℕ) - 1), X) where
  toFun y := (k y).endpoint.1
  continuous_toFun := by
    have hPathPoint : Continuous fun y : sphereBoundary ((n : ℕ) - 1) ↦ k y := k.continuous
    have hEndpoint :
        Continuous fun y : sphereBoundary ((n : ℕ) - 1) ↦
          (PathToSet.endpointAndPath A x (k y)).1 := by
      exact continuous_fst.comp (continuous_induced_dom.comp hPathPoint)
    -- The induced-topology model of `PathToSet` makes endpoint evaluation continuous.
    simpa [PathToSet.endpointAndPath] using continuous_subtype_val.comp hEndpoint

/-- Helper for Construction 9.5.4: the endpoint of a sphere family of `PathToSet` points lands in
`A`. -/
private theorem spherePathToSetEndpointMap_mem
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1))
    (y : sphereBoundary ((n : ℕ) - 1)) :
    spherePathToSetEndpointMap n A x k y ∈ A := by
  -- Each `PathToSet` endpoint is constrained to lie in `A`.
  simpa [spherePathToSetEndpointMap] using PathToSet.endpoint_mem (k y)

/-- Helper for Construction 9.5.4: a free sphere family records the varying `PathToSet` value at
the chosen concrete sphere-boundary basepoint. -/
private def spherePathToSetBasepointValue
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    PathToSet A x.1 :=
  k (sphereBoundaryBasepoint ((n : ℕ) - 1))

/-- Helper for Construction 9.5.4: the same free sphere family, viewed through the `ULift`
presentation of `𝕊 ((n : ℕ) - 1)`, lies in the sphere-evaluation fiber over its recorded
basepoint value. -/
private theorem spherePathToSetMapAsFiberPoint_mem
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    k.comp (topCatSphereToSphereBoundary ((n : ℕ) - 1)) ∈
      sphereBasepointFiber ((n : ℕ) - 1) (spherePathToSetBasepointValue n A x k) := by
  -- Evaluate the repackaged sphere family at the chosen sphere basepoint.
  rw [mem_sphereBasepointFiber_iff]
  simpa [spherePathToSetBasepointValue, topCatSphereToSphereBoundary, sphereBasepoint,
    sphereBoundaryBasepoint]

/-- Helper for Construction 9.5.4: packaging a free sphere family as a point of the corresponding
varying sphere-evaluation fiber only changes notation, not the underlying family. -/
private def spherePathToSetMapAsFiberPoint
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    sphereBasepointFiber ((n : ℕ) - 1) (spherePathToSetBasepointValue n A x k) :=
  ⟨k.comp (topCatSphereToSphereBoundary ((n : ℕ) - 1)),
    spherePathToSetMapAsFiberPoint_mem n A x k⟩

/-- Helper for Construction 9.5.4: a homotopy of free sphere families yields the corresponding
path between their recorded basepoint values in `PathToSet A x.1`. -/
private theorem spherePathToSetBasepointValuePath_nonempty
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    Nonempty
      (Path (spherePathToSetBasepointValue n A x k₀)
        (spherePathToSetBasepointValue n A x k₁)) := by
  refine ⟨Path.mk
    ⟨fun t ↦ H (t, sphereBoundaryBasepoint ((n : ℕ) - 1)), ?_⟩
    ?_ ?_⟩
  · let evalBasepoint : C(I, I × sphereBoundary ((n : ℕ) - 1)) :=
      ⟨fun t ↦ (t, sphereBoundaryBasepoint ((n : ℕ) - 1)), by
        fun_prop⟩
    -- Evaluate the free-family homotopy at the chosen boundary basepoint.
    simpa [evalBasepoint] using H.continuous.comp evalBasepoint.continuous
  · -- At time `0`, the evaluated homotopy starts at the first free sphere family.
    simpa [spherePathToSetBasepointValue] using
      H.apply_zero (sphereBoundaryBasepoint ((n : ℕ) - 1))
  · -- At time `1`, the evaluated homotopy ends at the second free sphere family.
    simpa [spherePathToSetBasepointValue] using
      H.apply_one (sphereBoundaryBasepoint ((n : ℕ) - 1))

/-- Helper for Construction 9.5.4: choose the path in `PathToSet A x.1` obtained by evaluating a
homotopy of free sphere families at the chosen boundary basepoint. -/
private noncomputable def spherePathToSetBasepointValuePath
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    Path (spherePathToSetBasepointValue n A x k₀)
      (spherePathToSetBasepointValue n A x k₁) := by
  refine Path.mk
    ⟨fun t ↦ H (t, sphereBoundaryBasepoint ((n : ℕ) - 1)), ?_⟩
    ?_ ?_
  · let evalBasepoint : C(I, I × sphereBoundary ((n : ℕ) - 1)) :=
      ⟨fun t ↦ (t, sphereBoundaryBasepoint ((n : ℕ) - 1)), by
        fun_prop⟩
    -- Evaluate the free-family homotopy at the chosen boundary basepoint.
    simpa [evalBasepoint] using H.continuous.comp evalBasepoint.continuous
  · -- At time `0`, the explicit evaluated path starts at the source basepoint value.
    simpa [spherePathToSetBasepointValue] using
      H.apply_zero (sphereBoundaryBasepoint ((n : ℕ) - 1))
  · -- At time `1`, the explicit evaluated path ends at the target basepoint value.
    simpa [spherePathToSetBasepointValue] using
      H.apply_one (sphereBoundaryBasepoint ((n : ℕ) - 1))

/-- Helper for Construction 9.5.4: a homotopy of free sphere families determines a path in the
Section 9.5 mapping space between the corresponding points of the varying evaluation fibers. -/
private def spherePathToSetHomotopyAsFiberPath
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    Path
      (spherePathToSetMapAsFiberPoint n A x k₀).1
      (spherePathToSetMapAsFiberPoint n A x k₁).1 := by
  refine Path.mk
    ⟨fun t ↦ (H.curry t).comp (topCatSphereToSphereBoundary ((n : ℕ) - 1)), ?_⟩
    ?_ ?_
  · -- Curry the free-family homotopy into a path in the compact-open mapping space.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hUncurried :
        Continuous fun z : I × (𝕊 ((n : ℕ) - 1) : TopCat) ↦
          H (z.1, topCatSphereToSphereBoundary ((n : ℕ) - 1) z.2) := by
      exact H.continuous.comp (by fun_prop)
    simpa [Function.uncurry] using hUncurried
  · -- At time `0`, we recover the repackaged source sphere family.
    ext s
    simpa [spherePathToSetMapAsFiberPoint] using
      H.apply_zero (topCatSphereToSphereBoundary ((n : ℕ) - 1) s)
  · -- At time `1`, we recover the repackaged target sphere family.
    ext s
    simpa [spherePathToSetMapAsFiberPoint] using
      H.apply_one (topCatSphereToSphereBoundary ((n : ℕ) - 1) s)

/-
This compatibility lemma belonged to the obsolete raw fiber-transport block above and was never
used by the orbit or pointed disk-boundary comparison.

/-- Helper for Construction 9.5.4: a homotopy of free sphere families transports the Section 9.5
fiber class of the source family to the fiber class of the target family along the evaluated
basepoint path. -/
private theorem spherePathToSetHomotopyTransportClass
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    sphereBasepointFiberZerothEquivOfPathClassLocal n A x
        (mk (spherePathToSetBasepointValuePath n A x H))
        ⟦spherePathToSetMapAsFiberPoint n A x k₀⟧ =
      ⟦spherePathToSetMapAsFiberPoint n A x k₁⟧ := by
  let p := spherePathToSetEvalMap n A x
  change
    sphereBasepointFiberZerothEquivOfPathLocal n A x
        (spherePathToSetBasepointValuePath n A x H)
        ⟦spherePathToSetMapAsFiberPoint n A x k₀⟧ =
      ⟦spherePathToSetMapAsFiberPoint n A x k₁⟧
  rw [sphereBasepointFiberZerothEquivOfPathLocal_apply_mk]
  have hproj :
      p.comp (spherePathToSetHomotopyAsFiberPath n A x H).toContinuousMap =
        (spherePathToSetBasepointValuePath n A x H).toContinuousMap := by
    ext t
    -- Evaluating the lifted sphere-family path at the sphere basepoint recovers the chosen
    -- basepoint-value path in `PathToSet A x.1`.
    simp [p, spherePathToSetEvalMap, sphereMapEvalAtBasepoint,
      spherePathToSetHomotopyAsFiberPath, spherePathToSetBasepointValuePath,
      spherePathToSetBasepointValue, topCatSphereToSphereBoundary, sphereBasepoint,
      sphereBoundaryBasepoint]
  -- The point-level transport bridge converts the explicit lifted path into equality of target
  -- fiber classes.
  have hTransport :=
    fiberTranslationPointClass_eq_of_sameProjectedLift p
      (spherePathToSetBasepointValuePath n A x H)
      (spherePathToSetMapAsFiberPoint n A x k₀)
      (spherePathToSetMapAsFiberPoint n A x k₁)
      (spherePathToSetHomotopyAsFiberPath n A x H)
      hproj
  simpa [p] using hTransport
-/

/-- Helper for Construction 9.5.4: the transport-stable free-sphere owner records a sphere
family in `PathToSet A x.1` only by its chosen basepoint value and the path component of the
corresponding varying Section 9.5 evaluation-fiber point. -/
private abbrev spherePathToSetFiberOrbitData
    (n : ℕ+) (A : Set X) (x : A) :=
  Σ γ : PathToSet A x.1, ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) γ)

/-- Helper for Construction 9.5.4: a free sphere family determines one point of the
transport-stable orbit owner by remembering its recorded basepoint value and its class in the
corresponding varying evaluation fiber. -/
private def spherePathToSetFiberOrbitPoint
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    spherePathToSetFiberOrbitData n A x :=
  ⟨spherePathToSetBasepointValue n A x k, ⟦spherePathToSetMapAsFiberPoint n A x k⟧⟩

/-- Helper for Construction 9.5.4: one generating step in the free-sphere orbit relation comes
from an honest homotopy of sphere families in `PathToSet A x.1`. -/
private def spherePathToSetFiberOrbitRel
    (n : ℕ+) (A : Set X) (x : A) :
    spherePathToSetFiberOrbitData n A x →
      spherePathToSetFiberOrbitData n A x → Prop
  | z₀, z₁ =>
      ∃ k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1),
        Nonempty (k₀.Homotopy k₁) ∧
          z₀ = spherePathToSetFiberOrbitPoint n A x k₀ ∧
            z₁ = spherePathToSetFiberOrbitPoint n A x k₁

/-- Helper for Construction 9.5.4: quotienting the recorded free-sphere data by the equivalence
relation generated by honest homotopies gives the transport-stable owner used for the remaining
disk-boundary comparison. -/
private abbrev spherePathToSetFiberOrbit
    (n : ℕ+) (A : Set X) (x : A) :=
  Quotient (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))

/-- Helper for Construction 9.5.4: a homotopy of free sphere families identifies the
corresponding points of the transport-stable orbit owner. -/
private theorem spherePathToSetFiberOrbit_eq_of_homotopy
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
        (spherePathToSetFiberOrbitPoint n A x k₀) :
      spherePathToSetFiberOrbit n A x) =
      Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
        (spherePathToSetFiberOrbitPoint n A x k₁) := by
  -- A single homotopy step becomes one generating relation in the orbit quotient.
  exact Quotient.sound <|
    Relation.EqvGen.rel _ _ ⟨k₀, k₁, ⟨H⟩, rfl, rfl⟩

/-- Helper for Construction 9.5.4: a path in the Section 9.5 sphere fiber over
`PathToSet.refl x` uncarries to an honest homotopy of the corresponding concrete sphere
families in `PathToSet A x.1`. -/
private def sphereFiberToSpherePathToSetHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    {f₀ f₁ : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)}
    (hff : Joined f₀ f₁) :
    (sphereFiberToSpherePathToSetMap n A x f₀).Homotopy
      (sphereFiberToSpherePathToSetMap n A x f₁) := by
  classical
  let γ := Classical.choice hff
  refine
    { toContinuousMap := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · refine ⟨fun z ↦ (γ z.1).1 (ULift.up z.2), ?_⟩
    -- Evaluate the path of Section 9.5 fiber points on the concrete sphere boundary.
    let _ : LocallyCompactSpace (sphereBoundary ((n : ℕ) - 1)) := inferInstance
    let _ : LocallyCompactSpace ((𝕊 ((n : ℕ) - 1) : TopCat.{u})) := by
      change LocallyCompactSpace (ULift.{u, 0} (sphereBoundary ((n : ℕ) - 1)))
      infer_instance
    have hMap :
        Continuous fun z : I × sphereBoundary ((n : ℕ) - 1) ↦
          (((γ z.1).1 : C((𝕊 ((n : ℕ) - 1) : TopCat.{u}), PathToSet A x.1))) := by
      exact continuous_subtype_val.comp (γ.continuous.comp continuous_fst)
    exact continuous_eval.comp <|
      hMap.prodMk (by
        fun_prop :
          Continuous fun z : I × sphereBoundary ((n : ℕ) - 1) ↦
            (ULift.up z.2 : (𝕊 ((n : ℕ) - 1) : TopCat.{u})))
  · intro s
    -- At time `0`, evaluating the path recovers the source sphere-fiber point.
    change (γ 0).1 (ULift.up s) = (sphereFiberToSpherePathToSetMap n A x f₀) s
    have hSource :=
      congrArg
        (fun q : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) ↦
          q.1 (ULift.up s))
        γ.source
    simpa [sphereFiberToSpherePathToSetMap, sphereBoundaryToTopCatSphere] using hSource
  · intro s
    -- At time `1`, evaluating the path recovers the target sphere-fiber point.
    change (γ 1).1 (ULift.up s) = (sphereFiberToSpherePathToSetMap n A x f₁) s
    have hTarget :=
      congrArg
        (fun q : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) ↦
          q.1 (ULift.up s))
        γ.target
    simpa [sphereFiberToSpherePathToSetMap, sphereBoundaryToTopCatSphere] using hTarget

/-- Helper for Construction 9.5.4: the based Section 9.5 sphere-fiber model already maps to the
transport-stable free-sphere orbit owner. -/
private noncomputable def sphereFiberZerothToSpherePathToSetFiberOrbit
    (n : ℕ+) (A : Set X) (x : A) :
    ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) →
      spherePathToSetFiberOrbit n A x :=
  Quotient.lift
    (fun f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) ↦
      (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
          (spherePathToSetFiberOrbitPoint n A x
            (sphereFiberToSpherePathToSetMap n A x f)) :
        spherePathToSetFiberOrbit n A x))
    (fun f₀ f₁ hff ↦ by
      -- A path in the based evaluation fiber gives a free-sphere homotopy, so the orbit class is
      -- independent of the chosen representative of the `ZerothHomotopy` class.
      exact spherePathToSetFiberOrbit_eq_of_homotopy n A x
        (sphereFiberToSpherePathToSetHomotopy n A x hff))

/-- Helper for Construction 9.5.4: on a represented Section 9.5 fiber point, the map to the
transport-stable orbit owner is given by the corresponding concrete free sphere family. -/
@[simp] private theorem sphereFiberZerothToSpherePathToSetFiberOrbit_mk
    (n : ℕ+) (A : Set X) (x : A)
    (f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :
    sphereFiberZerothToSpherePathToSetFiberOrbit n A x ⟦f⟧ =
      (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
          (spherePathToSetFiberOrbitPoint n A x
            (sphereFiberToSpherePathToSetMap n A x f)) :
        spherePathToSetFiberOrbit n A x) := by
  rfl

/-- Helper for Construction 9.5.4: reversing the paths in a sphere family of `PathToSet` points
gives a nullhomotopy of its endpoint map to the constant map at `x`. -/
private def spherePathToSetEndpointHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    (spherePathToSetEndpointMap n A x k).Homotopy (ContinuousMap.const _ x.1) where
  toContinuousMap := by
    let pathPoint : (I × sphereBoundary ((n : ℕ) - 1)) → PathToSet A x.1 := fun z ↦ k z.2
    have hPathPoint : Continuous pathPoint := k.continuous.comp continuous_snd
    have hPathComponent :
        Continuous fun z : I × sphereBoundary ((n : ℕ) - 1) ↦
          (PathToSet.endpointAndPath A x (pathPoint z)).2 := by
      exact continuous_snd.comp (continuous_induced_dom.comp hPathPoint)
    -- Evaluate the sphere-family paths at reversed time to run from `x` to each endpoint.
    exact
      { toFun := fun z ↦ k z.2 (unitInterval.symm z.1)
        continuous_toFun := by
          simpa [pathPoint] using
            (continuous_eval.comp <|
              hPathComponent.prodMk (by
                fun_prop :
                  Continuous fun z : I × sphereBoundary ((n : ℕ) - 1) ↦
                    unitInterval.symm z.1)) }
  map_zero_left := by
    intro y
    -- At `t = 0`, the reversed path is evaluated at its endpoint.
    simpa [spherePathToSetEndpointMap] using (k y).path.target'
  map_one_left := by
    intro y
    -- At `t = 1`, the reversed path returns to the common source `x`.
    simpa using (k y).path.source'

/-- Helper for Construction 9.5.4: a boundary map into `A` together with a nullhomotopy to the
constant map at `x` packages into a sphere family of `PathToSet` points. -/
private def sphereBoundaryHomotopyToSpherePathToSetMap
    (n : ℕ+) (A : Set X) (x : A)
    (k₀ : C(sphereBoundary ((n : ℕ) - 1), X))
    (hk₀ : ∀ y : sphereBoundary ((n : ℕ) - 1), k₀ y ∈ A)
    (H : k₀.Homotopy (ContinuousMap.const _ x.1)) :
    C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) where
  toFun y :=
    PathToSet.mk ⟨k₀ y, hk₀ y⟩ <|
      Path.mk
        { toFun := fun t ↦ H (unitInterval.symm t, y)
          continuous_toFun := by
            let reversedTime : I → I × sphereBoundary ((n : ℕ) - 1) := fun t ↦
              (unitInterval.symm t, y)
            have hReversedTime : Continuous reversedTime := by
              fun_prop
            -- Restrict the nullhomotopy to the chosen sphere point and reverse time.
            simpa [reversedTime] using H.continuous.comp hReversedTime }
        (by
          -- At `t = 0`, the reversed homotopy starts at the constant value `x`.
          change H (unitInterval.symm 0, y) = x.1
          simpa using H.apply_one y)
        (by
          -- At `t = 1`, the reversed homotopy ends at the original boundary value.
          change H (unitInterval.symm 1, y) = k₀ y
          simpa using H.apply_zero y)
  continuous_toFun := by
    have hEndpoint :
        Continuous fun y : sphereBoundary ((n : ℕ) - 1) ↦
          (⟨k₀ y, hk₀ y⟩ : A) := by
      exact Continuous.subtype_mk k₀.continuous fun y ↦ hk₀ y
    have hPath :
        Continuous fun y : sphereBoundary ((n : ℕ) - 1) ↦
          (Path.mk
            { toFun := fun t ↦ H (unitInterval.symm t, y)
              continuous_toFun := by
                let reversedTime : I → I × sphereBoundary ((n : ℕ) - 1) := fun t ↦
                  (unitInterval.symm t, y)
                have hReversedTime : Continuous reversedTime := by
                  fun_prop
                -- For each fixed boundary point, the path is the reversed nullhomotopy slice.
                simpa [reversedTime] using H.continuous.comp hReversedTime }
            (by
              change H (unitInterval.symm 0, y) = x.1
              simpa using H.apply_one y)
            (by
              change H (unitInterval.symm 1, y) = k₀ y
              simpa using H.apply_zero y) : C(I, X)) := by
      -- Uncurry the homotopy to see continuity of the whole family of reversed paths at once.
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      have hUncurried :
          Continuous fun z : sphereBoundary ((n : ℕ) - 1) × I ↦
            H (unitInterval.symm z.2, z.1) := by
        exact H.continuous.comp (by fun_prop)
      simpa [Function.uncurry] using hUncurried
    -- `PathToSet` carries the induced topology from endpoint and path coordinates.
    rw [continuous_induced_rng]
    change Continuous fun y : sphereBoundary ((n : ℕ) - 1) ↦
      ((⟨k₀ y, hk₀ y⟩ : A),
        (Path.mk
          { toFun := fun t ↦ H (unitInterval.symm t, y)
            continuous_toFun := by
              let reversedTime : I → I × sphereBoundary ((n : ℕ) - 1) := fun t ↦
                (unitInterval.symm t, y)
              have hReversedTime : Continuous reversedTime := by
                fun_prop
              simpa [reversedTime] using H.continuous.comp hReversedTime }
          (by
            change H (unitInterval.symm 0, y) = x.1
            simpa using H.apply_one y)
          (by
            change H (unitInterval.symm 1, y) = k₀ y
            simpa using H.apply_zero y) : C(I, X)))
    exact hEndpoint.prodMk hPath

/-- Helper for Construction 9.5.4: extracting endpoints from the packaged `PathToSet` family
recovers the original boundary map. -/
@[simp] private theorem sphereBoundaryHomotopyToSpherePathToSetMap_endpoint
    (n : ℕ+) (A : Set X) (x : A)
    (k₀ : C(sphereBoundary ((n : ℕ) - 1), X))
    (hk₀ : ∀ y : sphereBoundary ((n : ℕ) - 1), k₀ y ∈ A)
    (H : k₀.Homotopy (ContinuousMap.const _ x.1)) :
    spherePathToSetEndpointMap n A x
        (sphereBoundaryHomotopyToSpherePathToSetMap n A x k₀ hk₀ H) = k₀ := by
  -- The packaged `PathToSet` point keeps the same endpoint by construction.
  ext y
  rfl

/-- Helper for Construction 9.5.4: continuity of a `PathToSet`-valued family is reduced to the
continuity of its endpoint and path coordinates. -/
private theorem pathToSetContinuousOfEndpointPath
    {Y : Type v} [TopologicalSpace Y]
    (A : Set X) (x : A) (e : Y → A) (p : Y → C(I, X))
    (he : Continuous e) (hp : Continuous p)
    (h0 : ∀ y, p y 0 = x.1) (h1 : ∀ y, p y 1 = (e y).1) :
    Continuous (fun y ↦ (PathToSet.mk (e y) (Path.mk (p y) (h0 y) (h1 y)) : PathToSet A x.1)) := by
  -- `PathToSet` has the induced topology from endpoint and path coordinates, so those two
  -- coordinates control continuity of the packaged family.
  rw [continuous_induced_rng]
  change Continuous fun y ↦ (e y, (Path.mk (p y) (h0 y) (h1 y) : C(I, X)))
  exact he.prodMk hp

/-- Helper for Construction 9.5.4: a sphere family of `PathToSet` points determines a relative
disk-boundary triple map by descending its endpoint/nullhomotopy data through the cone
parameterization. -/
private theorem exists_relativeDiskBoundaryMap_of_spherePathToSetMap
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    ∃ f : relativeDiskBoundaryMap n A x,
      f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)) =
        spherePathToSetEndpointMap n A x k := by
  -- First extract the endpoint map and its canonical nullhomotopy from the `PathToSet` data.
  exact
    exists_relativeDiskBoundaryMap_of_sphereBoundaryHomotopy n A x
      (spherePathToSetEndpointMap n A x k)
      (spherePathToSetEndpointMap_mem n A x k)
      (spherePathToSetEndpointHomotopy n A x k)

/-- Helper for Construction 9.5.4: every relative disk-boundary triple map yields a sphere family
of `PathToSet` points by reading off the boundary values and the radial nullhomotopy to the cone
point. -/
private theorem exists_spherePathToSetMap_of_relativeDiskBoundaryMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    ∃ k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1),
      spherePathToSetEndpointMap n A x k =
        f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)) := by
  let H := relativeDiskBoundaryMapBoundaryHomotopy n A x f
  refine ⟨sphereBoundaryHomotopyToSpherePathToSetMap n A x
      (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)))
      (relativeDiskBoundaryMap_mapsTo_boundary n A x f) H, ?_⟩
  -- The endpoint extraction undoes the packaging from the chosen boundary nullhomotopy.
  simpa using sphereBoundaryHomotopyToSpherePathToSetMap_endpoint n A x
    (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)))
    (relativeDiskBoundaryMap_mapsTo_boundary n A x f) H

/-- Helper for Construction 9.5.4: the endpoint/nullhomotopy data of a sphere family descends
explicitly to the standard disk model by quotienting along the cone parameterization. -/
private noncomputable def spherePathToSetEndpointDescendedMap
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    C(unitDisk ((n : ℕ) - 1), X) := by
  let q := diskBoundaryConeParameterization n
  let hfactor :=
    sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization n x.1
      (spherePathToSetEndpointHomotopy n A x k)
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (diskBoundaryConeParameterization_surjective n) q.continuous
  -- Route correction: keep the disk descender in quotient-map normal form instead of hiding it
  -- behind `Classical.choose`, so later homotopy comparisons can rewrite through `lift_comp`.
  exact hq.lift (spherePathToSetEndpointHomotopy n A x k).toContinuousMap hfactor

/-- Helper for Construction 9.5.4: the explicit descended disk map restricts on the boundary to
the endpoint map of the original sphere family. -/
@[simp] private theorem spherePathToSetEndpointDescendedMap_boundary
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    (spherePathToSetEndpointDescendedMap n A x k).comp
        (sphereBoundaryInclusion ((n : ℕ) - 1)) =
      spherePathToSetEndpointMap n A x k := by
  let H := spherePathToSetEndpointHomotopy n A x k
  let q := diskBoundaryConeParameterization n
  let hfactor :=
    sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization n x.1
      H
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (diskBoundaryConeParameterization_surjective n) q.continuous
  let lifted : C(unitDisk ((n : ℕ) - 1), X) := hq.lift H.toContinuousMap hfactor
  ext y
  -- Evaluate the quotient-lift equation on the boundary slice `t = 0`.
  have hdesc :=
    congrArg
      (fun g : C(I × sphereBoundary ((n : ℕ) - 1), X) ↦ g (0, y))
      (hq.lift_comp H.toContinuousMap hfactor)
  change lifted (q (0, y)) = H (0, y) at hdesc
  calc
    lifted (sphereBoundaryInclusion ((n : ℕ) - 1) y) = H (0, y) := by
      simpa [lifted, q, diskBoundaryConeParameterization_zero] using hdesc
    _ = spherePathToSetEndpointMap n A x k y := by
      change k y (unitInterval.symm 0) = (k y).endpoint.1
      simpa [spherePathToSetEndpointMap] using (k y).path.target'

/-- Helper for Construction 9.5.4: the explicit descended disk map sends the cone point to the
basepoint `x`. -/
@[simp] private theorem spherePathToSetEndpointDescendedMap_conePoint
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    spherePathToSetEndpointDescendedMap n A x k (diskBoundaryConePoint n) = x.1 := by
  let H := spherePathToSetEndpointHomotopy n A x k
  let q := diskBoundaryConeParameterization n
  let hfactor :=
    sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization n x.1
      H
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (diskBoundaryConeParameterization_surjective n) q.continuous
  let lifted : C(unitDisk ((n : ℕ) - 1), X) := hq.lift H.toContinuousMap hfactor
  let y₀ : sphereBoundary ((n : ℕ) - 1) := sphereBoundaryBasepoint ((n : ℕ) - 1)
  -- Evaluate the same descended equation on the collapsed top slice.
  have hdesc :=
    congrArg
      (fun g : C(I × sphereBoundary ((n : ℕ) - 1), X) ↦ g (1, y₀))
      (hq.lift_comp H.toContinuousMap hfactor)
  change lifted (q (1, y₀)) = H (1, y₀) at hdesc
  simpa [spherePathToSetEndpointDescendedMap, H, lifted, q, diskBoundaryConeParameterization_one]
    using hdesc

/-- Helper for Construction 9.5.4: the canonical disk-boundary representative attached to a
sphere family is the explicit quotient-map descent of its endpoint/nullhomotopy data. -/
private noncomputable def relativeDiskBoundaryMapOfSpherePathToSetMap
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    relativeDiskBoundaryMap n A x := by
  refine ⟨spherePathToSetEndpointDescendedMap n A x k, ?_, ?_⟩
  · intro y
    -- The explicit descended map agrees with the endpoint map on the boundary sphere.
    have hy :
        spherePathToSetEndpointDescendedMap n A x k
            (sphereBoundaryInclusion ((n : ℕ) - 1) y) =
          spherePathToSetEndpointMap n A x k y := by
      exact ContinuousMap.congr_fun
        (spherePathToSetEndpointDescendedMap_boundary n A x k) y
    rw [hy]
    exact spherePathToSetEndpointMap_mem n A x k y
  · -- The quotient-lift construction also records the collapsed cone point explicitly.
    simpa using spherePathToSetEndpointDescendedMap_conePoint n A x k

/-- Helper for Construction 9.5.4: the chosen disk-boundary representative attached to a sphere
family in `PathToSet A x.1` restricts on the boundary sphere to the endpoint map of that family.
-/
@[simp] private theorem relativeDiskBoundaryMapOfSpherePathToSetMap_boundary
    (n : ℕ+) (A : Set X) (x : A)
    (k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)) :
    (relativeDiskBoundaryMapOfSpherePathToSetMap n A x k).1.comp
        (sphereBoundaryInclusion ((n : ℕ) - 1)) =
      spherePathToSetEndpointMap n A x k := by
  -- The explicit disk descender was built to satisfy the same boundary equation.
  exact spherePathToSetEndpointDescendedMap_boundary n A x k

/-- Helper for Construction 9.5.4: the canonical sphere family in `PathToSet A x.1` attached to a
disk-boundary triple map is obtained by packaging the boundary values together with the radial
nullhomotopy toward the cone point. -/
private noncomputable def spherePathToSetMapOfRelativeDiskBoundaryMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) :=
  sphereBoundaryHomotopyToSpherePathToSetMap n A x
    (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)))
    (relativeDiskBoundaryMap_mapsTo_boundary n A x f)
    (relativeDiskBoundaryMapBoundaryHomotopy n A x f)

/-- Helper for Construction 9.5.4: extracting endpoints from the chosen `PathToSet` family
attached to a disk-boundary triple map recovers the original boundary map. -/
@[simp] private theorem spherePathToSetMapOfRelativeDiskBoundaryMap_endpoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    spherePathToSetEndpointMap n A x
        (spherePathToSetMapOfRelativeDiskBoundaryMap n A x f) =
      f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)) := by
  -- The endpoint extraction undoes the explicit radial packaging.
  simpa [spherePathToSetMapOfRelativeDiskBoundaryMap] using
    sphereBoundaryHomotopyToSpherePathToSetMap_endpoint n A x
      (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)))
      (relativeDiskBoundaryMap_mapsTo_boundary n A x f)
      (relativeDiskBoundaryMapBoundaryHomotopy n A x f)

/-- Helper for Construction 9.5.4: a homotopy through relative disk-boundary triple maps induces
an honest homotopy of the associated canonical sphere families in `PathToSet A x.1`. -/
private noncomputable def relativeDiskBoundaryMapToSpherePathToSetHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    {f g : relativeDiskBoundaryMap n A x}
    (hfg :
      ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeDiskBoundaryTripleMap n A x)) :
    (spherePathToSetMapOfRelativeDiskBoundaryMap n A x f).Homotopy
      (spherePathToSetMapOfRelativeDiskBoundaryMap n A x g) := by
  let H := Classical.choice hfg
  let endpointData : I × sphereBoundary ((n : ℕ) - 1) → A := fun z ↦
    ⟨H (z.1, sphereBoundaryInclusion ((n : ℕ) - 1) z.2), (H.prop z.1).1 z.2⟩
  let pathData : I × sphereBoundary ((n : ℕ) - 1) → C(I, X) := fun z ↦
    { toFun := fun u ↦ H (z.1, diskBoundaryConeParameterization n (unitInterval.symm u, z.2))
      continuous_toFun := by
        let coneSlice : I → I × unitDisk ((n : ℕ) - 1) := fun u ↦
          (z.1, diskBoundaryConeParameterization n (unitInterval.symm u, z.2))
        have hConeSlice : Continuous coneSlice := by
          fun_prop
        -- Restrict the disk homotopy to the radial cone line through the chosen boundary point.
        simpa [coneSlice] using H.continuous.comp hConeSlice }
  have hEndpointData :
      Continuous endpointData := by
    have hRaw :
        Continuous fun z : I × sphereBoundary ((n : ℕ) - 1) ↦
          H (z.1, sphereBoundaryInclusion ((n : ℕ) - 1) z.2) := by
      exact H.continuous.comp (by fun_prop)
    -- Each time slice of `H` is still a relative disk-boundary triple map, so the endpoint lands
    -- in `A`.
    exact Continuous.subtype_mk hRaw fun z ↦ (H.prop z.1).1 z.2
  have hPathData :
      Continuous pathData := by
    -- Uncurry the three-parameter family to see continuity of the packaged paths all at once.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hUncurried :
        Continuous fun w : (I × sphereBoundary ((n : ℕ) - 1)) × I ↦
          H (w.1.1, diskBoundaryConeParameterization n (unitInterval.symm w.2, w.1.2)) := by
      exact H.continuous.comp (by fun_prop)
    simpa [Function.uncurry, pathData] using hUncurried
  have hPathSource :
      ∀ z : I × sphereBoundary ((n : ℕ) - 1), pathData z 0 = x.1 := by
    intro z
    calc
      pathData z 0 =
          H (z.1, diskBoundaryConeParameterization n (unitInterval.symm 0, z.2)) := rfl
      _ = H (z.1, diskBoundaryConePoint n) := by
        simpa using congrArg (fun a ↦ H (z.1, a)) (diskBoundaryConeParameterization_one n z.2)
      _ = x.1 := (H.prop z.1).2
  have hPathTarget :
      ∀ z : I × sphereBoundary ((n : ℕ) - 1), pathData z 1 = (endpointData z).1 := by
    intro z
    calc
      pathData z 1 =
          H (z.1, diskBoundaryConeParameterization n (unitInterval.symm 1, z.2)) := rfl
      _ = H (z.1, sphereBoundaryInclusion ((n : ℕ) - 1) z.2) := by
        simpa using congrArg (fun a ↦ H (z.1, a)) (diskBoundaryConeParameterization_zero n z.2)
      _ = (endpointData z).1 := rfl
  let familyPoint : I × sphereBoundary ((n : ℕ) - 1) → PathToSet A x.1 := fun z ↦
    PathToSet.mk (endpointData z) (Path.mk (pathData z) (hPathSource z) (hPathTarget z))
  refine
    { toContinuousMap :=
        ⟨familyPoint,
          pathToSetContinuousOfEndpointPath A x endpointData pathData
            hEndpointData hPathData hPathSource hPathTarget⟩
      map_zero_left := by
        intro y
        -- Compare the endpoint coordinate and the radial path coordinate separately.
        apply PathToSet.endpointAndPath_injective A x
        refine Prod.ext ?_ ?_
        · apply Subtype.ext
          change H (0, sphereBoundaryInclusion ((n : ℕ) - 1) y) =
            f.1 (sphereBoundaryInclusion ((n : ℕ) - 1) y)
          simpa using H.apply_zero (sphereBoundaryInclusion ((n : ℕ) - 1) y)
        · apply ContinuousMap.ext
          intro u
          change H (0, diskBoundaryConeParameterization n (unitInterval.symm u, y)) =
            f.1 (diskBoundaryConeParameterization n (unitInterval.symm u, y))
          simpa using H.apply_zero
            (diskBoundaryConeParameterization n (unitInterval.symm u, y))
      map_one_left := by
        intro y
        -- The same endpoint/path comparison identifies the final time slice with `g`.
        apply PathToSet.endpointAndPath_injective A x
        refine Prod.ext ?_ ?_
        · apply Subtype.ext
          change H (1, sphereBoundaryInclusion ((n : ℕ) - 1) y) =
            g.1 (sphereBoundaryInclusion ((n : ℕ) - 1) y)
          simpa using H.apply_one (sphereBoundaryInclusion ((n : ℕ) - 1) y)
        · apply ContinuousMap.ext
          intro u
          change H (1, diskBoundaryConeParameterization n (unitInterval.symm u, y)) =
            g.1 (diskBoundaryConeParameterization n (unitInterval.symm u, y))
          simpa using H.apply_one
            (diskBoundaryConeParameterization n (unitInterval.symm u, y)) }

/-- Helper for Construction 9.5.4: a homotopy of free sphere families descends to an honest
homotopy of the explicit quotient-lift disk representatives. -/
private noncomputable def spherePathToSetEndpointDescendedHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    (spherePathToSetEndpointDescendedMap n A x k₀).Homotopy
      (spherePathToSetEndpointDescendedMap n A x k₁) where
  toContinuousMap := by
    let q := diskBoundaryConeParameterization n
    let hq : Topology.IsQuotientMap q :=
      IsQuotientMap.of_surjective_continuous
        (diskBoundaryConeParameterization_surjective n) q.continuous
    let descended : I × unitDisk ((n : ℕ) - 1) → X := fun p ↦
      spherePathToSetEndpointDescendedMap n A x (H.curry p.1) p.2
    have hdescEq :
        (fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
          descended (p.1, q p.2)) =
          fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
            H (p.1, p.2.2) (unitInterval.symm p.2.1) := by
      funext p
      let hfactor :=
        sphereBoundaryHomotopy_factorsThrough_diskBoundaryConeParameterization n x.1
          (spherePathToSetEndpointHomotopy n A x (H.curry p.1))
      have hcomp :
          spherePathToSetEndpointDescendedMap n A x (H.curry p.1) (q p.2) =
            (spherePathToSetEndpointHomotopy n A x (H.curry p.1)) p.2 := by
        exact ContinuousMap.congr_fun
          (hq.lift_comp
            (spherePathToSetEndpointHomotopy n A x (H.curry p.1)).toContinuousMap hfactor)
          p.2
      -- Rewrite the quotient-lift slice back to the raw endpoint/nullhomotopy family.
      calc
        descended (p.1, q p.2) =
            (spherePathToSetEndpointHomotopy n A x (H.curry p.1)) p.2 := by
          simpa [descended, q] using hcomp
        _ = H (p.1, p.2.2) (unitInterval.symm p.2.1) := by
          rfl
    have hraw :
        Continuous fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
          H (p.1, p.2.2) (unitInterval.symm p.2.1) := by
      have hPoint :
          Continuous fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
            H (p.1, p.2.2) := by
        exact H.continuous.comp (by fun_prop)
      have hPath :
          Continuous fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
            (PathToSet.endpointAndPath A x (H (p.1, p.2.2))).2 := by
        exact continuous_snd.comp (continuous_induced_dom.comp hPoint)
      -- Evaluate the path coordinate of the sphere-family homotopy at the reversed radial time.
      simpa [PathToSet.endpointAndPath] using
        (continuous_eval.comp <|
          hPath.prodMk (by
            fun_prop :
              Continuous fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
                unitInterval.symm p.2.1))
    have hdesc :
        Continuous fun p : I × (I × sphereBoundary ((n : ℕ) - 1)) ↦
          descended (p.1, q p.2) := by
      simpa [hdescEq] using hraw
    -- Prove continuity on `I × unitDisk` by checking it after precomposing with the quotient map
    -- on the disk factor.
    exact ⟨descended, hq.continuous_lift_prod_right hdesc⟩
  map_zero_left := by
    intro y
    have hzero : H.curry 0 = k₀ := by
      ext z
      simpa using H.apply_zero z
    -- At time `0`, the descended family is the source quotient-lift representative.
    simpa using
      congrArg (fun k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) ↦
        spherePathToSetEndpointDescendedMap n A x k y) hzero
  map_one_left := by
    intro y
    have hone : H.curry 1 = k₁ := by
      ext z
      simpa using H.apply_one z
    -- At time `1`, the descended family is the target quotient-lift representative.
    simpa using
      congrArg (fun k : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) ↦
        spherePathToSetEndpointDescendedMap n A x k y) hone

/-- Helper for Construction 9.5.4: a homotopy of free sphere families yields a homotopy through
relative disk-boundary triple maps between their canonical disk representatives. -/
private theorem spherePathToSetHomotopyToRelativeDiskBoundaryMapHomotopy
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    ContinuousMap.HomotopicWith
      (relativeDiskBoundaryMapOfSpherePathToSetMap n A x k₀).1
      (relativeDiskBoundaryMapOfSpherePathToSetMap n A x k₁).1
      (IsRelativeDiskBoundaryTripleMap n A x) := by
  refine ⟨{
    toHomotopy := spherePathToSetEndpointDescendedHomotopy n A x H
    prop' := ?_
  }⟩
  intro t
  -- Each intermediate slice is itself the canonical disk representative of `H.curry t`.
  change IsRelativeDiskBoundaryTripleMap n A x
    (spherePathToSetEndpointDescendedMap n A x (H.curry t))
  exact (relativeDiskBoundaryMapOfSpherePathToSetMap n A x (H.curry t)).2

/-- Helper for Construction 9.5.4: the canonical disk-boundary class attached to a free sphere
family depends only on its homotopy class. -/
private theorem relativeDiskBoundaryClassOfSpherePathToSetMap_eq_of_homotopy
    (n : ℕ+) (A : Set X) (x : A)
    {k₀ k₁ : C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1)}
    (H : k₀.Homotopy k₁) :
    (⟦relativeDiskBoundaryMapOfSpherePathToSetMap n A x k₀⟧ :
        relativeDiskBoundaryHomotopyClass n A x) =
      ⟦relativeDiskBoundaryMapOfSpherePathToSetMap n A x k₁⟧ := by
  -- Descend the free-sphere homotopy to the disk model, then pass to the quotient class.
  exact Quotient.sound (spherePathToSetHomotopyToRelativeDiskBoundaryMapHomotopy n A x H)

/-- Helper for Construction 9.5.4: the fixed Section 9.5 sphere-fiber owner already maps to the
current disk-boundary quotient by forgetting the sphere-basepoint condition and descending the
resulting `PathToSet` family to the disk model. -/
private noncomputable def sphereFiberZerothToRelativeDiskBoundaryClass
    (n : ℕ+) (A : Set X) (x : A) :
    ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) →
      relativeDiskBoundaryHomotopyClass n A x :=
  Quotient.lift
    (fun f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) ↦
      ⟦relativeDiskBoundaryMapOfSpherePathToSetMap n A x
          (sphereFiberToSpherePathToSetMap n A x f)⟧)
    (fun f₀ f₁ hff ↦ by
      -- A path in the fixed sphere-evaluation fiber gives a homotopy of the corresponding free
      -- sphere families, so the descended disk class is representative-independent.
      exact relativeDiskBoundaryClassOfSpherePathToSetMap_eq_of_homotopy n A x
        (sphereFiberToSpherePathToSetHomotopy n A x hff))

/-- Helper for Construction 9.5.4: on represented points of the fixed Section 9.5 fiber, the map
to the current disk-boundary quotient is given by the explicit descended disk representative of
the corresponding concrete sphere family. -/
@[simp] private theorem sphereFiberZerothToRelativeDiskBoundaryClass_mk
    (n : ℕ+) (A : Set X) (x : A)
    (f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :
    sphereFiberZerothToRelativeDiskBoundaryClass n A x ⟦f⟧ =
      ⟦relativeDiskBoundaryMapOfSpherePathToSetMap n A x
          (sphereFiberToSpherePathToSetMap n A x f)⟧ := by
  rfl

/-- Helper for Construction 9.5.4: the canonical sphere-family representative of a
disk-boundary homotopy class is well defined in the transport-stable orbit owner. -/
private theorem relativeDiskBoundaryMapToSpherePathToSetOrbit_respects
    (n : ℕ+) (A : Set X) (x : A)
    {f g : relativeDiskBoundaryMap n A x}
    (hfg :
      ContinuousMap.HomotopicWith f.1 g.1 (IsRelativeDiskBoundaryTripleMap n A x)) :
    (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
        (spherePathToSetFiberOrbitPoint n A x
          (spherePathToSetMapOfRelativeDiskBoundaryMap n A x f)) :
      spherePathToSetFiberOrbit n A x) =
      Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
        (spherePathToSetFiberOrbitPoint n A x
          (spherePathToSetMapOfRelativeDiskBoundaryMap n A x g)) := by
  -- Pass from the representative-level disk homotopy to equality in the orbit quotient.
  exact spherePathToSetFiberOrbit_eq_of_homotopy n A x
    (relativeDiskBoundaryMapToSpherePathToSetHomotopy n A x hfg)

/-- Helper for Construction 9.5.4: passing a relative disk-boundary homotopy class to the
transport-stable orbit owner uses the canonical sphere family attached to each representative. -/
private noncomputable def relativeDiskBoundaryClassToSpherePathToSetFiberOrbit
    (n : ℕ+) (A : Set X) (x : A) :
    relativeDiskBoundaryHomotopyClass n A x → spherePathToSetFiberOrbit n A x :=
  Quotient.lift
    (fun f : relativeDiskBoundaryMap n A x ↦
      (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
          (spherePathToSetFiberOrbitPoint n A x
            (spherePathToSetMapOfRelativeDiskBoundaryMap n A x f)) :
        spherePathToSetFiberOrbit n A x))
    (fun _ _ hfg ↦
      relativeDiskBoundaryMapToSpherePathToSetOrbit_respects n A x hfg)

/-- Helper for Construction 9.5.4: on a represented disk-boundary class, the orbit map is given
by the canonical sphere family obtained from that representative. -/
@[simp] private theorem relativeDiskBoundaryClassToSpherePathToSetFiberOrbit_mk
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryMap n A x) :
    relativeDiskBoundaryClassToSpherePathToSetFiberOrbit n A x ⟦f⟧ =
      (Quotient.mk (Relation.EqvGen.setoid (spherePathToSetFiberOrbitRel n A x))
          (spherePathToSetFiberOrbitPoint n A x
            (spherePathToSetMapOfRelativeDiskBoundaryMap n A x f)) :
        spherePathToSetFiberOrbit n A x) := by
  rfl

/-- Helper for Construction 9.5.4: a path-space representative records a continuous endpoint map
from the parameter cube into `A`. -/
private def relativePathLoopEndpointMap
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x) :
    C(I^(relativePathSpaceIndex n), X) where
  toFun a := (p a).endpoint.1
  continuous_toFun := by
    have hPathPoint : Continuous fun a : I^(relativePathSpaceIndex n) ↦ p a := p.1.continuous
    have hEndpoint :
        Continuous fun a : I^(relativePathSpaceIndex n) ↦
          (PathToSet.endpointAndPath A x (p a)).1 := by
      exact continuous_fst.comp (continuous_induced_dom.comp hPathPoint)
    -- The induced-topology presentation of `PathToSet` makes endpoint evaluation continuous.
    simpa [PathToSet.endpointAndPath] using continuous_subtype_val.comp hEndpoint

/-- Helper for Construction 9.5.4: the endpoint map of a path-space representative lands in `A`.
-/
private theorem relativePathLoopEndpointMap_mem
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x)
    (a : I^(relativePathSpaceIndex n)) :
    relativePathLoopEndpointMap n A x p a ∈ A := by
  -- Each `PathToSet` endpoint is constrained to lie in `A`.
  simpa [relativePathLoopEndpointMap] using PathToSet.endpoint_mem (p a)

/-- Helper for Construction 9.5.4: on `boundary(I^(n - 1))`, the endpoint map is the constant
basepoint because the representative itself is the constant path `PathToSet.refl x`. -/
private theorem relativePathLoopEndpointMap_eq_basepoint_of_memBoundary
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x)
    {a : I^(relativePathSpaceIndex n)} (ha : a ∈ Cube.boundary (relativePathSpaceIndex n)) :
    relativePathLoopEndpointMap n A x p a = x.1 := by
  -- The boundary condition identifies the whole `PathToSet` point with the constant path.
  have hp : p a = PathToSet.refl x := p.2 a ha
  simpa [relativePathLoopEndpointMap, PathToSet.refl] using
    congrArg (fun γ : PathToSet A x.1 ↦ γ 1) hp

/-- Helper for Construction 9.5.4: reversing each path in a path-space representative gives a
homotopy from its endpoint map to the constant map at `x`. -/
private def relativePathLoopEndpointHomotopy
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x) :
    (relativePathLoopEndpointMap n A x p).Homotopy (ContinuousMap.const _ x.1) where
  toContinuousMap := by
    let pathPoint : (I × I^(relativePathSpaceIndex n)) → PathToSet A x.1 := fun z ↦ p z.2
    have hPathPoint : Continuous pathPoint := p.1.continuous.comp continuous_snd
    have hPathComponent :
        Continuous fun z : I × I^(relativePathSpaceIndex n) ↦
          (PathToSet.endpointAndPath A x (pathPoint z)).2 := by
      exact continuous_snd.comp (continuous_induced_dom.comp hPathPoint)
    -- Evaluate the family of paths at the reversed time coordinate.
    exact
      { toFun := fun z ↦ p z.2 (unitInterval.symm z.1)
        continuous_toFun := by
          simpa [pathPoint] using
            (continuous_eval.comp <|
              hPathComponent.prodMk (by
                fun_prop :
                  Continuous fun z : I × I^(relativePathSpaceIndex n) ↦
                    unitInterval.symm z.1)) }
  map_zero_left := by
    intro a
    -- At `t = 0` the reversed path is evaluated at its endpoint.
    simpa [relativePathLoopEndpointMap] using (p a).path.target'
  map_one_left := by
    intro a
    -- At `t = 1` the reversed path is evaluated back at its source `x`.
    simpa using (p a).path.source'

/-- Helper for Construction 9.5.4: the reversed-path homotopy is constant on the parameter-cube
boundary because the boundary representative is already `PathToSet.refl x`. -/
private theorem relativePathLoopEndpointHomotopy_eq_basepoint_of_memBoundary
    (n : ℕ+) (A : Set X) (x : A) (p : relativePathSpaceLoop n A x)
    {a : I^(relativePathSpaceIndex n)} (ha : a ∈ Cube.boundary (relativePathSpaceIndex n))
    (t : I) :
    relativePathLoopEndpointHomotopy n A x p (t, a) = x.1 := by
  -- The boundary condition lets us replace the varying path by the constant one before
  -- evaluating at the reversed time coordinate.
  have hp : p a = PathToSet.refl x := p.2 a ha
  simpa [relativePathLoopEndpointHomotopy, PathToSet.refl] using
    congrArg (fun γ : PathToSet A x.1 ↦ γ (unitInterval.symm t)) hp

/-- Helper for Construction 9.5.4: the standard disk contracts linearly to the chosen boundary
basepoint while fixing that boundary basepoint. -/
private def diskBoundaryBasepointParameterization (n : ℕ+) :
    C(I × sphereBoundary ((n : ℕ) - 1), unitDisk ((n : ℕ) - 1)) where
  toFun z := by
    refine ⟨(1 - (z.1 : ℝ)) • (z.2 : V[((n : ℕ) - 1)]) +
        (z.1 : ℝ) • (sphereBoundaryBasepoint ((n : ℕ) - 1) : V[((n : ℕ) - 1)]), ?_⟩
    rw [mem_unitDisk_iff]
    calc
      ‖(1 - (z.1 : ℝ)) • (z.2 : V[((n : ℕ) - 1)]) +
          (z.1 : ℝ) • (sphereBoundaryBasepoint ((n : ℕ) - 1) : V[((n : ℕ) - 1)])‖ ≤
          ‖(1 - (z.1 : ℝ)) • (z.2 : V[((n : ℕ) - 1)])‖ +
            ‖(z.1 : ℝ) • (sphereBoundaryBasepoint ((n : ℕ) - 1) : V[((n : ℕ) - 1)])‖ :=
        norm_add_le _ _
      _ = ‖1 - (z.1 : ℝ)‖ * ‖(z.2 : V[((n : ℕ) - 1)])‖ +
            ‖(z.1 : ℝ)‖ * ‖(sphereBoundaryBasepoint ((n : ℕ) - 1) : V[((n : ℕ) - 1)])‖ := by
        rw [norm_smul, norm_smul]
      _ = (1 - (z.1 : ℝ)) * 1 + (z.1 : ℝ) * 1 := by
        simp [Real.norm_eq_abs, abs_of_nonneg z.1.2.1,
          abs_of_nonneg (sub_nonneg.mpr z.1.2.2), sphereBoundaryBasepoint]
      _ = 1 := by ring
  continuous_toFun := by
    sorry

@[simp] private theorem diskBoundaryBasepointParameterization_zero
    (n : ℕ+) (y : sphereBoundary ((n : ℕ) - 1)) :
    diskBoundaryBasepointParameterization n (0, y) =
      sphereBoundaryInclusion ((n : ℕ) - 1) y := by
  sorry

@[simp] private theorem diskBoundaryBasepointParameterization_one
    (n : ℕ+) (y : sphereBoundary ((n : ℕ) - 1)) :
    diskBoundaryBasepointParameterization n (1, y) =
      sphereBoundaryInclusion ((n : ℕ) - 1) (sphereBoundaryBasepoint ((n : ℕ) - 1)) := by
  sorry

@[simp] private theorem diskBoundaryBasepointParameterization_basepoint
    (n : ℕ+) (t : I) :
    diskBoundaryBasepointParameterization n (t, sphereBoundaryBasepoint ((n : ℕ) - 1)) =
      sphereBoundaryInclusion ((n : ℕ) - 1) (sphereBoundaryBasepoint ((n : ℕ) - 1)) := by
  sorry

/-- Helper for Construction 9.5.4: a pointed disk-boundary map contracts its boundary sphere to
the chosen boundary basepoint, so the associated boundary map is nullhomotopic to the constant
map at `x`. -/
private def relativeDiskBoundaryPointedMapBoundaryHomotopy
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) :
    (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1))).Homotopy
      (ContinuousMap.const _ x.1) where
  toContinuousMap := f.1.comp (diskBoundaryBasepointParameterization n)
  map_zero_left := by
    sorry
  map_one_left := by
    sorry

@[simp] private theorem relativeDiskBoundaryPointedMapBoundaryHomotopy_basepoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) (t : I) :
    relativeDiskBoundaryPointedMapBoundaryHomotopy n A x f
      (t, sphereBoundaryBasepoint ((n : ℕ) - 1)) = x.1 := by
  sorry

/-- Helper for Construction 9.5.4: a pointed disk-boundary map determines a sphere family of
`PathToSet` points whose chosen sphere-basepoint value is exactly `PathToSet.refl x`. -/
private def spherePathToSetMapOfRelativeDiskBoundaryPointedMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) :
    C(sphereBoundary ((n : ℕ) - 1), PathToSet A x.1) :=
  sphereBoundaryHomotopyToSpherePathToSetMap n A x
    (f.1.comp (sphereBoundaryInclusion ((n : ℕ) - 1)))
    (relativeDiskBoundaryPointedMap_mapsTo_boundary n A x f)
    (relativeDiskBoundaryPointedMapBoundaryHomotopy n A x f)

@[simp] private theorem spherePathToSetMapOfRelativeDiskBoundaryPointedMap_basepoint
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) :
    spherePathToSetMapOfRelativeDiskBoundaryPointedMap n A x f
        (sphereBoundaryBasepoint ((n : ℕ) - 1)) =
      PathToSet.refl x := by
  sorry

/-- Helper for Construction 9.5.4: the sphere family attached to a pointed disk-boundary map is
already a point of the fixed Section 9.5 sphere-evaluation fiber over `PathToSet.refl x`. -/
private def sphereFiberPointOfRelativeDiskBoundaryPointedMap
    (n : ℕ+) (A : Set X) (x : A) (f : relativeDiskBoundaryPointedMap n A x) :
    sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) := by
  refine ⟨(spherePathToSetMapOfRelativeDiskBoundaryPointedMap n A x f).comp
      (topCatSphereToSphereBoundary ((n : ℕ) - 1)), ?_⟩
  sorry

/-- Helper for Construction 9.5.4: a fixed Section 9.5 sphere-fiber point descends to a pointed
disk-boundary triple map. -/
private def relativeDiskBoundaryPointedMapOfSphereFiberPoint
    (n : ℕ+) (A : Set X) (x : A)
    (f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :
    relativeDiskBoundaryPointedMap n A x := by
  refine ⟨spherePathToSetEndpointDescendedMap n A x (sphereFiberToSpherePathToSetMap n A x f),
    ?_, ?_⟩
  · sorry
  · sorry

/-- Helper for Construction 9.5.4: passing to homotopy classes sends a fixed Section 9.5
sphere-fiber class to the corresponding pointed disk-boundary homotopy class. -/
private noncomputable def sphereFiberZerothToRelativeDiskBoundaryPointedClass
    (n : ℕ+) (A : Set X) (x : A) :
    ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) →
      relativeDiskBoundaryPointedHomotopyClass n A x :=
  Quotient.lift
    (fun f : sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x) ↦
      ⟦relativeDiskBoundaryPointedMapOfSphereFiberPoint n A x f⟧)
    (fun _ _ _ ↦ by
      sorry)

/-- Helper for Construction 9.5.4: passing to homotopy classes sends a pointed disk-boundary
class to the corresponding class in the fixed Section 9.5 sphere-evaluation fiber. -/
private noncomputable def relativeDiskBoundaryPointedClassToSphereFiberZeroth
    (n : ℕ+) (A : Set X) (x : A) :
    relativeDiskBoundaryPointedHomotopyClass n A x →
      ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x)) :=
  Quotient.lift
    (fun f : relativeDiskBoundaryPointedMap n A x ↦
      ⟦sphereFiberPointOfRelativeDiskBoundaryPointedMap n A x f⟧)
    (fun _ _ _ ↦ by
      sorry)

/-- Helper for Construction 9.5.4: shorthand for the fixed Section 9.5 sphere-evaluation fiber
owner over `PathToSet.refl x`. -/
private abbrev relativeDiskBoundaryPointedSphereFiberZeroth
    (n : ℕ+) (A : Set X) (x : A) : Type u :=
  ZerothHomotopy (sphereBasepointFiber ((n : ℕ) - 1) (PathToSet.refl x))

/-- Helper for Construction 9.5.4: specialize the Section 9.5 sphere-fiber comparison to the
current ambient space `X` so the public source-facing maps do not need explicit named arguments.
-/
private abbrev relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x ≃ relativeDiskBoundaryPointedSphereFiberZeroth n A x :=
  relativeHomotopyGroupEquivSphereFiberZerothPathToSet n A x

/-- Construction 9.5.4 (1): the Chapter 9 owner `relativeHomotopyGroup n A x` is explicitly
identified with the source-faithful pointed disk-boundary model
`(CS^(n - 1), S^(n - 1), *) → (X, A, *)`. -/
def relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x → relativeDiskBoundaryPointedHomotopyClass n A x :=
  fun u ↦
    sphereFiberZerothToRelativeDiskBoundaryPointedClass n A x
      ((relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x) u)

/-- Applying `relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass` sends a relative
homotopy class to the pointed disk-boundary class obtained from the fixed Section 9.5 sphere
fiber. -/
@[simp] theorem relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass_def
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass n A x =
      fun u ↦
        sphereFiberZerothToRelativeDiskBoundaryPointedClass n A x
          ((relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x) u) := rfl

/-- Applying `relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass` sends a relative
homotopy class to the pointed disk-boundary class obtained from the fixed Section 9.5 sphere
fiber. -/
@[simp] theorem relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeHomotopyGroup n A x) :
    relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass n A x u =
      sphereFiberZerothToRelativeDiskBoundaryPointedClass n A x
        ((relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x) u) := rfl

/-- Construction 9.5.4 (2): the pointed disk-boundary model maps back to the
Chapter 9 owner by first returning to the fixed Section 9.5 sphere-evaluation
fiber. -/
def relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup
    (n : ℕ+) (A : Set X) (x : A) :
    relativeDiskBoundaryPointedHomotopyClass n A x → relativeHomotopyGroup n A x :=
  fun u ↦
    (relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x).symm
      (relativeDiskBoundaryPointedClassToSphereFiberZeroth n A x u)

/-- Applying `relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup` returns a pointed
disk-boundary class to the Chapter 9 owner through the fixed Section 9.5 sphere fiber. -/
@[simp] theorem relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup_def
    (n : ℕ+) (A : Set X) (x : A) :
    relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup n A x =
      fun u ↦
        (relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x).symm
          (relativeDiskBoundaryPointedClassToSphereFiberZeroth n A x u) := rfl

/-- Applying `relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup` returns a pointed
disk-boundary class to the Chapter 9 owner through the fixed Section 9.5 sphere fiber. -/
@[simp] theorem relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeDiskBoundaryPointedHomotopyClass n A x) :
    relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup n A x u =
      (relativeHomotopyGroupDiskBoundaryPointedSphereFiberEquiv n A x).symm
        (relativeDiskBoundaryPointedClassToSphereFiberZeroth n A x u) := rfl

def relativeHomotopyGroupDiskBoundaryPointedEquiv
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroup n A x ≃ relativeDiskBoundaryPointedHomotopyClass n A x where
  toFun := relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass n A x
  invFun := relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup n A x
  left_inv := by
    sorry
  right_inv := by
    sorry

/-- `relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass` is the forward function of
`relativeHomotopyGroupDiskBoundaryPointedEquiv`. -/
@[simp] theorem relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass_eq
    (n : ℕ+) (A : Set X) (x : A) :
    relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass n A x =
      relativeHomotopyGroupDiskBoundaryPointedEquiv n A x := rfl

/-- `relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup` is the inverse function of
`relativeHomotopyGroupDiskBoundaryPointedEquiv`. -/
@[simp] theorem relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup_eq
    (n : ℕ+) (A : Set X) (x : A) :
    relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup n A x =
      (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).symm := rfl

/-- Applying `relativeHomotopyGroupDiskBoundaryPointedEquiv` sends a relative homotopy class to
its pointed disk-boundary representative class. -/
@[simp] theorem relativeHomotopyGroupDiskBoundaryPointedEquiv_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeHomotopyGroup n A x) :
    relativeHomotopyGroupDiskBoundaryPointedEquiv n A x u =
      relativeHomotopyGroupToRelativeDiskBoundaryPointedHomotopyClass n A x u := rfl

/-- Applying `(relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).symm` sends a pointed
disk-boundary class back to the Chapter 9 owner through the fixed Section 9.5 sphere fiber. -/
@[simp] theorem relativeHomotopyGroupDiskBoundaryPointedEquiv_symm_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeDiskBoundaryPointedHomotopyClass n A x) :
    (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).symm u =
      relativeDiskBoundaryPointedHomotopyClassToRelativeHomotopyGroup n A x u := rfl

/-- Construction 9.5.4 (3): this also yields the corresponding explicit
comparison from the cubical quotient to the pointed disk-boundary model by
composing with `relativeHomotopyGroupCubeEquiv`. -/
def relativeCubeHomotopyClassDiskBoundaryPointedEquiv
    (n : ℕ+) (A : Set X) (x : A) :
    relativeCubeHomotopyClass n A x ≃ relativeDiskBoundaryPointedHomotopyClass n A x :=
  (relativeHomotopyGroupCubeEquiv n A x).symm.trans
    (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x)

/-- Coercing `relativeCubeHomotopyClassDiskBoundaryPointedEquiv` to a function is definitionally
the composition of the existing cube/path comparison with the pointed disk-boundary comparison. -/
@[simp] theorem relativeCubeHomotopyClassDiskBoundaryPointedEquiv_toFun
    (n : ℕ+) (A : Set X) (x : A) :
    (relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).toFun =
      fun u ↦ relativeHomotopyGroupDiskBoundaryPointedEquiv n A x
        (relativeCubeHomotopyClassToRelativeHomotopyGroup n A x u) := rfl

/-- Coercing `relativeCubeHomotopyClassDiskBoundaryPointedEquiv` to a function is definitionally
the composition of the existing cube/path comparison with the pointed disk-boundary comparison. -/
@[simp] theorem relativeCubeHomotopyClassDiskBoundaryPointedEquiv_coe
    (n : ℕ+) (A : Set X) (x : A) :
    (relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x :
        relativeCubeHomotopyClass n A x → relativeDiskBoundaryPointedHomotopyClass n A x) =
      fun u ↦ relativeHomotopyGroupDiskBoundaryPointedEquiv n A x
        (relativeCubeHomotopyClassToRelativeHomotopyGroup n A x u) := rfl

/-- `relativeCubeHomotopyClassDiskBoundaryPointedEquiv` is definitionally the composition of the
cube/path comparison with the pointed disk-boundary comparison. -/
@[simp] theorem relativeCubeHomotopyClassDiskBoundaryPointedEquiv_def
    (n : ℕ+) (A : Set X) (x : A) :
    relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x =
      (relativeHomotopyGroupCubeEquiv n A x).symm.trans
        (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x) := rfl

/-- Applying `relativeCubeHomotopyClassDiskBoundaryPointedEquiv` is the composition of the
existing cube/path comparison with the pointed disk-boundary comparison. -/
@[simp] theorem relativeCubeHomotopyClassDiskBoundaryPointedEquiv_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeCubeHomotopyClass n A x) :
    relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x u =
      relativeHomotopyGroupDiskBoundaryPointedEquiv n A x
        (relativeCubeHomotopyClassToRelativeHomotopyGroup n A x u) := rfl

/-- Applying `(relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).symm` first returns to
the Chapter 9 owner and then to the cubical quotient. -/
@[simp] theorem relativeCubeHomotopyClassDiskBoundaryPointedEquiv_symm_apply
    (n : ℕ+) (A : Set X) (x : A) (u : relativeDiskBoundaryPointedHomotopyClass n A x) :
    (relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).symm u =
      relativeHomotopyGroupToRelativeCubeHomotopyClass n A x
        ((relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).symm u) := rfl

/-- An explicit comparison between the cubical quotient and the source-faithful pointed
disk-boundary quotient consists of forward and backward maps that are inverse to one another. -/
theorem relativeCubeHomotopyClassHasDiskBoundaryModel
    (n : ℕ+) (A : Set X) (x : A) :
    ∃ forward :
        relativeCubeHomotopyClass n A x → relativeDiskBoundaryPointedHomotopyClass n A x,
      ∃ backward :
          relativeDiskBoundaryPointedHomotopyClass n A x → relativeCubeHomotopyClass n A x,
        Function.LeftInverse backward forward ∧
          Function.RightInverse backward forward := by
  refine ⟨relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x,
    (relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).symm, ?_⟩
  exact ⟨(relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).left_inv,
    (relativeCubeHomotopyClassDiskBoundaryPointedEquiv n A x).right_inv⟩

/-- Construction 9.5.4 (4): with `unitDisk ((n : ℕ) - 1)` as the standard model of `CS^(n - 1)` and
`sphereBoundary ((n : ℕ) - 1)` as `S^(n - 1)`, the cubical quotient
`relativeCubeHomotopyClass n A x`, and hence the Chapter 9 owner `relativeHomotopyGroup n A x`,
are both represented by the pointed disk-boundary model of maps of triples
`(CS^(n - 1), S^(n - 1), *) → (X, A, *)`, where `*` is the chosen basepoint of
`sphereBoundary ((n : ℕ) - 1)`. -/
theorem relativeHomotopyGroupHasDiskBoundaryModel
    (n : ℕ+) (A : Set X) (x : A) :
    ∃ forward :
        relativeHomotopyGroup n A x → relativeDiskBoundaryPointedHomotopyClass n A x,
      ∃ backward :
          relativeDiskBoundaryPointedHomotopyClass n A x → relativeHomotopyGroup n A x,
        Function.LeftInverse backward forward ∧
          Function.RightInverse backward forward := by
  refine ⟨relativeHomotopyGroupDiskBoundaryPointedEquiv n A x,
    (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).symm, ?_⟩
  exact ⟨(relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).left_inv,
    (relativeHomotopyGroupDiskBoundaryPointedEquiv n A x).right_inv⟩
