import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Topology.CompactOpen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.SphereDiskModel
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open scoped TopCat unitInterval Topology Topology.Homotopy

noncomputable section

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

variable {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z]

-- Semantic recall via `lean_leansearch`: no direct mathlib owner surfaced for the sphere-to-disk
-- extension step deduced from `π_ n(F(e; y₁)) = 0`. The source-facing owner here is the
-- specialized homotopy fiber `homotopyFiberAt`, reusing the Chapter 9 bridge
-- `underTopOfPointMap`.

/-- The homotopy fiber `F(e; y₁)` of `e` pointed by the chosen element `y₁ : Y`. -/
abbrev homotopyFiberAt (e : C(Y, Z)) (y₁ : Y) : BasedSpace :=
  homotopyFiber (underTopOfPointMap e y₁)

/-- Helper for ProofStep 9.6.9: the concrete boundary sphere maps continuously into the canonical
TopCat sphere model by `ULift.up`. -/
def sphereBoundaryToTopCatSphere (n : ℕ) : C(sphereBoundary n, (𝕊 n : TopCat)) :=
  ⟨ULift.up, Homeomorph.ulift.symm.continuous_toFun⟩

/-- Helper for ProofStep 9.6.9: the canonical TopCat sphere model maps continuously back to the
concrete boundary sphere by `ULift.down`. -/
def topCatSphereToSphereBoundary (n : ℕ) : C((𝕊 n : TopCat), sphereBoundary n) :=
  ⟨ULift.down, Homeomorph.ulift.continuous_toFun⟩

/-- Helper for ProofStep 9.6.9: the Section 9.5 sphere-fiber owner identifies `π_ n(X, x)` with
the path components of `sphereBasepointFiber n x`. -/
noncomputable def homotopyGroupEquivSphereBasepointFiberZeroth
    {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X) :
    π_ n X x ≃ ZerothHomotopy (sphereBasepointFiber n x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace n x)
  -- Compare `π_ n` with iterated loops, then use the Section 9.5 fiber model.
  (homotopyGroupEquivZerothHomotopyGenLoop n x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for ProofStep 9.6.9: a based map on the concrete boundary sphere gives a point of the
canonical Section 9.5 sphere-evaluation fiber after transporting through `Homeomorph.ulift`. -/
noncomputable def sphereBoundaryBasedMapToSphereFiber
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X)) (hk₀ : k₀ (sphereBoundaryBasepoint n) = x) :
    sphereBasepointFiber n x :=
  ⟨k₀.comp (topCatSphereToSphereBoundary n),
    (mem_sphereBasepointFiber_iff n x _).2 <| by
    -- The chosen sphere basepoint is exactly the `ULift` of `sphereBoundaryBasepoint n`.
    simpa [sphereBasepoint, sphereBoundaryBasepoint] using hk₀⟩

/-- Helper for ProofStep 9.6.9: if `π_ n(X, x)` is trivial, then every point of the Section 9.5
sphere fiber lies in the same path component as the constant based sphere map. -/
theorem joinedConstSphereFiberOfSubsingletonHomotopyGroup
    {X : Type*} [TopologicalSpace X] (n : ℕ) (x : X) (f : sphereBasepointFiber n x)
    (hπ : Subsingleton (π_ n X x)) :
    Joined f ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩ := by
  let e := homotopyGroupEquivSphereBasepointFiberZeroth n x
  have hsub : Subsingleton (ZerothHomotopy (sphereBasepointFiber n x)) := by
    letI : Subsingleton (π_ n X x) := hπ
    exact Equiv.subsingleton e.symm
  let ηf : ZerothHomotopy (sphereBasepointFiber n x) := Quotient.mk _ f
  let ηc : ZerothHomotopy (sphereBasepointFiber n x) :=
    Quotient.mk _ ⟨ContinuousMap.const _ x, by simp [mem_sphereBasepointFiber_iff]⟩
  have hη : ηf = ηc := Subsingleton.elim _ _
  -- Equality in the path-component quotient is exactly the `Joined` relation.
  exact Quotient.exact hη

/-- Helper for ProofStep 9.6.9: a path in the Section 9.5 sphere fiber between the transported
boundary datum and the constant datum uncarries to an honest homotopy on `sphereBoundary n`. -/
noncomputable def sphereBoundaryHomotopyToConstantOfJoinedFiberPoints
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
  letI : CompactSpace (𝕊 n : TopCat) := by
    simpa using
      Homeomorph.compactSpace
        (Homeomorph.ulift.symm : sphereBoundary n ≃ₜ (𝕊 n : TopCat))
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
  · intro y
    -- Evaluate the path at time `0` and then undo the `ULift` transport of the sphere model.
    change ((γ 0).1) (ULift.up y) = k₀ y
    have hsource :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦
          q.1 (ULift.up y))
        γ.source
    simpa [transported, transportDomain, γmaps, sphereBoundaryBasedMapToSphereFiber, sphereBasepoint,
      sphereBoundaryBasepoint] using hsource
  · intro y
    -- At time `1`, the path lands at the constant based map.
    change ((γ 1).1) (ULift.up y) = x
    have htarget :=
      congrArg
        (fun q : sphereBasepointFiber n x ↦
          q.1 (ULift.up y))
        γ.target
    simpa [transported, transportDomain, γmaps] using htarget

/-- Helper for ProofStep 9.6.9: the radial cone map collapses the top slice
`{1} × sphereBoundary n` to the disk center and keeps the bottom slice as the boundary
inclusion. -/
def sphereBoundaryConeQuotientMap (n : ℕ) : C(I × sphereBoundary n, unitDisk n) where
  toFun p := by
    refine ⟨(1 - (p.1 : ℝ)) • p.2.1, ?_⟩
    rw [mem_unitDisk_iff, norm_smul]
    have hp_nonneg : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.2.2
    have hp_le : 1 - (p.1 : ℝ) ≤ 1 := by linarith [p.1.2.1]
    rw [mem_sphereBoundary_iff.mp p.2.2, Real.norm_of_nonneg hp_nonneg]
    simpa using hp_le
  continuous_toFun := by
    fun_prop

/-- Helper for ProofStep 9.6.9: the radial cone quotient map restricts on the bottom slice
to the standard boundary inclusion. -/
@[simp] theorem sphereBoundaryConeQuotientMap_zero
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (0, x) = sphereBoundaryInclusion n x := by
  apply Subtype.ext
  change (1 - ((0 : I) : ℝ)) • (x : V[n]) = (x : V[n])
  simp

/-- Helper for ProofStep 9.6.9: the radial cone quotient map collapses the top slice
`{1} × sphereBoundary n` to the disk center. -/
@[simp] theorem sphereBoundaryConeQuotientMap_one
    (n : ℕ) (x : sphereBoundary n) :
    sphereBoundaryConeQuotientMap n (1, x) =
      (⟨0, by simp [mem_unitDisk_iff]⟩ : unitDisk n) := by
  apply Subtype.ext
  change (1 - ((1 : I) : ℝ)) • (x : V[n]) = 0
  simp

/-- Helper for ProofStep 9.6.9: the radial cone quotient map from `I × sphereBoundary n` onto
`unitDisk n` is surjective. -/
theorem sphereBoundaryConeQuotientMap_surjective (n : ℕ) :
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

/-- Helper for ProofStep 9.6.9: if a sphere homotopy ends at a constant map, then it is constant
on the fibers of the radial cone quotient map and therefore descends to a disk map. -/
theorem sphereBoundaryHomotopy_factorsThrough_coneQuotient
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    {k₀ : C(sphereBoundary n, X)}
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

/-- Helper for ProofStep 9.6.9: a nullhomotopy of a boundary sphere map descends along the radial
cone quotient to a continuous filler on `unitDisk n`. -/
noncomputable def exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    C(unitDisk n, X) :=
  let q := sphereBoundaryConeQuotientMap n
  let hq : Topology.IsQuotientMap q :=
    IsQuotientMap.of_surjective_continuous
      (sphereBoundaryConeQuotientMap_surjective n) q.continuous
  -- Descend the nullhomotopy across the compact quotient map `I × S^n → D^(n+1)`.
  hq.lift H.toContinuousMap
    (sphereBoundaryHomotopy_factorsThrough_coneQuotient n x H)

/-- Helper for ProofStep 9.6.9: the descended disk filler restricts on the boundary to the
original sphere map. -/
theorem exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant_comp
    (n : ℕ) {X : Type*} [TopologicalSpace X] (x : X)
    (k₀ : C(sphereBoundary n, X))
    (H : k₀.Homotopy (ContinuousMap.const _ x)) :
    (exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant n x k₀ H).comp
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
      (fun f : C(I × sphereBoundary n, X) ↦ f (0, y))
      (hq.lift_comp H.toContinuousMap hfactor)
  change (exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant n x k₀ H)
      (sphereBoundaryConeQuotientMap n (0, y)) = H (0, y) at hdesc
  simpa [exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant, sphereBoundaryConeQuotientMap_zero]
    using hdesc

/-- ProofStep 9.6.9: after tracking the basepoint through the homotopy fiber `F(e; y₁)` and
constructing a based map `k₀ : S^n ⟶ F(e; y₁)`, the vanishing of `π_ n(F(e; y₁))` yields a based
extension of `k₀` across the disk `D^(n+1)`. This is the homotopy-fiber step used in the hard
direction of the technical lemma. -/
theorem exists_unitDiskLift_of_subsingleton_homotopyGroup_homotopyFiberAt
    (n : ℕ) (e : C(Y, Z)) (y₁ : Y)
    (k₀ : C(sphereBoundary n, (homotopyFiberAt e y₁).right))
    (hk₀ :
      k₀ (sphereBoundaryBasepoint n) = underTopBasepoint (homotopyFiberAt e y₁))
    (hπ :
      Subsingleton
        (π_ n (homotopyFiberAt e y₁).right (underTopBasepoint (homotopyFiberAt e y₁)))) :
    ∃ k : C(unitDisk n, (homotopyFiberAt e y₁).right),
      k.comp (sphereBoundaryInclusion n) = k₀ := by
  let x0 : (homotopyFiberAt e y₁).right := underTopBasepoint (homotopyFiberAt e y₁)
  have hjoin :
      Joined
        ((sphereBoundaryBasedMapToSphereFiber (X := (homotopyFiberAt e y₁).right) n x0 k₀ hk₀ :
          sphereBasepointFiber (X := (homotopyFiberAt e y₁).right) n x0))
        ((⟨ContinuousMap.const (TopCat.sphere.{0} n) x0, by simp [mem_sphereBasepointFiber_iff]⟩ :
          sphereBasepointFiber (X := (homotopyFiberAt e y₁).right) n x0)) := by
    -- Trivial `π_ n` makes the packaged based sphere map path-connected to the constant datum.
    simpa [x0] using
      joinedConstSphereFiberOfSubsingletonHomotopyGroup
        (X := (homotopyFiberAt e y₁).right) n x0
        (sphereBoundaryBasedMapToSphereFiber (X := (homotopyFiberAt e y₁).right) n x0 k₀ hk₀) hπ
  let H :
      k₀.Homotopy (ContinuousMap.const (sphereBoundary n) x0) :=
    sphereBoundaryHomotopyToConstantOfJoinedFiberPoints n x0 k₀ hk₀ hjoin
  refine ⟨exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant n
      x0 k₀ H, ?_⟩
  -- Descend the nullhomotopy along the radial cone quotient and read off its boundary value.
  exact exists_unitDiskLift_of_sphereBoundaryHomotopyToConstant_comp n
    x0 k₀ H
