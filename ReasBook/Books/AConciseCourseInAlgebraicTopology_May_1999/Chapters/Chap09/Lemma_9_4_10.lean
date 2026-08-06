import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Criterion_8_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Example_9_4_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_3_4
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.PartitionOfUnity

open scoped TopCat Topology Topology.Homotopy unitInterval

noncomputable section

-- Semantic recall via `lean_leansearch`: `HomotopyGroup.Pi` is the canonical owner for `π_ n`,
-- while local Chapter 9 precedent records existence-only sphere calculations as
-- `Nonempty (… ≃* …)` when the source does not specify a concrete equivalence datum.

/-- Helper for Lemma 9.4.10: the north pole of `S²`, namely the third coordinate basis vector in
the standard Euclidean model. -/
private theorem northPole_mem :
    (EuclideanSpace.single 2 (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  -- The chosen coordinate vector has norm one, so it lies on the unit sphere.
  simp

/-- Helper for Lemma 9.4.10: the geometric north pole of `S²`. -/
private def northPole : 𝕊 2 :=
  ULift.up ⟨EuclideanSpace.single 2 (1 : ℝ), northPole_mem⟩

/-- Helper for Lemma 9.4.10: the Hopf map sends the standard basepoint of `S³` to the north
pole of `S²`. -/
private theorem hopfMap_sphereThreeBasepoint_eq_northPole :
    hopfMap (sphereBasepoint 3) = northPole := by
  -- Evaluate the explicit Hopf coordinates at the first basis vector in `S³`.
  apply ULift.ext
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [hopfMap, hopfMapVec, sphereBasepoint, northPole]

/-- Helper for Lemma 9.4.10: the explicit Hopf map packaged as a continuous map `S³ → S²`. -/
private def hopfMapContinuousMap :
    C(𝕊 3, 𝕊 2) :=
  ⟨hopfMap, by
    -- Re-run the coordinatewise continuity proof from the Hopf-map construction.
    have hdown : Continuous fun x : 𝕊 3 =>
        (((x.down :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) : EuclideanSpace ℝ (Fin 4))) :=
      continuous_subtype_val.comp continuous_uliftDown
    have h0 : Continuous fun x : 𝕊 3 ↦ x.down.1 0 := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 0).continuous.comp hdown
    have h1 : Continuous fun x : 𝕊 3 ↦ x.down.1 1 := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 1).continuous.comp hdown
    have h2 : Continuous fun x : 𝕊 3 ↦ x.down.1 2 := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 2).continuous.comp hdown
    have h3 : Continuous fun x : 𝕊 3 ↦ x.down.1 3 := by
      simpa using (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 4) 3).continuous.comp hdown
    have hVec : Continuous hopfMapVec := by
      -- Each Hopf coordinate is a polynomial in the ambient Euclidean coordinates.
      refine (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp ?_
      refine continuous_pi fun i : Fin 3 ↦ ?_
      fin_cases i
      · simpa [hopfMapVec] using
          continuous_const.mul ((h0.mul h2).add (h1.mul h3))
      · simpa [hopfMapVec] using
          continuous_const.mul ((h1.mul h2).sub (h0.mul h3))
      · simpa [hopfMapVec] using
          (((h0.pow 2).add (h1.pow 2)).sub (h2.pow 2)).sub (h3.pow 2)
    have hSphere : Continuous fun x : 𝕊 3 ↦
        (⟨hopfMapVec x, hopfMapVec_mem x⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Continuous.subtype_mk hVec fun x ↦ hopfMapVec_mem x
    -- Lift the sphere-valued coordinate map back to the chosen `ULift` presentation of `S²`.
    simpa [hopfMap] using continuous_uliftUp.comp hSphere⟩

/-- Helper for Lemma 9.4.10: the continuous Hopf map still sends the chosen basepoint of `S³` to
the north pole. -/
private theorem hopfMapContinuousMap_basepoint :
    hopfMapContinuousMap (sphereBasepoint 3) = northPole :=
  hopfMap_sphereThreeBasepoint_eq_northPole

/-- Helper for Lemma 9.4.10: `Circle` is path connected via the standard additive-circle
parameterization. -/
private instance circle_pathConnectedSpace : PathConnectedSpace Circle :=
  let e : AddCircle (2 * Real.pi) ≃ₜ Circle := AddCircle.homeomorphCircle'
  -- Push path connectedness across the standard circle homeomorphism.
  e.surjective.pathConnectedSpace e.continuous

/-- Helper for Lemma 9.4.10: `π_1(Circle, z)` is infinite cyclic for every basepoint `z`. -/
private noncomputable def circlePi1MulEquivIntAt (z : Circle) :
    π_ 1 Circle z ≃* Multiplicative ℤ :=
  -- Transport the canonical `π₁` computation at `1 : Circle` along a chosen path from `z`.
  (HomotopyGroup.pi1MulEquivFundamentalGroup z).trans
    ((FundamentalGroup.fundamentalGroupMulEquivOfPath
        (PathConnectedSpace.somePath z (1 : Circle))).trans
      circleFundamentalGroupMulEquivInt.symm)

/-- Helper for Lemma 9.4.10: restricting a trivialization to any subset of its base set still
gives an unbased fibration over that smaller base. -/
private theorem trivializationRestrictPreimageIsFibration
    {E B F : Type*} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace F] [Nonempty F]
    {p : C(E, B)} (e : Bundle.Trivialization F p) {s : Set B} (hs : s ⊆ e.baseSet) :
    IsFibration (p.restrictPreimage s) := by
  sorry

/-- Helper for Lemma 9.4.10: the Hopf bundle local trivializations globalize to an unbased
fibration `S³ → S²`. -/
private theorem hopfMapContinuousMap_isFibration :
    IsFibration hopfMapContinuousMap := by
  -- Route correction: the local chartwise proof is reduced to the canonical Chapter 7
  -- globalization theorem, but importing `Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_4_3` currently
  -- exposes the duplicate declaration `mappingPathSpacePathProjectionContinuous`
  -- (`Lemma_7_3_2` versus `Theorem_7_4_3`). Once that owner-level collision is repaired, the
  -- proof closes by applying `isFibration_of_forall_restrictPreimage_isFibration` to the
  -- partition-of-unity cover built from the Hopf trivialization base sets and the generalized
  -- local helper `trivializationRestrictPreimageIsFibration`.
  sorry

/-- Helper for Lemma 9.4.10: the Hopf map is surjective once its unbased fibration structure is in
place. -/
private theorem hopfMapContinuousMap_surjective :
    Function.Surjective hopfMapContinuousMap :=
  (IsFibration.iff_surjective_and_nonempty_continuousPathLiftingFunction
    hopfMapContinuousMap).1 hopfMapContinuousMap_isFibration |>.1

/-- Helper for Lemma 9.4.10: a partition of unity on `S²` canonically yields `I`-valued
numerating functions. -/
private noncomputable def partitionOfUnityToUnitInterval {ι : Type*}
    (ρ : PartitionOfUnity ι (𝕊 2) (Set.univ : Set (𝕊 2))) (i : ι) :
    C(𝕊 2, I) :=
  { toFun := fun b ↦ ⟨ρ i b, ⟨ρ.nonneg i b, ρ.le_one i b⟩⟩
    continuous_toFun :=
      -- The partition-of-unity summands already land in `[0, 1]`, so they refine to `I`.
      Continuous.subtype_mk (ρ i).continuous fun b ↦ ⟨ρ.nonneg i b, ρ.le_one i b⟩ }

/-- Helper for Lemma 9.4.10: the positivity loci of a partition of unity form the associated
numerable open cover. -/
private noncomputable def numerableOpenCoverOfPartitionOfUnity {ι : Type*}
    (ρ : PartitionOfUnity ι (𝕊 2) (Set.univ : Set (𝕊 2))) :
    NumerableOpenCover ι (𝕊 2) where
  cover i :=
    ⟨(partitionOfUnityToUnitInterval ρ i) ⁻¹' Set.Ioi (0 : I), by
      -- Each cover member is the positivity locus of a continuous `I`-valued summand.
      exact
        (partitionOfUnityToUnitInterval ρ i).continuous.isOpen_preimage _ isOpen_Ioi⟩
  toFun := fun i b ↦ partitionOfUnityToUnitInterval ρ i b
  isOpenCover := by
    -- At every point one partition-of-unity summand is positive.
    refine TopologicalSpace.IsOpenCover.of_sets
      (fun i ↦
        (partitionOfUnityToUnitInterval ρ i).continuous.isOpen_preimage _ isOpen_Ioi) ?_
    ext b
    constructor
    · intro _
      simp
    · intro _
      rcases ρ.exists_pos (by simp : b ∈ (Set.univ : Set (𝕊 2))) with ⟨i, hi⟩
      exact Set.mem_iUnion.2 ⟨i, by simpa [partitionOfUnityToUnitInterval] using hi⟩
  iocPreimage_eq i := by
    -- Inside `I`, membership in `(0, 1]` is equivalent to strict positivity.
    ext b
    constructor
    · intro hb
      exact hb.1
    · intro hb
      exact ⟨hb, le_top⟩
  locallyFinite := by
    -- The positivity loci are contained in the supports of the partition-of-unity summands.
    refine ρ.locallyFinite.subset ?_
    intro i b hb
    have hpos : 0 < ρ i b := by
      simpa [partitionOfUnityToUnitInterval] using hb
    simpa [Function.mem_support] using ne_of_gt hpos

/-- Helper for Lemma 9.4.10: the Hopf map rebased at the north pole of `S²`. -/
private def basedHopfMapNorth :
    basedSpaceAtPoint (𝕊 3) (sphereBasepoint 3) ⟶ basedSpaceAtPoint (𝕊 2) northPole :=
  CategoryTheory.Under.homMk (TopCat.ofHom hopfMapContinuousMap) (by
    -- A based map out of the terminal object is determined by the image of the chosen basepoint.
    ext u
    have hu : u = TopCat.terminalIsoPUnit.inv PUnit.unit := by
      have hu' : TopCat.terminalIsoPUnit.hom u = PUnit.unit := by
        cases TopCat.terminalIsoPUnit.hom u
        rfl
      simpa using congrArg TopCat.terminalIsoPUnit.inv hu'
    subst hu
    simpa [hopfMapContinuousMap] using hopfMapContinuousMap_basepoint)

/-- Helper for Lemma 9.4.10: the actual fiber of the north-based Hopf map is homeomorphic to the
model fiber `Circle`. -/
private noncomputable def hopfNorthFiberHomeomorphCircle :
    actualFiberSet basedHopfMapNorth ≃ₜ Circle := by
  let e : Bundle.Trivialization Circle hopfMap :=
    Classical.choose (hopfMap_isFiberBundle northPole)
  let he : northPole ∈ e.baseSet :=
    Classical.choose_spec (hopfMap_isFiberBundle northPole)
  let fiberHomeomorph :
      actualFiberSet basedHopfMapNorth ≃ₜ ({northPole} : Set (𝕊 2)) × Circle := by
    -- Use the local trivialization through the basepoint to identify the chosen fiber with the
    -- product of the singleton base and the model fiber.
    simpa [actualFiberSet, fiber, basedHopfMapNorth, hopfMapContinuousMap] using
      e.preimageHomeomorph (s := ({northPole} : Set (𝕊 2))) (by
        intro b hb
        rcases Set.mem_singleton_iff.mp hb with rfl
        exact he)
  let singletonProdCircle :
      ({northPole} : Set (𝕊 2)) × Circle ≃ₜ Circle :=
    { toFun := fun x ↦ x.2
      invFun := fun z ↦ (⟨northPole, by simp⟩, z)
      left_inv := by
        rintro ⟨x, z⟩
        apply Prod.ext
        · apply Subtype.ext
          simpa [Set.mem_singleton_iff] using x.2.symm
        · rfl
      right_inv := by
        intro z
        rfl
      continuous_toFun := continuous_snd
      continuous_invFun := continuous_const.prodMk continuous_id }
  -- Collapse the singleton base factor to recover the fiber `Circle`.
  exact fiberHomeomorph.trans singletonProdCircle

/-
The following obsolete adapter mixed the k-ified unbased mapping-path topology with the raw
based subtype topology. No later declaration uses it.

/-- Helper for Lemma 9.4.10: a continuous path-lifting function upgrades to a based path-lifting
function once it sends the canonical based mapping-path-space basepoint to the constant basepoint
path. -/
private theorem basedPathLiftOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    Nonempty (BasedPathLiftingFunction p) := by
  -- The based mapping-path space is definitionally the same subtype as the unbased owner.
  refine ⟨{
    toContinuousMap := s.toContinuousMap
    source_eq := ?_
    proj_comp_eq := ?_
    map_basepoint := hbase
  }⟩
  · intro x
    exact s.source_eq x
  · intro x
    exact s.proj_comp_eq x

/-- Helper for Lemma 9.4.10: a surjective based map with a continuous path lift satisfying the
basepoint condition is a based fibration. -/
private theorem isBasedFibrationOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B) (hsurj : Function.Surjective p.right.hom)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    IsBasedFibration p := by
  -- Convert the unbased path-lifting witness to the Chapter 8 based owner and apply the
  -- criterion characterizing based fibrations.
  let _ : Nonempty (BasedPathLiftingFunction p) :=
    basedPathLiftOfContinuousPathLift p s hbase
  exact (IsBasedFibration.iff_surjective_and_nonempty_basedPathLiftingFunction p).2
    ⟨hsurj, inferInstance⟩
-/

/-- Helper for Lemma 9.4.10: the north-based Hopf map should be shown to be a based fibration by
upgrading the Hopf bundle's local trivializations to a based path-lifting function. -/
-- Route correction: the local trivialization and partition-of-unity interfaces above isolate the
-- remaining blocker to the Chapter 8 bridge from the now-proved unbased Hopf fibration
-- `hopfMapContinuousMap_isFibration` to a based path-lifting function on the universal
-- mapping-path-space test object.
private theorem basedHopfMapNorth_isBasedFibration :
    IsBasedFibration basedHopfMapNorth := by
  sorry

/-- Helper for Lemma 9.4.10: `S²` is path connected, so the north pole can be joined to the
standard sphere basepoint. -/
private instance sphereTwo_pathConnectedSpace : PathConnectedSpace (𝕊 2) := by
  -- Reuse the earlier sphere path-connectedness computation in the first nontrivial dimension.
  simpa using (sphere_pathConnectedSpace_of_two_le (n := 2) (by decide))

/-- Helper for Lemma 9.4.10: a chosen path from the north pole of `S²` to `sphereBasepoint 2`.
-/
private noncomputable def northPoleToSphereBasepoint :
    Path northPole (sphereBasepoint 2) :=
  -- Fix one path now so the later basepoint transport stays owner-level instead of inlining
  -- `PathConnectedSpace.somePath` at each use.
  PathConnectedSpace.somePath northPole (sphereBasepoint 2)

/-- Helper for Lemma 9.4.10: in an exact pair `A ⟶ B ⟶ C`, a trivial source forces the second
map to be injective. -/
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
  -- Cancel the trivial quotient element to recover equality of the original classes.
  calc
    x = x * 1 := by simp
    _ = x * (y⁻¹ * y) := by rw [inv_mul_cancel]
    _ = (x * y⁻¹) * y := by simp [mul_assoc]
    _ = 1 * y := by rw [hquotient]
    _ = y := by simp

/-- Helper for Lemma 9.4.10: in an exact pair `A ⟶ B ⟶ C`, a trivial target forces the first
map to be surjective. -/
private theorem surjective_of_mulExact_of_subsingleton_target
    {A B C : Type*} [Group A] [Group B] [Group C]
    (f : A →* B) (g : B → C) (hfg : Function.MulExact f g)
    [Subsingleton C] :
    Function.Surjective f := by
  intro y
  -- Exactness identifies every target element with an image because the obstruction vanishes.
  have hy : g y = 1 := by
    exact Subsingleton.elim _ _
  exact (hfg _).mp hy

/-- Lemma 9.4.10 (1): the second homotopy group of `S²` at the standard sphere basepoint is
infinite cyclic. -/
-- TODO: Apply `fibrationHomotopyLongExactSequence` to `basedHopfMapNorth`, use
-- `hopfNorthFiberHomeomorphCircle`, `circle_pi1_mulEquiv_int`, the vanishing of `π₁(S³)` and
-- `π₂(S³)`, and then transport the north-pole result back to `sphereBasepoint 2`.
theorem sphereTwo_pi2_mulEquiv_int :
    Nonempty (π_ 2 (𝕊 2) (sphereBasepoint 2) ≃* Multiplicative ℤ) := sorry

/-- Lemma 9.4.10 (2): for every `k : ℕ`, the homotopy groups `π_(k + 3)(S³)` and
`π_(k + 3)(S²)` at the standard sphere basepoints are isomorphic, i.e. `π_n(S³) ≃ π_n(S²)`
for `n ≥ 3`. -/
-- TODO: Apply the same long exact sequence in degree `q = k + 1`, use the vanishing of the
-- neighboring circle groups, and then transport the resulting north-pole equivalence on `S²`
-- back to `sphereBasepoint 2`.
theorem sphereThree_pi_geThree_mulEquiv_sphereTwo (k : ℕ) :
    Nonempty
      (π_ (k + 3) (𝕊 3) (sphereBasepoint 3) ≃*
        π_ (k + 3) (𝕊 2) (sphereBasepoint 2)) := sorry
