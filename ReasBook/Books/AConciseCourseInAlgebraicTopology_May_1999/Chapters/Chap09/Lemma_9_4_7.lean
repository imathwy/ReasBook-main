import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.Homotopy.HomotopyGroup
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Geometry.Manifold.Instances.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Example_3_2_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Example_5_1_11
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Theorem_7_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Observation_8_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_5_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_5_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_2_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open TopCat (SphereModel sphereModelHomeomorph)
open scoped TopCat Topology Topology.Homotopy unitInterval

-- Semantic recall: `lean_leansearch` identifies `HomotopyGroup.Pi` as the canonical owner for
-- `π_ i X x`; local precedent uses `𝕊 n` for spheres and states triviality via `Subsingleton`.
-- Since `Subsingleton` is a typeclass-valued proposition, the reusable public surface here is a
-- named instance.

/-- Helper for Lemma 9.4.7: the ambient Euclidean model of `SphereModel n` has finrank `n + 1`. -/
private instance sphereModelFinrankFact (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨@finrank_euclideanSpace_fin ℝ _ (n + 1)⟩

/-- Helper for Lemma 9.4.7: spheres of positive dimension are path connected. -/
private theorem sphere_pathConnectedSpace_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    PathConnectedSpace (𝕊 n) := by
  -- Convert the sphere dimension bound into the rank hypothesis used by `isPathConnected_sphere`.
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n + 1 := by
      simpa using Nat.succ_le_succ hn
    have hcard : 1 < (n + 1 : Cardinal) := by
      exact_mod_cast hnat
    simpa using hcard
  let _ : PathConnectedSpace (SphereModel n) := by
    -- Move path connectedness to the concrete sphere model first.
    exact isPathConnected_iff_pathConnectedSpace.mp <|
      by
        simpa [SphereModel] using
          (isPathConnected_sphere
            hdim
            (0 : EuclideanSpace ℝ (Fin (n + 1)))
            (by norm_num : 0 ≤ (1 : ℝ)))
  -- Transfer the resulting path connectedness back across the standard sphere homeomorphism.
  rw [pathConnectedSpace_iff_univ]
  have hs : IsPathConnected (Set.univ : Set (SphereModel n)) := isPathConnected_univ
  simpa using ((sphereModelHomeomorph n).symm.isPathConnected_image).2 hs

/-- Helper for Lemma 9.4.7: the complement of a point in the concrete sphere model is
homeomorphic to Euclidean space via stereographic projection. -/
private def sphereModelPuncturedHomeomorphEuclidean (n : ℕ) (v : SphereModel n) :
    ({v}ᶜ : Set (SphereModel n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  -- Rewrite the source and target of `stereographic'` into the punctured-sphere chart.
  let e : ({v}ᶜ : Set (SphereModel n)) ≃ₜ
      (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    have hsource : (stereographic' n v).source = {v}ᶜ := stereographic'_source v
    have htarget : (stereographic' n v).target = Set.univ := stereographic'_target v
    rw [← hsource, ← htarget]
    exact (stereographic' n v).toHomeomorphSourceTarget
  exact e.trans (Homeomorph.Set.univ (EuclideanSpace ℝ (Fin n)))

/-- Helper for Lemma 9.4.7: the complement of a point in `S^n` itself is homeomorphic to
Euclidean space. -/
private noncomputable def spherePuncturedHomeomorphEuclidean (n : ℕ) (y : 𝕊 n) :
    ({y}ᶜ : Set (𝕊 n)) ≃ₜ EuclideanSpace ℝ (Fin n) := by
  let v : SphereModel n := sphereModelHomeomorph n y
  let e : 𝕊 n ≃ₜ SphereModel n := sphereModelHomeomorph n
  let eComp : ({y}ᶜ : Set (𝕊 n)) ≃ₜ ({v}ᶜ : Set (SphereModel n)) := by
    -- Restrict the sphere-model homeomorphism to the complements of the chosen puncture.
    have hs : ({v}ᶜ : Set (SphereModel n)) ⊆ Set.range e := by
      intro z hz
      exact ⟨e.symm z, by simp⟩
    have hpre : e ⁻¹' ({v}ᶜ : Set (SphereModel n)) = ({y}ᶜ : Set (𝕊 n)) := by
      -- Reduce the complement comparison to injectivity of the sphere-model homeomorphism.
      ext x
      change ¬ e x = v ↔ ¬ x = y
      constructor
      · intro hx hxy
        subst hxy
        exact hx (by simp [e, v])
      · intro hx hxy
        apply hx
        have hxy' : e x = e y := by
          simpa [e, v] using hxy
        exact e.injective hxy'
    exact (Homeomorph.setCongr hpre).symm.trans (e.isEmbedding.homeomorphOfSubsetRange hs)
  -- After moving to the concrete sphere model, apply the stereographic chart there.
  exact eComp.trans (sphereModelPuncturedHomeomorphEuclidean n v)

/-- Helper for Lemma 9.4.7: compactifying the punctured chart centered at `y` recovers `S^n`. -/
private noncomputable def puncturedSphereCompactificationHomeomorph (n : ℕ)
    (y : (𝕊 n : TopCat.{0})) :
    OnePoint (EuclideanSpace ℝ (Fin n)) ≃ₜ (𝕊 n : TopCat.{0}) := by
  let ePunct : ({y}ᶜ : Set (𝕊 n)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
    spherePuncturedHomeomorphEuclidean n y
  let finiteBranch : EuclideanSpace ℝ (Fin n) → (𝕊 n : TopCat.{0}) :=
    fun z ↦ (ePunct.symm z).1
  have hFiniteBranch : Topology.IsEmbedding finiteBranch := by
    -- The finite branch is the inverse punctured chart followed by the subtype inclusion.
    simpa [finiteBranch] using Topology.IsEmbedding.subtypeVal.comp ePunct.symm.isEmbedding
  have hRange : Set.range finiteBranch = ({y}ᶜ : Set (𝕊 n)) := by
    -- The finite branch hits exactly the punctured sphere.
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (ePunct.symm z).2
    · intro hx
      refine ⟨ePunct ⟨x, hx⟩, ?_⟩
      simpa [finiteBranch] using congrArg Subtype.val (ePunct.symm_apply_apply ⟨x, hx⟩)
  let _ : CompactSpace (𝕊 n : TopCat.{0}) := by
    -- `S^n` is the boundary of the compact disk `D^(n + 1)`.
    change CompactSpace (TopCat.diskBoundary (n + 1))
    infer_instance
  -- The compactification point is exactly the puncture omitted by the finite chart.
  exact OnePoint.equivOfIsEmbeddingOfRangeEq y finiteBranch hFiniteBranch hRange

/-- Helper for Lemma 9.4.7: the complement of any point in `S^n` is contractible. -/
private theorem spherePuncturedContractible (n : ℕ) (y : 𝕊 n) :
    ContractibleSpace ({y}ᶜ : Set (𝕊 n)) := by
  let e := spherePuncturedHomeomorphEuclidean n y
  -- Transport the standard contractible structure on Euclidean space back across the punctured
  -- chart.
  exact e.contractibleSpace

/-- Helper for Lemma 9.4.7: any two basepoints in the punctured sphere are joined. -/
private theorem puncturedSphere_joined {n : ℕ} (y : 𝕊 n)
    (xy xy' : ({y}ᶜ : Set (𝕊 n))) :
    Joined xy xy' := by
  let _ : ContractibleSpace ({y}ᶜ : Set (𝕊 n)) := spherePuncturedContractible n y
  -- Contractibility of the punctured sphere upgrades immediately to path connectedness.
  exact PathConnectedSpace.joined xy xy'

/-- Helper for Lemma 9.4.7: the antipodal first basis vector is a point of `S^n`. -/
private theorem oppositeSphereBasepoint_mem (n : ℕ) :
    (-EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin (n + 1))) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  -- The antipodal first basis vector still has norm one, so it lies on the sphere.
  simp

/-- Helper for Lemma 9.4.7: a fixed antipodal point gives a puncture distinct from the chosen
sphere basepoint. -/
private def oppositeSphereBasepoint (n : ℕ) : 𝕊 n :=
  ULift.up ⟨-EuclideanSpace.single 0 (1 : ℝ), oppositeSphereBasepoint_mem n⟩

/-- Helper for Lemma 9.4.7: the standard basepoint of `S^n` is distinct from the chosen antipodal
puncture. -/
private theorem sphereBasepoint_ne_oppositeSphereBasepoint (n : ℕ) :
    sphereBasepoint n ≠ oppositeSphereBasepoint n := by
  -- Compare the zeroth Euclidean coordinates of the two concrete sphere points.
  intro h
  have h0 := congrArg (fun z : 𝕊 n ↦ ((ULift.down z).1 0 : ℝ)) h
  simp [sphereBasepoint, oppositeSphereBasepoint] at h0
  linarith

/-- Helper for Lemma 9.4.7: the punctured-sphere subtype includes continuously into the ambient
sphere. -/
private def puncturedSphereInclusion {n : ℕ} {y : 𝕊 n} :
    C(({y}ᶜ : Set (𝕊 n)), 𝕊 n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Lemma 9.4.7: a representative missing `y` lifts pointwise to the punctured sphere
subtype. -/
private def genLoopLiftToPuncturedSphereMap {i n : ℕ} {x y : 𝕊 n}
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    C(I^(Fin i), ({y}ᶜ : Set (𝕊 n))) where
  toFun t := ⟨γ.1 t, hmiss t⟩
  continuous_toFun := γ.1.continuous.subtype_mk fun t ↦ hmiss t

/-- Helper for Lemma 9.4.7: the lifted representative still has the correct boundary value in the
punctured-sphere subtype. -/
private theorem genLoopLiftToPuncturedSphere_boundary {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y)
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    ∀ t ∈ Cube.boundary (Fin i), genLoopLiftToPuncturedSphereMap γ hmiss t = ⟨x, hxy⟩ := by
  -- On the boundary, the original generalized loop is already the basepoint `x`.
  intro t ht
  apply Subtype.ext
  simpa using γ.2 t ht

/-- Helper for Lemma 9.4.7: a representative missing `y` defines a generalized loop in the
punctured sphere based at `⟨x, hxy⟩`. -/
private def genLoopLiftToPuncturedSphere {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y)
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    Ω^ (Fin i) ({y}ᶜ : Set (𝕊 n)) ⟨x, hxy⟩ :=
  ⟨genLoopLiftToPuncturedSphereMap γ hmiss, genLoopLiftToPuncturedSphere_boundary hxy γ hmiss⟩

/-- Helper for Lemma 9.4.7: forgetting the punctured-sphere subtype recovers the original
representative. -/
private theorem genLoopLiftToPuncturedSphere_subtypeVal {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y)
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    genLoopMap (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n))
        (genLoopLiftToPuncturedSphere hxy γ hmiss) = γ := by
  -- The subtype lift is pointwise the original map, so postcomposition by the inclusion undoes it.
  ext t
  rfl

/-- Helper for Lemma 9.4.7: the punctured-sphere inclusion sends the lifted class back to the
original class. -/
private theorem genLoopLiftToPuncturedSphere_class {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y)
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i ⟨x, hxy⟩
        (⟦genLoopLiftToPuncturedSphere hxy γ hmiss⟧ : π_ i ({y}ᶜ : Set (𝕊 n)) ⟨x, hxy⟩) =
      (⟦γ⟧ : π_ i (𝕊 n) x) := by
  -- Evaluate `e_*` on the chosen representative and collapse the inclusion/complement bridge.
  rw [homotopyGroupMap_mk, genLoopLiftToPuncturedSphere_subtypeVal]
  rfl

/-- Helper for Lemma 9.4.7: the punctured-sphere inclusion preserves the constant homotopy
class. -/
private theorem puncturedSphereInclusion_constClass {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y) :
    (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i ⟨x, hxy⟩
        (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 n)) ⟨x, hxy⟩)⟧) =
      (⟦(GenLoop.const : Ω^ (Fin i) (𝕊 n) x)⟧ : π_ i (𝕊 n) x) := by
  -- Constant representatives stay constant after postcomposition by the subtype inclusion.
  rw [homotopyGroupMap_mk, genLoopMap_const]
  rfl

/-- Helper for Lemma 9.4.7: generalized-loop homotopies are exactly paths in the generalized-loop
space. -/
private theorem genLoop_homotopic_iff_joined
    {N : Type*} {X : Type*} [TopologicalSpace X] {x : X} {p q : Ω^ N X x} :
    GenLoop.Homotopic p q ↔ Joined p q := by
  constructor
  · rintro ⟨H⟩
    let curriedHomotopy := H.toHomotopy.curry
    -- Curry the relative homotopy into a path through the generalized-loop space.
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
    -- Uncurry a path of generalized loops into a boundary-relative homotopy.
    refine ⟨⟨⟨
      (ContinuousMap.comp ⟨Subtype.val, continuous_subtype_val⟩ γ.toContinuousMap).uncurry,
      ?_, ?_⟩, ?_⟩⟩
    · intro y
      change γ 0 y = p y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.source
    · intro y
      change γ 1 y = q y
      exact congrArg (fun r : Ω^ N X x ↦ r y) γ.target
    · intro t y hy
      exact ((γ t).property y hy).trans (p.property y hy).symm

/-- Helper for Lemma 9.4.7: `π_i(X, x)` is the zeroth homotopy set of the iterated loop-space
owner `Ω^ (Fin i) X x`. -/
private abbrev homotopyGroupEquivZerothHomotopyGenLoop
    {X : Type*} [TopologicalSpace X] (N : Type*) (x : X) :
    HomotopyGroup N X x ≃ ZerothHomotopy (Ω^ N X x) :=
  Quotient.congr (Equiv.refl _) fun _ _ ↦ genLoop_homotopic_iff_joined

/-- Helper for Lemma 9.4.7: for the target sphere `𝕊 n`, the Chapter 9 sphere-fiber model
identifies `π_i(𝕊 n, x)` with the path components of the evaluation fiber over `x`. -/
private noncomputable def sphereHomotopyGroupEquivSphereBasepointFiberZeroth
    {i n : ℕ} (x : (𝕊 n : TopCat.{0})) :
    π_ i (𝕊 n : TopCat.{0}) x ≃ ZerothHomotopy (sphereBasepointFiber i x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace i x)
  -- First rewrite `π_i` as path components of the iterated loop-space owner, then convert the
  -- chosen Section 9.5 homeomorphism into a homotopy equivalence on path components.
  (homotopyGroupEquivZerothHomotopyGenLoop (Fin i) x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Lemma 9.4.7: a path between basepoints induces an equivalence on the path
components of the corresponding sphere-evaluation fibers. -/
private noncomputable def sphereBasepointFiberZerothEquivOfPath
    {i n : ℕ} {x x' : (𝕊 n : TopCat.{0})} (β : Path x x') :
    ZerothHomotopy (sphereBasepointFiber i x) ≃ ZerothHomotopy (sphereBasepointFiber i x') :=
  by
    letI : CompactSpace (𝕊 n : TopCat.{0}) := by
      change CompactSpace
        (ULift.{0, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      infer_instance
    letI : T2Space (𝕊 n : TopCat.{0}) := by
      change T2Space
        (ULift.{0, 0} (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))
      infer_instance
    letI : WeaklyLocallyCompactSpace (𝕊 n : TopCat.{0}) := inferInstance
    letI : LocallyCompactSpace (𝕊 n : TopCat.{0}) := inferInstance
    letI : CompactlyGeneratedWeakHausdorffSpace.{0, 0} (𝕊 n : TopCat.{0}) :=
      instCompactlyGeneratedWeakHausdorffSpaceOfLocallyCompact
    exact sphereBasepointFiberZerothEquivOfPathClass i (Path.Homotopic.Quotient.mk β)

/-- Helper for Lemma 9.4.7: a path between basepoints induces an equivalence on `π_i(𝕊 n)`. -/
private noncomputable def sphereHomotopyGroupBasepointChangeEquiv
    {i n : ℕ} {x x' : (𝕊 n : TopCat.{0})} (β : Path x x') :
    π_ i (𝕊 n : TopCat.{0}) x ≃ π_ i (𝕊 n : TopCat.{0}) x' :=
  -- Compare both homotopy groups with the Chapter 7 translated sphere-fiber owner.
  (sphereHomotopyGroupEquivSphereBasepointFiberZeroth (i := i) x).trans <|
    (sphereBasepointFiberZerothEquivOfPath (i := i) β).trans <|
      (sphereHomotopyGroupEquivSphereBasepointFiberZeroth (i := i) x').symm

/-- Helper for Lemma 9.4.7: a homeomorphism preserves and reflects the path relation `Joined`. -/
private theorem joined_iff_homeomorph
    {Y : Type*} {Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {a b : Y} :
    Joined (h a) (h b) ↔ Joined a b := by
  constructor
  · rintro ⟨γ⟩
    -- Pull the path back along the inverse homeomorphism.
    simpa using (show Joined (h.symm (h a)) (h.symm (h b)) from ⟨γ.map h.symm.continuous⟩)
  · rintro ⟨γ⟩
    -- Push the path forward along the homeomorphism.
    exact ⟨γ.map h.continuous⟩

/-- Helper for Lemma 9.4.7: a homeomorphism of generalized-loop spaces preserves the relative
homotopy relation. -/
private theorem genLoopHomotopic_iff_of_homeomorph
    {M : Type*} {N : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z] {y : Y} {z : Z}
    (h : Ω^ M Y y ≃ₜ Ω^ N Z z) {p q : Ω^ M Y y} :
    GenLoop.Homotopic (h p) (h q) ↔ GenLoop.Homotopic p q := by
  -- Translate both homotopy relations to paths, compare them through the homeomorphism, and
  -- translate back.
  rw [genLoop_homotopic_iff_joined, genLoop_homotopic_iff_joined, joined_iff_homeomorph h]

/-- Helper for Lemma 9.4.7: `Fin 1`-indexed generalized loops are the ordinary loop space. -/
private def oneGenLoopHomeomorph
    {Y : Type*} [TopologicalSpace Y] (y : Y) :
    Ω^ (Fin 1) Y y ≃ₜ Ω Y y where
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
        change γ (t 0) = y
        calc
          γ (t 0) = γ 0 := by simpa using congrArg γ hi0
          _ = y := γ.source
      · have hi1 : t 0 = 1 := by
          fin_cases i
          simpa using hi
        change γ (t 0) = y
        calc
          γ (t 0) = γ 1 := by simpa using congrArg γ hi1
          _ = y := γ.target⟩
  left_inv p := by
    ext t
    have ht : t = fun _ : Fin 1 ↦ t 0 := by
      funext i
      fin_cases i
      rfl
    rw [ht]
    rfl
  right_inv γ := by
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

/-- Helper for Lemma 9.4.7: the inverse `Fin 1` loop-homeomorphism sends the constant loop to the
constant generalized loop. -/
@[simp] private theorem oneGenLoopHomeomorph_symm_refl
    {Y : Type*} [TopologicalSpace Y] (y : Y) :
    (oneGenLoopHomeomorph y).symm (Path.refl y) = GenLoop.const := by
  -- The inverse loop-homeomorphism evaluates the same constant loop in every coordinate.
  ext t
  rfl

/-- Helper for Lemma 9.4.7: a homeomorphism of spaces induces a homeomorphism on generalized-loop
spaces. -/
private def genLoopHomeomorph
    {M : Type*} {Y : Type*} {Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (h : Y ≃ₜ Z) {y : Y} {z : Z} (hy : h y = z) :
    Ω^ M Y y ≃ₜ Ω^ M Z z where
  toFun p :=
    ⟨⟨fun t ↦ h (p t), h.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      simpa [hy] using congrArg h (p.2 t ht)⟩
  invFun p :=
    ⟨⟨fun t ↦ h.symm (p t), h.symm.continuous.comp p.1.continuous⟩, fun t ht ↦ by
      have hp : p t = z := p.2 t ht
      calc
        h.symm (p t) = h.symm z := by rw [hp]
        _ = y := (h.symm_apply_eq).2 hy.symm⟩
  left_inv p := by
    ext t
    simp
  right_inv p := by
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

/-- Helper for Lemma 9.4.7: iterated loops on the loop space identify with the next ordinary
iterated loop space. -/
private def loopSpaceRepresentativeHomeomorph
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ Ω^ (Fin (n + 1)) Y y :=
  let e₁ : Ω^ (Fin n) (Ω Y y) (Path.refl y) ≃ₜ Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const :=
    genLoopHomeomorph (oneGenLoopHomeomorph y).symm (oneGenLoopHomeomorph_symm_refl y)
  let e₂ : Ω^ (Fin n) (Ω^ (Fin 1) Y y) GenLoop.const ≃ₜ Ω^ (Fin n ⊕ Fin 1) Y y :=
    GenLoop.genLoopGenLoopEquiv y
  let e₃ : Ω^ (Fin n ⊕ Fin 1) Y y ≃ₜ Ω^ (Fin (n + 1)) Y y :=
    GenLoop.congr y (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1))
  (e₁.trans e₂).trans e₃

/-- Helper for Lemma 9.4.7: the standard loop-space shift descends to an equivalence on homotopy
groups. -/
private def loopSpaceHomotopyGroupEquivPiSucc
    {Y : Type*} [TopologicalSpace Y] (n : ℕ) (y : Y) :
    π_ n (Ω Y y) (Path.refl y) ≃ π_ (n + 1) Y y :=
  -- Descend the representative-level loop-space comparison through the homotopy quotient.
  Quotient.congr (loopSpaceRepresentativeHomeomorph n y) fun _ _ ↦
    (genLoopHomotopic_iff_of_homeomorph (loopSpaceRepresentativeHomeomorph n y)).symm

/-- Helper for Lemma 9.4.7: the representative-level loop-space shift commutes with the subspace
inclusion `A ↪ X`. -/
private theorem loopSpaceRepresentativeHomeomorph_subtypeInclusion
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (n : ℕ)
    (γ : Ω^ (Fin n) (Ω A x) (Path.refl x)) :
    loopSpaceRepresentativeHomeomorph n x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ) =
      genLoopMap (pairSubspaceInclusion A)
        (loopSpaceRepresentativeHomeomorph n x γ) := by
  -- Each stage of the loop-space shift is defined pointwise, so it commutes with inclusion.
  ext t
  rfl

/-- Helper for Lemma 9.4.7: the tail `π₀(Ω-) ≃ π₁(-)` identification carries the loop-space
subtype-inclusion map to the ordinary degree-`1` inclusion map. -/
private theorem pairLoopPiZero_commutes_withPairSubspaceInclusionPiOne
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) :
    (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).toFun ∘
        pairLoopSubspaceInclusionPiZeroMap A x =
      pairSubspaceInclusionHomotopyGroupMap A x 1 ∘
        (loopSpaceHomotopyGroupEquivPiSucc 0 x).toFun := by
  -- Compare both induced maps on loop representatives before passing to the homotopy quotient.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Quotient.mk'
      (loopSpaceRepresentativeHomeomorph 0 x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ)) =
      Quotient.mk'
        (genLoopMap (pairSubspaceInclusion A)
          (loopSpaceRepresentativeHomeomorph 0 x γ))
  exact congrArg Quotient.mk' (loopSpaceRepresentativeHomeomorph_subtypeInclusion A x 0 γ)

/-- Helper for Lemma 9.4.7: the higher loop-space owners from the pair long exact sequence agree
with the direct inclusion-induced map after the standard loop-space shift equivalence. -/
private theorem pairLoopSubspaceInclusion_commutes_withPairSubspaceInclusionPiSucc
    {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (q : ℕ) :
    (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).toFun ∘
        pairLoopSubspaceInclusionHomotopyGroupMap A x q =
      pairSubspaceInclusionHomotopyGroupMap A x (q + 2) ∘
        (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x).toFun := by
  -- Compare both induced maps on iterated-loop representatives before quotienting.
  funext a
  refine Quotient.inductionOn a ?_
  intro γ
  change
    Quotient.mk'
      (loopSpaceRepresentativeHomeomorph (q + 1) x.1
        (genLoopMap (pairLoopSubspaceInclusionMap A x) γ)) =
      Quotient.mk'
        (genLoopMap (pairSubspaceInclusion A)
          (loopSpaceRepresentativeHomeomorph (q + 1) x γ))
  exact congrArg Quotient.mk'
    (loopSpaceRepresentativeHomeomorph_subtypeInclusion A x (q + 1) γ)

/-- Helper for Lemma 9.4.7: based sphere maps at the standard basepoint identify with the chosen
iterated loop-space owner. -/
private noncomputable def sphereBasedMapSpaceHomeomorphGenLoop (i n : ℕ) :
    sphereBasepointBasedMapSpace i (sphereBasepoint n) ≃ₜ
      Ω^ (Fin i) (𝕊 n) (sphereBasepoint n) :=
  let e := Classical.choice
    (sphereBasepointFiber_homeomorphic_iteratedLoopSpace i (sphereBasepoint n : 𝕊 n))
  -- First forget the based-map presentation back to the evaluation fiber, then apply the chosen
  -- Section 9.5 comparison with the iterated loop space.
  (sphereBasepointFiberBasedMapSpaceHomeomorph i (sphereBasepoint n : 𝕊 n)).symm.trans e

/-- Helper for Lemma 9.4.7: the based-map and generalized-loop presentations carry the same path
relation. -/
private theorem sphereBasedMapJoined_iff_genLoopHomotopic
    {i n : ℕ} {f g : sphereBasepointBasedMapSpace i (sphereBasepoint n)} :
    Joined f g ↔
      GenLoop.Homotopic
        (sphereBasedMapSpaceHomeomorphGenLoop i n f)
        (sphereBasedMapSpaceHomeomorphGenLoop i n g) := by
  -- Translate generalized-loop homotopy to paths and use the comparison homeomorphism once.
  rw [genLoop_homotopic_iff_joined]
  rw [joined_iff_homeomorph (sphereBasedMapSpaceHomeomorphGenLoop i n)]

/-- Helper for Lemma 9.4.7: the standard based sphere-mapping space is exactly the Chapter 8
based-mapping-space owner for the same chosen basepoints. -/
private def sphereBasedMapSpaceHomeomorphUnderBasedMapSpace (i n : ℕ) :
    sphereBasepointBasedMapSpace i (sphereBasepoint n : (𝕊 n : TopCat.{0})) ≃ₜ
      underBasedMapSpace
        (underTopOfPoint (𝕊 i : TopCat.{0}) (sphereBasepoint i : (𝕊 i : TopCat.{0})))
        (underTopOfPoint (𝕊 n : TopCat.{0}) (sphereBasepoint n : (𝕊 n : TopCat.{0}))) where
  toEquiv :=
    { toFun := fun f ↦ ⟨f.1, by simpa using f.2⟩
      invFun := fun f ↦ ⟨f.1, by simpa using f.2⟩
      left_inv := fun f ↦ by
        -- Both owners keep the same underlying continuous map, so the round trip is pointwise
        -- the identity.
        ext t
        rfl
      right_inv := fun f ↦ by
        -- The inverse round trip is equally the identity on the underlying continuous map.
        ext t
        rfl }
  continuous_toFun :=
    -- The forward comparison is the identity on the ambient compact-open function space.
    Continuous.subtype_mk continuous_subtype_val fun f ↦ by
      simpa using f.2
  continuous_invFun :=
    -- The inverse comparison is the same identity map read in the opposite owner.
    Continuous.subtype_mk continuous_subtype_val fun f ↦ by
      simpa using f.2

/-- Helper for Lemma 9.4.7: path components of the Chapter 9 based sphere-mapping space agree
with Chapter 8 based homotopy classes of based sphere maps. -/
private noncomputable def sphereBasedMapSpaceZerothHomotopyEquivBasedHomotopyClasses (i n : ℕ) :
    ZerothHomotopy.{0}
        (sphereBasepointBasedMapSpace i (sphereBasepoint n : (𝕊 n : TopCat.{0}))) ≃
      basedHomotopyClasses
        (underTopOfPoint (𝕊 i : TopCat.{0}) (sphereBasepoint i : (𝕊 i : TopCat.{0})))
        (underTopOfPoint (𝕊 n : TopCat.{0}) (sphereBasepoint n : (𝕊 n : TopCat.{0}))) :=
  -- First rewrite the owner of the based mapping space, then apply Observation 8.1.5.
  (zerothHomotopyEquivOfHomotopyEquiv
      (sphereBasedMapSpaceHomeomorphUnderBasedMapSpace i n).toHomotopyEquiv).trans
    (basedHomotopyClassesEquivPi0BasedMappingSpace
      (underTopOfPoint (𝕊 i : TopCat.{0}) (sphereBasepoint i : (𝕊 i : TopCat.{0})))
      (underTopOfPoint (𝕊 n : TopCat.{0}) (sphereBasepoint n : (𝕊 n : TopCat.{0})))).symm

/-- Helper for Lemma 9.4.7: when a representative misses `y`, its class factors through the
contractible punctured sphere and is therefore constant. -/
private theorem homotopyClass_eq_const_ofPointAvoidingRepresentative
    {i n : ℕ} {x y : 𝕊 n} (hxy : x ≠ y)
    (γ : Ω^ (Fin i) (𝕊 n) x) (hmiss : ∀ t, γ.1 t ≠ y) :
    ((⟦γ⟧ : π_ i (𝕊 n) x) = ⟦(GenLoop.const : Ω^ (Fin i) (𝕊 n) x)⟧) := by
  let _ : ContractibleSpace ({y}ᶜ : Set (𝕊 n)) := spherePuncturedContractible n y
  let xy : ({y}ᶜ : Set (𝕊 n)) := ⟨x, hxy⟩
  let _ :
      Subsingleton (π_ i ({y}ᶜ : Set (𝕊 n)) xy) :=
    homotopyGroup_subsingleton_of_contractible i xy
  have hLift :
      (⟦genLoopLiftToPuncturedSphere hxy γ hmiss⟧ :
          π_ i ({y}ᶜ : Set (𝕊 n)) xy) =
        ⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 n)) xy)⟧ := by
    -- The lifted class lies in a contractible punctured sphere, so it equals the constant class.
    exact
      @Subsingleton.elim
        (π_ i ({y}ᶜ : Set (𝕊 n)) xy)
        (homotopyGroup_subsingleton_of_contractible i xy)
        _ _
  have hImageLift :
      (⟦γ⟧ : π_ i (𝕊 n) x) =
        (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i xy
          (⟦genLoopLiftToPuncturedSphere hxy γ hmiss⟧ :
            π_ i ({y}ᶜ : Set (𝕊 n)) xy) := by
    -- The punctured-sphere inclusion returns the lifted representative to the ambient sphere.
    exact (genLoopLiftToPuncturedSphere_class hxy γ hmiss).symm
  have hImageConst :
      (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i xy
          (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 n)) xy)⟧) =
        (⟦(GenLoop.const : Ω^ (Fin i) (𝕊 n) x)⟧ : π_ i (𝕊 n) x) := by
    -- The subtype inclusion also preserves the constant representative.
    simpa [xy] using puncturedSphereInclusion_constClass hxy
  have hImageLiftToConst :
      (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i xy
          (⟦genLoopLiftToPuncturedSphere hxy γ hmiss⟧ :
            π_ i ({y}ᶜ : Set (𝕊 n)) xy) =
        (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i xy
          (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 n)) xy)⟧) := by
    -- Rewrite the lifted punctured-sphere class to the constant one before mapping back.
    rw [hLift]
  exact hImageLift.trans (hImageLiftToConst.trans hImageConst)

/-- Helper for Lemma 9.4.7: the punctured-sphere inclusion uses the same induced map on homotopy
groups as the pair long exact sequence owner `pairSubspaceInclusionHomotopyGroupMap`. -/
private theorem puncturedSphereInclusion_eq_pairSubspaceInclusionMap {i n : ℕ} (y : 𝕊 n)
    (xy : ({y}ᶜ : Set (𝕊 n))) :
    ((puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i xy) =
      pairSubspaceInclusionHomotopyGroupMap ({y}ᶜ : Set (𝕊 n)) xy i := by
  -- Both maps are induced by the same subtype inclusion `({y}ᶜ : Set (𝕊 n)) ↪ 𝕊 n`.
  funext a
  rfl

/-- Helper for Lemma 9.4.7: the pointed tail owner `pairRelativePiZeroHomotopyGroup` is
definitionally the degree-`1` relative homotopy group. -/
private theorem pairRelativePiZeroHomotopyGroup_eq_relativePiOne {X : Type*}
    [TopologicalSpace X] (A : Set X) (x : A) :
    pairRelativePiZeroHomotopyGroup A x = relativeHomotopyGroup 1 A x :=
  rfl

/-- Helper for Lemma 9.4.7: trivial relative `π₁(X, A, x)` collapses the pointed tail owner
`pairRelativePiZeroHomotopyGroup A x`. -/
private theorem pairRelativePiZeroSubsingleton_of_relativePiOneSubsingleton {X : Type*}
    [TopologicalSpace X] (A : Set X) (x : A)
    [Subsingleton (relativeHomotopyGroup 1 A x)] :
    Subsingleton (pairRelativePiZeroHomotopyGroup A x) := by
  -- The two Chapter 9 owners are judgmentally the same in degree `1`.
  simpa [pairRelativePiZeroHomotopyGroup_eq_relativePiOne (A := A) (x := x)] using
    (inferInstance : Subsingleton (relativeHomotopyGroup 1 A x))

/-- Helper for Lemma 9.4.7: triviality of the pointed tail relative term makes the tail
loop-space inclusion map surjective. -/
private theorem pairLoopSubspaceInclusionPiZero_surjective_of_relativePiZeroSubsingleton
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A)
    [Subsingleton (pairRelativePiZeroHomotopyGroup A x)] :
    Function.Surjective (pairLoopSubspaceInclusionPiZeroMap A x) := by
  intro g
  -- Exactness identifies the image of the loop-space inclusion with the kernel of the relative
  -- tail map, and the trivial relative term forces every class into that kernel.
  have hbase : pairLoopToRelativePiZeroMap A x g = pairRelativePiZeroBasepoint A x := by
    exact Subsingleton.elim _ _
  exact (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient A x g).mp hbase

/-- Helper for Lemma 9.4.7: triviality of the positive-degree relative term makes the
loop-space inclusion map from Theorem 9.2.2 surjective. -/
private theorem pairLoopSubspaceInclusion_surjective_of_relativeSubsingleton
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A) (q : ℕ)
    [Subsingleton (relativeHomotopyGroup (q + 1).succPNat A x)] :
    Function.Surjective (pairLoopSubspaceInclusionHomotopyGroupMap A x q) := by
  intro g
  -- Exactness on the native pair-LES owners shows that every ambient class comes from the
  -- subspace once the relative obstruction group is trivial.
  have hbase : pairLoopToRelativeHomotopyGroupMap A x q g = 1 := by
    exact Subsingleton.elim _ _
  exact ((pairHomotopyLongExactSequenceSubspaceToAmbient A x q) g).mp hbase

/-- Helper for Lemma 9.4.7: surjectivity of the tail loop-space owner transfers to surjectivity of
the direct degree-`1` inclusion-induced map. -/
private theorem pairSubspaceInclusion_surjective_of_loopPiZeroOwnerSurjective
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A)
    (hsurj : Function.Surjective (pairLoopSubspaceInclusionPiZeroMap A x)) :
    Function.Surjective (pairSubspaceInclusionHomotopyGroupMap A x 1) := by
  intro g
  let gLoop := (loopSpaceHomotopyGroupEquivPiSucc 0 x.1).symm g
  rcases hsurj gLoop with ⟨aLoop, haLoop⟩
  refine ⟨(loopSpaceHomotopyGroupEquivPiSucc 0 x) aLoop, ?_⟩
  -- Compare the chosen preimage through the degree-`1` loop-space shift compatibility.
  calc
    pairSubspaceInclusionHomotopyGroupMap A x 1
        ((loopSpaceHomotopyGroupEquivPiSucc 0 x) aLoop) =
      (loopSpaceHomotopyGroupEquivPiSucc 0 x.1)
        (pairLoopSubspaceInclusionPiZeroMap A x aLoop) := by
          simpa using
            (congrFun (pairLoopPiZero_commutes_withPairSubspaceInclusionPiOne A x) aLoop).symm
    _ = (loopSpaceHomotopyGroupEquivPiSucc 0 x.1) gLoop := by rw [haLoop]
    _ = g := by simp [gLoop]

/-- Helper for Lemma 9.4.7: surjectivity of the higher loop-space owner transfers to surjectivity
of the direct inclusion-induced map in the corresponding positive degree. -/
private theorem pairSubspaceInclusion_surjective_of_loopOwnerSurjective
    {X : Type*} [TopologicalSpace X] (A : Set X) (x : A) (q : ℕ)
    (hsurj : Function.Surjective (pairLoopSubspaceInclusionHomotopyGroupMap A x q)) :
    Function.Surjective (pairSubspaceInclusionHomotopyGroupMap A x (q + 2)) := by
  intro g
  let gLoop := (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1).symm g
  rcases hsurj gLoop with ⟨aLoop, haLoop⟩
  refine ⟨(loopSpaceHomotopyGroupEquivPiSucc (q + 1) x) aLoop, ?_⟩
  -- Compare the chosen preimage through the higher loop-space shift compatibility.
  calc
    pairSubspaceInclusionHomotopyGroupMap A x (q + 2)
        ((loopSpaceHomotopyGroupEquivPiSucc (q + 1) x) aLoop) =
      (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1)
        (pairLoopSubspaceInclusionHomotopyGroupMap A x q aLoop) := by
          simpa using
            (congrFun
              (pairLoopSubspaceInclusion_commutes_withPairSubspaceInclusionPiSucc A x q)
              aLoop).symm
    _ = (loopSpaceHomotopyGroupEquivPiSucc (q + 1) x.1) gLoop := by rw [haLoop]
    _ = g := by simp [gLoop]

/-- Helper for Lemma 9.4.7: the standard boundary owner for the disk model of `(D^n, S^(n - 1))`
is the range of the boundary inclusion into `unitDisk ((n : ℕ) - 1)`. -/
private abbrev standardBoundaryRange (n : ℕ+) : Set (unitDisk ((n : ℕ) - 1)) :=
  Set.range (sphereBoundaryInclusion ((n : ℕ) - 1))

/-- Helper for Lemma 9.4.7: a point of the standard disk lies in the boundary range exactly when
its ambient norm is `1`. -/
private theorem mem_standardBoundaryRange_iff_norm_eq_one (n : ℕ+)
    (x : unitDisk ((n : ℕ) - 1)) :
    x ∈ standardBoundaryRange n ↔
      ‖(x : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1)))‖ = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    -- The range points are literally the boundary-sphere points viewed inside the disk.
    exact mem_sphereBoundary_iff.mp y.2
  · intro hx
    refine ⟨⟨x.1, ?_⟩, ?_⟩
    · -- A norm-one point of the disk belongs to the boundary sphere.
      simpa [sphereBoundary] using hx
    · -- Repackaging the same ambient point through the inclusion changes no coordinates.
      apply Subtype.ext
      rfl

/-- Helper for Lemma 9.4.7: a point of the standard disk avoids the boundary range exactly when
its ambient norm is strictly less than `1`. -/
private theorem mem_standardBoundaryRange_compl_iff_norm_lt_one (n : ℕ+)
    (x : unitDisk ((n : ℕ) - 1)) :
    x ∈ (standardBoundaryRange n)ᶜ ↔
      ‖(x : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1)))‖ < 1 := by
  rw [Set.mem_compl_iff, mem_standardBoundaryRange_iff_norm_eq_one]
  constructor
  · intro hx
    have hxle :
        ‖(x : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1)))‖ ≤ 1 :=
      mem_unitDisk_iff.mp x.2
    exact lt_of_le_of_ne hxle fun hEq ↦ hx hEq
  · intro hx hxBoundary
    exact (ne_of_lt hx) hxBoundary

/-- Helper for Lemma 9.4.7: the chosen basepoint of the standard boundary range is the image of
`diskBoundaryBasepoint n`. -/
private def standardBoundaryRangeBasepoint (n : ℕ+) : standardBoundaryRange n :=
  ⟨sphereBoundaryInclusion ((n : ℕ) - 1) (diskBoundaryBasepoint n), ⟨_, rfl⟩⟩

/-- Helper for Lemma 9.4.7: the standard boundary owner has only one path component in dimensions
`n > 1`. -/
private theorem standardBoundaryRange_zerothHomotopy_subsingleton
    {n : ℕ+} (hn : 1 < (n : ℕ)) :
    Subsingleton (ZerothHomotopy (standardBoundaryRange n)) := by
  classical
  refine ⟨?_⟩
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro a b
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  rcases ha with ⟨ya, rfl⟩
  rcases hb with ⟨yb, rfl⟩
  have hdim : 1 ≤ ((n : ℕ) - 1) := by
    omega
  let e : ((𝕊 (((n : ℕ) - 1)) : TopCat.{0})) ≃ₜ SphereModel ((n : ℕ) - 1) :=
    sphereModelHomeomorph ((n : ℕ) - 1)
  let _ : PathConnectedSpace ((𝕊 (((n : ℕ) - 1)) : TopCat.{0})) :=
    sphere_pathConnectedSpace_of_one_le hdim
  have hJoinedSphere :
      Joined (e.symm ya) (e.symm yb) :=
    PathConnectedSpace.joined _ _
  have hJoinedBoundary : Joined ya yb := by
    -- Move the path in `S^(n - 1)` back to the concrete boundary sphere before factoring through
    -- the normalized range owner.
    exact (joined_iff_homeomorph e.symm).1 hJoinedSphere
  let f : C(sphereBoundary ((n : ℕ) - 1), standardBoundaryRange n) :=
    ⟨Set.rangeFactorization (sphereBoundaryInclusion ((n : ℕ) - 1)),
      (sphereBoundaryInclusion ((n : ℕ) - 1)).continuous.rangeFactorization⟩
  -- Map the boundary-sphere path through the range factorization to identify the two components.
  exact Quotient.sound <| by
    rcases hJoinedBoundary with ⟨γ⟩
    exact ⟨γ.map f.continuous⟩

/-- Helper for Lemma 9.4.7: the degree-`1` relative obstruction of the standard disk-boundary pair
is trivial once the boundary sphere is path connected. -/
private theorem standardDiskPairRelativePiZero_subsingleton
    {n : ℕ+} (hn : 1 < (n : ℕ)) :
    Subsingleton
      (pairRelativePiZeroHomotopyGroup (standardBoundaryRange n)
        (standardBoundaryRangeBasepoint n)) := by
  let Astd : Set (unitDisk ((n : ℕ) - 1)) := standardBoundaryRange n
  let astd : Astd := standardBoundaryRangeBasepoint n
  let _ : ContractibleSpace (unitDisk ((n : ℕ) - 1)) := by
    -- The standard disk is convex, hence contractible.
    exact
      Convex.contractibleSpace
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1))) (1 : ℝ))
        (by
          refine ⟨0, ?_⟩
          simp [unitDisk, Metric.mem_closedBall])
  let _ : Subsingleton (ZerothHomotopy Astd) :=
    standardBoundaryRange_zerothHomotopy_subsingleton hn
  have hAmbient :
      Subsingleton (pairAmbientLoopPiZeroHomotopyGroup Astd astd) := by
    -- Transfer the contractible-disk vanishing of `π₁` back to the loop-space `π₀` owner.
    refine ⟨?_⟩
    intro g h
    apply (loopSpaceHomotopyGroupEquivPiSucc 0 astd.1).injective
    let _ : Subsingleton (π_ 1 (unitDisk ((n : ℕ) - 1)) astd.1) :=
      homotopyGroup_subsingleton_of_contractible 1 astd.1
    exact Subsingleton.elim _ _
  refine ⟨?_⟩
  intro r s
  let a₀ : pairSubspaceLoopPiZeroHomotopyGroup Astd astd := default
  have hBase :
      pairLoopToRelativePiZeroMap Astd astd
          (pairLoopSubspaceInclusionPiZeroMap Astd astd a₀) =
        pairRelativePiZeroBasepoint Astd astd := by
    -- Exactness at the ambient loop-space owner identifies the image of the subspace inclusion
    -- with the kernel of the relative tail map.
    exact
      (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient Astd astd
        (pairLoopSubspaceInclusionPiZeroMap Astd astd a₀)).2 ⟨a₀, rfl⟩
  have hrBoundary : pairHomotopyBoundaryZeroMap Astd astd r = ⟦astd⟧ := by
    -- The boundary range is path connected, so the terminal boundary map is forced to the
    -- distinguished component.
    exact Subsingleton.elim _ _
  have hsBoundary : pairHomotopyBoundaryZeroMap Astd astd s = ⟦astd⟧ := by
    exact Subsingleton.elim _ _
  rcases
      (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative Astd astd r).mp hrBoundary with
    ⟨g, hg⟩
  rcases
      (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative Astd astd s).mp hsBoundary with
    ⟨g', hg'⟩
  have hgBase : g = pairLoopSubspaceInclusionPiZeroMap Astd astd a₀ := by
    exact Subsingleton.elim _ _
  have hg'Base : g' = pairLoopSubspaceInclusionPiZeroMap Astd astd a₀ := by
    exact Subsingleton.elim _ _
  -- Every relative class lifts to the unique ambient loop component, and that unique component
  -- already maps to the relative basepoint.
  calc
    r = pairLoopToRelativePiZeroMap Astd astd
        (pairLoopSubspaceInclusionPiZeroMap Astd astd a₀) := by
          rw [← hg, hgBase]
    _ = pairRelativePiZeroBasepoint Astd astd := hBase
    _ = pairLoopToRelativePiZeroMap Astd astd
        (pairLoopSubspaceInclusionPiZeroMap Astd astd a₀) := hBase.symm
    _ = s := by
          rw [← hg', hg'Base]

/-- Helper for Lemma 9.4.7: choosing the disk-boundary model data packages an explicit
comparison from relative homotopy groups to the relative disk-boundary quotient. -/
private noncomputable def relativeHomotopyGroupEquivRelativeDiskBoundaryClass
    {X : Type*} [TopologicalSpace X] (q : ℕ+) (A : Set X) (a : A) :
    relativeHomotopyGroup q A a ≃ relativeDiskBoundaryPointedHomotopyClass q A a :=
  let hModel := relativeHomotopyGroupHasDiskBoundaryModel q A a
  let forward := Classical.choose hModel
  let backward := Classical.choose (Classical.choose_spec hModel)
  let hInverse := Classical.choose_spec (Classical.choose_spec hModel)
  -- Package the chosen disk-boundary comparison maps as one explicit equivalence.
  { toFun := forward
    invFun := backward
    left_inv := hInverse.1
    right_inv := hInverse.2 }

/-- Helper for Lemma 9.4.7: a homeomorphism of spaces induces an equivalence of positive-degree
iterated loop-space owners. -/
private noncomputable def genLoopEquivOfHomeomorphSucc
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (q : ℕ) (x : X) :
    Ω^ (Fin (q + 1)) X x ≃ Ω^ (Fin (q + 1)) Y (e x) where
  toFun := fun γ ↦
    ⟨⟨fun t ↦ e (γ.1 t), e.continuous_toFun.comp γ.1.continuous⟩,
      fun t ht ↦ by simpa using congrArg e (γ.2 t ht)⟩
  invFun := fun γ ↦
    ⟨⟨fun t ↦ e.symm (γ.1 t), e.symm.continuous_toFun.comp γ.1.continuous⟩,
      fun t ht ↦ by
        change e.symm (γ.1 t) = x
        rw [γ.2 t ht]
        exact e.left_inv x⟩
  left_inv := by
    -- Both iterated-loop maps cancel pointwise after applying `e.symm ∘ e`.
    intro γ
    ext t
    simp
  right_inv := by
    -- The same pointwise cancellation works in the opposite direction.
    intro γ
    ext t
    simp

/-- Helper for Lemma 9.4.7: generalized-loop homotopies are preserved and reflected by the
iterated-loop equivalence induced from a homeomorphism of spaces. -/
private theorem genLoopHomotopic_iff_ofHomeomorphSucc
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (q : ℕ) (x : X)
    {p q' : Ω^ (Fin (q + 1)) X x} :
    GenLoop.Homotopic
        (genLoopEquivOfHomeomorphSucc e q x p)
        (genLoopEquivOfHomeomorphSucc e q x q') ↔
      GenLoop.Homotopic p q' := by
  constructor
  · intro hpq
    -- Compose the homotopy with `e.symm` to return to the original loop owner.
    change p.1.HomotopicRel q'.1 (Cube.boundary (Fin (q + 1)))
    let esymm : C(Y, X) := ⟨e.symm, e.symm.continuous_toFun⟩
    have hcomp := ContinuousMap.HomotopicRel.comp_continuousMap hpq esymm
    have hp :
        esymm.comp (genLoopEquivOfHomeomorphSucc e q x p).1 = p.1 := by
      ext t
      simp [esymm, genLoopEquivOfHomeomorphSucc]
    have hq :
        esymm.comp (genLoopEquivOfHomeomorphSucc e q x q').1 = q'.1 := by
      ext t
      simp [esymm, genLoopEquivOfHomeomorphSucc]
    exact hp ▸ hq ▸ hcomp
  · intro hpq
    -- Compose the homotopy with `e` to move it into the transported loop owner.
    change
      (genLoopEquivOfHomeomorphSucc e q x p).1.HomotopicRel
        (genLoopEquivOfHomeomorphSucc e q x q').1
        (Cube.boundary (Fin (q + 1)))
    let econt : C(X, Y) := ⟨e, e.continuous_toFun⟩
    have hcomp := ContinuousMap.HomotopicRel.comp_continuousMap hpq econt
    have hp :
        econt.comp p.1 = (genLoopEquivOfHomeomorphSucc e q x p).1 := by
      ext t
      simp [econt, genLoopEquivOfHomeomorphSucc]
    have hq :
        econt.comp q'.1 = (genLoopEquivOfHomeomorphSucc e q x q').1 := by
      ext t
      simp [econt, genLoopEquivOfHomeomorphSucc]
    exact hp ▸ hq ▸ hcomp

/-- Helper for Lemma 9.4.7: a homeomorphism induces an equivalence on positive-degree homotopy
groups at the transported basepoint. -/
private noncomputable def homotopyGroupSuccEquivOfHomeomorph
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (q : ℕ) (x : X) :
    π_ (q + 1) X x ≃ π_ (q + 1) Y (e x) :=
  -- Descend the iterated-loop equivalence through the homotopy quotient.
  Quotient.congr (genLoopEquivOfHomeomorphSucc e q x) fun _ _ ↦
    (genLoopHomotopic_iff_ofHomeomorphSucc e q x).symm

/-- Helper for Lemma 9.4.7: every punctured sphere has a convenient reference basepoint chosen
from the two fixed antipodal sphere points already used in this file. -/
private noncomputable def puncturedSphereReferenceBasepoint (n : ℕ) (y : 𝕊 n) :
    ({y}ᶜ : Set (𝕊 n)) := by
  classical
  by_cases hy : sphereBasepoint n ≠ y
  · exact ⟨sphereBasepoint n, hy⟩
  · exact ⟨oppositeSphereBasepoint n, by
      -- If `y` is the standard basepoint, use the fixed antipodal puncture instead.
      intro hop
      apply sphereBasepoint_ne_oppositeSphereBasepoint n
      have hbase : sphereBasepoint n = y := not_not.mp hy
      exact hbase.trans hop.symm⟩

/-- Helper for Lemma 9.4.7: when the standard sphere basepoint avoids the puncture, the chosen
reference basepoint is exactly that standard basepoint viewed in the punctured sphere. -/
private theorem puncturedSphereReferenceBasepoint_eq_of_ne {n : ℕ} {y : 𝕊 n}
    (hy : sphereBasepoint n ≠ y) :
    puncturedSphereReferenceBasepoint n y = ⟨sphereBasepoint n, hy⟩ := by
  -- Unfold the reference-basepoint choice and keep only the branch picked by `hy`.
  simp [puncturedSphereReferenceBasepoint, hy]

/-- Helper for Lemma 9.4.7: the chosen reference basepoint and any other point of the same
punctured sphere lie in one path component. -/
private theorem puncturedSphereReferenceBasepoint_joined (n : ℕ) (y : 𝕊 n)
    (xy : ({y}ᶜ : Set (𝕊 n))) :
    Joined (puncturedSphereReferenceBasepoint n y) xy := by
  -- The punctured sphere is contractible, so all of its basepoints are joined.
  exact puncturedSphere_joined y (puncturedSphereReferenceBasepoint n y) xy

/-- Helper for Lemma 9.4.7: the standard boundary-range owner is homeomorphic to the concrete
boundary sphere that parametrizes it. -/
private noncomputable abbrev standardBoundaryRangeHomeomorphSphereBoundary (n : ℕ+) :
    standardBoundaryRange n ≃ₜ sphereBoundary ((n : ℕ) - 1) :=
  -- The boundary inclusion is an embedding whose range is exactly `standardBoundaryRange n`.
  ((sphereBoundaryInclusion ((n : ℕ) - 1)).continuous.isClosedEmbedding fun a b hab ↦ by
      cases a
      cases b
      cases hab
      rfl).toIsEmbedding.toHomeomorph.symm

/-- Helper for Lemma 9.4.7: the standard boundary-range owner is homeomorphic to the usual
topological sphere `S^(n - 1)`. -/
private noncomputable def standardBoundaryRangeHomeomorphSphere (n : ℕ+) :
    standardBoundaryRange n ≃ₜ (𝕊 (((n : ℕ) - 1)) : TopCat.{0}) :=
  -- First identify the range owner with the concrete boundary sphere, then use the standard
  -- sphere-model homeomorphism.
  (standardBoundaryRangeHomeomorphSphereBoundary n).trans
    (sphereModelHomeomorph ((n : ℕ) - 1)).symm

/-- Helper for Lemma 9.4.7: the standard boundary-range basepoint lands at the usual sphere
basepoint under the canonical boundary-range homeomorphism. -/
private theorem standardBoundaryRangeHomeomorphSphere_basepoint (n : ℕ+) :
    standardBoundaryRangeHomeomorphSphere n (standardBoundaryRangeBasepoint n) =
      (sphereBasepoint ((n : ℕ) - 1) : (𝕊 (((n : ℕ) - 1)) : TopCat.{0})) := by
  let eRange :=
    ((sphereBoundaryInclusion ((n : ℕ) - 1)).continuous.isClosedEmbedding fun a b hab ↦ by
      cases a
      cases b
      cases hab
      rfl).toIsEmbedding.toHomeomorph
  have hRange :
      standardBoundaryRangeHomeomorphSphereBoundary n (standardBoundaryRangeBasepoint n) =
        diskBoundaryBasepoint n := by
    -- The range homeomorphism is literally the inverse of the boundary inclusion onto its image.
    apply eRange.injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  -- After identifying the range owner with the concrete boundary sphere, the remaining map is the
  -- standard sphere-model homeomorphism at the chosen first-basis-vector basepoint.
  calc
    standardBoundaryRangeHomeomorphSphere n (standardBoundaryRangeBasepoint n) =
        (sphereModelHomeomorph ((n : ℕ) - 1)).symm
          (standardBoundaryRangeHomeomorphSphereBoundary n (standardBoundaryRangeBasepoint n)) := by
            rfl
    _ = (sphereModelHomeomorph ((n : ℕ) - 1)).symm (diskBoundaryBasepoint n) := by rw [hRange]
    _ = (sphereBasepoint ((n : ℕ) - 1) : (𝕊 (((n : ℕ) - 1)) : TopCat.{0})) := by
          rfl

/-- Helper for Lemma 9.4.7: a lower-sphere vanishing input transports to the standard
boundary-range owner. -/
private theorem standardBoundaryRangeHomotopyGroupSubsingleton_ofSphereSubsingleton
    {q : ℕ} (n : ℕ+)
    (hSphere :
      Subsingleton
        (π_ (q + 1) (𝕊 (((n : ℕ) - 1)) : TopCat.{0}) (sphereBasepoint ((n : ℕ) - 1)))) :
    Subsingleton (π_ (q + 1) (standardBoundaryRange n) (standardBoundaryRangeBasepoint n)) := by
  let e := standardBoundaryRangeHomeomorphSphere n
  have hSphere :
      Subsingleton
        (π_ (q + 1) (𝕊 (((n : ℕ) - 1)) : TopCat.{0})
          (e (standardBoundaryRangeBasepoint n))) := by
    -- Normalize the target basepoint to the canonical sphere basepoint once.
    simpa [e, standardBoundaryRangeHomeomorphSphere_basepoint] using hSphere
  -- Transport the subsingleton fact back across the homeomorphism-induced equivalence.
  refine ⟨fun a b ↦ ?_⟩
  exact
    (homotopyGroupSuccEquivOfHomeomorph e q (standardBoundaryRangeBasepoint n)).injective
      (Subsingleton.elim _ _)

/-- Helper for Lemma 9.4.7: the connecting map `π_(q + 2)(X, x) → π_(q + 2)(X, A, x)` sends the
unit class to the unit class. -/
private theorem pairLoopToRelativeHomotopyGroupMap_one {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (q : ℕ) :
    pairLoopToRelativeHomotopyGroupMap A x q 1 = 1 := by
  -- Unfold the transported `e_*` definition and reduce to the standard homotopy-group map lemma.
  cases relativeHomotopyGroup_succ (q + 1) A x
  change homotopyGroupMap (pairLoopToRelativePathSpaceMap A x) (q + 1) (Path.refl x.1) 1 = 1
  exact homotopyGroupMap_one (pairLoopToRelativePathSpaceMap A x) q (Path.refl x.1)

/-- Helper for Lemma 9.4.7: the pair boundary map in positive degrees is multiplicative. -/
private noncomputable def pairHomotopyBoundaryMulHom {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (q : ℕ) :
    relativeHomotopyGroup (q + 1).succPNat A x →* π_ (q + 1) A x := by
  -- After rewriting the relative group as the path-space homotopy group, this is the ordinary
  -- multiplicative induced map of the endpoint projection.
  cases relativeHomotopyGroup_succ (q + 1) A x
  exact (pairRelativeEndpointMap A x).eStarMulHomOverEq q (pairRelativeEndpointMap_refl A x)

/-- Helper for Lemma 9.4.7: the bundled positive-degree pair boundary map is the same function as
`pairHomotopyBoundaryMap`. -/
private theorem pairHomotopyBoundaryMulHom_apply {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : A) (q : ℕ)
    (u : relativeHomotopyGroup (q + 1).succPNat A x) :
    pairHomotopyBoundaryMulHom A x q u = pairHomotopyBoundaryMap A x q u := by
  -- Both owners are definitionally the same transported map after opening `relativeHomotopyGroup`.
  cases relativeHomotopyGroup_succ (q + 1) A x
  rfl

/-- Helper for Lemma 9.4.7: once the boundary homotopy group is already trivial, the positive
relative group of the standard disk-boundary pair is trivial as well. -/
private theorem standardDiskPairRelativeSubsingleton_ofBoundarySubsingleton
    {q : ℕ} {n : ℕ+}
    [Subsingleton (π_ (q + 1) (standardBoundaryRange n) (standardBoundaryRangeBasepoint n))] :
    Subsingleton
      (relativeHomotopyGroup (q + 1).succPNat (standardBoundaryRange n)
        (standardBoundaryRangeBasepoint n)) := by
  let Astd : Set (unitDisk ((n : ℕ) - 1)) := standardBoundaryRange n
  let astd : Astd := standardBoundaryRangeBasepoint n
  let _ : ContractibleSpace (unitDisk ((n : ℕ) - 1)) := by
    -- The standard disk is convex, hence contractible.
    exact
      Convex.contractibleSpace
        (convex_closedBall (0 : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1))) (1 : ℝ))
        (by
          refine ⟨0, ?_⟩
          simp [unitDisk, Metric.mem_closedBall])
  have hAmbient :
      Subsingleton (π_ (q + 1) (Ω (unitDisk ((n : ℕ) - 1)) astd.1) (Path.refl astd.1)) := by
    -- Shift the ambient loop owner back to `π_(q + 2)` of the contractible disk.
    refine ⟨?_⟩
    intro g h
    apply (loopSpaceHomotopyGroupEquivPiSucc (q + 1) astd.1).injective
    let _ : Subsingleton (π_ (q + 2) (unitDisk ((n : ℕ) - 1)) astd.1) :=
      homotopyGroup_subsingleton_of_contractible (q + 2) astd.1
    exact Subsingleton.elim _ _
  refine ⟨?_⟩
  intro u v
  let δ := pairHomotopyBoundaryMulHom Astd astd q
  have huvδ : δ u = δ v := by
    exact Subsingleton.elim _ _
  have hkernel :
      pairHomotopyBoundaryMap Astd astd q (u * v⁻¹) = 1 := by
    -- Convert equality of boundary images into a kernel statement for `u * v⁻¹`.
    change δ (u * v⁻¹) = 1
    rw [δ.map_mul, δ.map_inv, huvδ, mul_inv_cancel]
  rcases (pairHomotopyLongExactSequenceAmbientToRelative Astd astd q (u * v⁻¹)).mp hkernel with
    ⟨g, hg⟩
  have hgOne : g = 1 := Subsingleton.elim _ _
  have huMulV : u * v⁻¹ = 1 := by
    -- The only ambient loop class is the unit, so exactness forces the kernel element to be the
    -- unit class as well.
    rw [← hg, hgOne, pairLoopToRelativeHomotopyGroupMap_one]
  -- Cancel the inverse on the right to recover equality of the two relative classes.
  calc
    u = u * (v⁻¹ * v) := by simp
    _ = (u * v⁻¹) * v := by rw [mul_assoc]
    _ = 1 * v := by rw [huMulV]
    _ = v := by simp

/-- Helper for Lemma 9.4.7: a lower-sphere vanishing input collapses the positive relative group
of the standard disk-boundary pair. -/
private theorem standardDiskPairRelativeSubsingletonOfSphereSubsingleton
    {q : ℕ} (n : ℕ+)
    (hSphere :
      Subsingleton
        (π_ (q + 1) (𝕊 (((n : ℕ) - 1)) : TopCat.{0}) (sphereBasepoint ((n : ℕ) - 1)))) :
    Subsingleton
      (relativeHomotopyGroup (q + 1).succPNat (standardBoundaryRange n)
        (standardBoundaryRangeBasepoint n)) := by
  let _ :
      Subsingleton (π_ (q + 1) (standardBoundaryRange n) (standardBoundaryRangeBasepoint n)) :=
    standardBoundaryRangeHomotopyGroupSubsingleton_ofSphereSubsingleton (q := q) n hSphere
  -- Reduce the standard-pair relative term to the already-collapsed boundary owner.
  exact standardDiskPairRelativeSubsingleton_ofBoundarySubsingleton

/-- Helper for Lemma 9.4.7: the complement of `standardBoundaryRange n` in the standard disk admits
the expected open-ball chart in the ambient Euclidean space. -/
private theorem standardBoundaryRangeComplHomeomorphUnitBall (n : ℕ+) :
    Nonempty
      (((standardBoundaryRange n)ᶜ : Set (unitDisk ((n : ℕ) - 1))) ≃ₜ
        Metric.ball (0 : EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1))) 1) := by
  let E := EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1))
  let preimageBallHomeomorph :
      Metric.ball (0 : E) 1 ≃ₜ
        {x : unitDisk ((n : ℕ) - 1) //
          ((x : E) ∈ Metric.ball (0 : E) 1)} := by
    refine
      { toFun := fun x ↦
          ⟨⟨x.1, by
              -- A point of the open unit ball also lies in the closed unit disk.
              have hxdist : dist x.1 0 < 1 := x.2
              have hx : ‖(x : E)‖ < 1 := by
                simpa [dist_eq_norm] using hxdist
              exact (mem_unitDisk_iff).2 hx.le⟩, x.2⟩
        invFun := fun x ↦ ⟨x.1.1, x.2⟩
        left_inv := ?_
        right_inv := ?_
        continuous_toFun := ?_
        continuous_invFun := ?_ }
    · intro x
      rfl
    · intro x
      cases x
      rfl
    · refine
        Continuous.subtype_mk
          (Continuous.subtype_mk continuous_subtype_val fun x ↦
            (mem_unitDisk_iff).2 <| by
              have hxdist : dist x.1 0 < 1 := x.2
              have hx : ‖(x : E)‖ < 1 := by
                simpa [dist_eq_norm] using hxdist
              exact hx.le)
          (fun x ↦ x.2)
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) fun x ↦ x.2
  have hcompl :
      ((standardBoundaryRange n)ᶜ : Set (unitDisk ((n : ℕ) - 1))) =
        ((↑) ⁻¹' (Metric.ball (0 : E) 1) : Set (unitDisk ((n : ℕ) - 1))) := by
    ext x
    -- Normalize the complement condition to the ambient strict norm inequality.
    rw [mem_standardBoundaryRange_compl_iff_norm_lt_one, Set.mem_preimage]
    constructor
    · intro hx
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    · intro hx
      simpa [Metric.mem_ball, dist_eq_norm] using hx
  -- First rewrite the subtype owner as the preimage of the open unit ball, then forget the closed
  -- disk proof which is automatic there.
  exact ⟨(Homeomorph.setCongr hcompl).trans preimageBallHomeomorph.symm⟩

/-- Helper for Lemma 9.4.7: the standard-side complement owner admits the expected Euclidean chart
by forgetting the open-ball radius constraint through `Homeomorph.unitBall`. -/
private theorem standardBoundaryRangeComplHomeomorphEuclidean (n : ℕ+) :
    Nonempty
      (((standardBoundaryRange n)ᶜ : Set (unitDisk ((n : ℕ) - 1))) ≃ₜ
        EuclideanSpace ℝ (Fin (((n : ℕ) - 1) + 1))) := by
  -- Compose the open-ball identification with the standard Euclidean-to-unit-ball homeomorphism.
  rcases standardBoundaryRangeComplHomeomorphUnitBall n with ⟨e⟩
  exact ⟨e.trans Homeomorph.unitBall.symm⟩

/-- Helper for Lemma 9.4.7: postcomposition by a map of pairs induces the corresponding map on the
relative disk-boundary homotopy quotient. -/
private theorem relativeDiskBoundaryClassMapOfPairMap
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : ℕ+) {A : Set X} {B : Set Y} {a : A} {b : B}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) (hbase : f a.1 = b.1) :
    Nonempty
      (relativeDiskBoundaryPointedHomotopyClass q A a →
        relativeDiskBoundaryPointedHomotopyClass q B b) := by
  refine ⟨Quotient.map ?_ ?_⟩
  · intro g
    refine ⟨f.comp g.1, ?_⟩
    constructor
    · intro u
      -- The boundary condition is preserved because `f` carries `A` into `B`.
      exact hf (relativeDiskBoundaryPointedMap_mapsTo_boundary q A a g u)
    · -- The chosen boundary basepoint is sent to the transported basepoint by construction.
      calc
        (f.comp g.1)
            (sphereBoundaryInclusion ((q : ℕ) - 1)
              (sphereBoundaryBasepoint ((q : ℕ) - 1))) = f a.1 := by
          simp [relativeDiskBoundaryPointedMap_mapsTo_basepoint]
        _ = b.1 := hbase
  · intro g h hgh
    -- Postcompose the witness homotopy and re-check the pair conditions at each time slice.
    refine ⟨{ toHomotopy := by
                simpa using (ContinuousMap.Homotopy.refl f).comp hgh.some.toHomotopy
              prop' := ?_ }⟩
    intro t
    constructor
    · intro u
      exact hf ((hgh.some.prop' t).1 u)
    · calc
        (f.comp ⟨fun x ↦ hgh.some (t, x), hgh.some.continuous_toFun.comp (by fun_prop)⟩)
            (sphereBoundaryInclusion ((q : ℕ) - 1)
              (sphereBoundaryBasepoint ((q : ℕ) - 1))) =
          f a.1 := by
            simpa using congrArg f ((hgh.some.prop' t).2)
        _ = b.1 := hbase

/-- Helper for Lemma 9.4.7: postcomposition by a map of pairs acts on relative disk-boundary
representatives before passing to the quotient. -/
private def relativeDiskBoundaryPointedMapRepOfPairMap
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : ℕ+) {A : Set X} {B : Set Y} {a : A} {b : B}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) (hbase : f a.1 = b.1) :
    relativeDiskBoundaryPointedMap q A a → relativeDiskBoundaryPointedMap q B b
  | g =>
      ⟨f.comp g.1, by
        constructor
        · intro u
          -- The pair-map hypothesis carries the boundary sphere image into the target subspace.
          exact hf (relativeDiskBoundaryPointedMap_mapsTo_boundary q A a g u)
        · -- The chosen boundary basepoint is sent to the transported basepoint.
          calc
            (f.comp g.1)
                (sphereBoundaryInclusion ((q : ℕ) - 1)
                  (sphereBoundaryBasepoint ((q : ℕ) - 1))) = f a.1 := by
              simp [relativeDiskBoundaryPointedMap_mapsTo_basepoint]
            _ = b.1 := hbase⟩

/-- Helper for Lemma 9.4.7: the representative-level pair-map action respects the disk-boundary
homotopy relation. -/
private theorem relativeDiskBoundaryPointedMapRepOfPairMap_respects
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : ℕ+) {A : Set X} {B : Set Y} {a : A} {b : B}
    (f : C(X, Y)) (hf : Set.MapsTo f A B) (hbase : f a.1 = b.1)
    {g h : relativeDiskBoundaryPointedMap q A a}
    (hgh :
      ContinuousMap.HomotopicWith g.1 h.1 (IsRelativeDiskBoundaryPointedTripleMap q A a)) :
    ContinuousMap.HomotopicWith
      (relativeDiskBoundaryPointedMapRepOfPairMap q f hf hbase g).1
      (relativeDiskBoundaryPointedMapRepOfPairMap q f hf hbase h).1
      (IsRelativeDiskBoundaryPointedTripleMap q B b) := by
  -- Postcompose the witness homotopy and re-check the pair conditions stagewise.
  refine ⟨{ toHomotopy := by
              simpa [relativeDiskBoundaryPointedMapRepOfPairMap] using
                (ContinuousMap.Homotopy.refl f).comp hgh.some.toHomotopy
            prop' := ?_ }⟩
  intro t
  constructor
  · intro u
    exact hf ((hgh.some.prop' t).1 u)
  · calc
      (f.comp ⟨fun x ↦ hgh.some (t, x),
          hgh.some.continuous_toFun.comp (by fun_prop)⟩)
          (sphereBoundaryInclusion ((q : ℕ) - 1)
            (sphereBoundaryBasepoint ((q : ℕ) - 1))) =
        f a.1 := by
          simpa using congrArg f ((hgh.some.prop' t).2)
      _ = b.1 := hbase

/-- Helper for Lemma 9.4.7: a homeomorphism of ambient spaces respecting the chosen distinguished
subspaces induces an equivalence on relative disk-boundary homotopy classes. -/
private noncomputable def relativeDiskBoundaryClassEquivOfHomeomorph
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (q : ℕ+) (e : X ≃ₜ Y)
    {A : Set X} {B : Set Y} {a : A} {b : B}
    (he : Set.MapsTo e A B) (he_symm : Set.MapsTo e.symm B A)
    (hbase : e a.1 = b.1) :
    relativeDiskBoundaryPointedHomotopyClass q A a ≃ relativeDiskBoundaryPointedHomotopyClass q B b := by
  let eMap : C(X, Y) := ⟨e, e.continuous_toFun⟩
  let eSymmMap : C(Y, X) := ⟨e.symm, e.symm.continuous_toFun⟩
  have hbase_symm : e.symm b.1 = a.1 := by
    apply e.injective
    calc
      e (e.symm b.1) = b.1 := by simp
      _ = e a.1 := hbase.symm
  refine
    { toFun := Quotient.map
        (relativeDiskBoundaryPointedMapRepOfPairMap q eMap he hbase)
        (fun _ _ hgh ↦
          relativeDiskBoundaryPointedMapRepOfPairMap_respects q eMap he hbase hgh)
      invFun := Quotient.map
        (relativeDiskBoundaryPointedMapRepOfPairMap q eSymmMap he_symm hbase_symm)
        (fun _ _ hgh ↦
          relativeDiskBoundaryPointedMapRepOfPairMap_respects q eSymmMap he_symm hbase_symm hgh)
      left_inv := ?_
      right_inv := ?_ }
  · intro u
    refine Quotient.inductionOn u ?_
    intro g
    apply Quotient.sound
    have hrep :
        relativeDiskBoundaryPointedMapRepOfPairMap q eSymmMap he_symm hbase_symm
            (relativeDiskBoundaryPointedMapRepOfPairMap q eMap he hbase g) = g := by
      apply Subtype.ext
      ext t
      simp [eMap, eSymmMap, relativeDiskBoundaryPointedMapRepOfPairMap]
    -- After canceling `e.symm ∘ e`, the representative is unchanged.
    simpa [hrep] using ContinuousMap.HomotopicWith.refl g.1 g.2
  · intro u
    refine Quotient.inductionOn u ?_
    intro g
    apply Quotient.sound
    have hrep :
        relativeDiskBoundaryPointedMapRepOfPairMap q eMap he hbase
            (relativeDiskBoundaryPointedMapRepOfPairMap q eSymmMap he_symm hbase_symm g) = g := by
      apply Subtype.ext
      ext t
      simp [eMap, eSymmMap, relativeDiskBoundaryPointedMapRepOfPairMap]
    -- The same cancellation works after starting on the target side.
    simpa [hrep] using ContinuousMap.HomotopicWith.refl g.1 g.2

/-- Helper for Lemma 9.4.7: the compactification chart sends the punctured sphere complement to the
finite branch of the one-point compactification. -/
private theorem puncturedSphereCompactificationHomeomorph_infty
    (n : ℕ) (y : (𝕊 n : TopCat.{0})) :
    puncturedSphereCompactificationHomeomorph n y OnePoint.infty = y := by
  let _ : CompactSpace (𝕊 n : TopCat.{0}) := by
    -- `S^n` is the compact disk boundary model used throughout the file.
    change CompactSpace (TopCat.diskBoundary (n + 1))
    infer_instance
  simpa [puncturedSphereCompactificationHomeomorph] using
    (OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty
      (y := y)
      (f := fun z : EuclideanSpace ℝ (Fin n) ↦
        ((spherePuncturedHomeomorphEuclidean n y).symm z).1))

/-- Helper for Lemma 9.4.7: the compactification chart sends the punctured sphere complement to the
finite branch of the one-point compactification. -/
private theorem puncturedSphereCompactificationHomeomorph_symm_mapsTo_compl_infty
    (n : ℕ) (y : (𝕊 n : TopCat.{0})) :
    Set.MapsTo
      (puncturedSphereCompactificationHomeomorph n y).symm
      ({y}ᶜ : Set (𝕊 n))
      ({(OnePoint.infty : OnePoint (EuclideanSpace ℝ (Fin n)))}ᶜ :
        Set (OnePoint (EuclideanSpace ℝ (Fin n)))) := by
  intro x hx
  -- The unique point mapping to `y` is `∞`, so complement points land in the finite branch.
  intro hEq
  have hxeq : x = y := by
    let e := puncturedSphereCompactificationHomeomorph n y
    calc
      x = e (e.symm x) := by simp [e]
      _ = e OnePoint.infty := by simpa [e] using congrArg e hEq
      _ = y := puncturedSphereCompactificationHomeomorph_infty n y
  exact hx <| by simpa [Set.mem_singleton_iff] using hxeq

/-- Helper for Lemma 9.4.7: the punctured reference basepoint has a canonical finite image in the
compactification model. -/
private noncomputable def puncturedCompactificationReferenceBasepoint
    (n : ℕ) (y : (𝕊 n : TopCat.{0})) :
    ({(OnePoint.infty : OnePoint (EuclideanSpace ℝ (Fin n)))}ᶜ :
      Set (OnePoint (EuclideanSpace ℝ (Fin n)))) :=
  ⟨(puncturedSphereCompactificationHomeomorph n y).symm
      (puncturedSphereReferenceBasepoint n y),
    puncturedSphereCompactificationHomeomorph_symm_mapsTo_compl_infty n y
      (puncturedSphereReferenceBasepoint n y).2⟩

/-- Helper for Lemma 9.4.7: the punctured pair is already normalized by the compactification chart
to the common one-point ambient owner. -/
private noncomputable def puncturedPairRelativeDiskBoundaryEquivCompactification
    {q n : ℕ} (y : (𝕊 n : TopCat.{0})) :
    relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat ({y}ᶜ : Set (𝕊 n))
        (puncturedSphereReferenceBasepoint n y) ≃
      relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat
        ({(OnePoint.infty : OnePoint (EuclideanSpace ℝ (Fin n)))}ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin n))))
        (puncturedCompactificationReferenceBasepoint n y) := by
  let e := puncturedSphereCompactificationHomeomorph n y
  -- Normalize the punctured sphere pair to the fixed compactification owner before comparing it
  -- with the standard disk-boundary pair.
  exact
    relativeDiskBoundaryClassEquivOfHomeomorph (q := (q + 1).succPNat) e.symm
      (puncturedSphereCompactificationHomeomorph_symm_mapsTo_compl_infty n y)
      (by
        intro z hz
        change e z ≠ y
        intro hzy
        have hz' : z ≠ OnePoint.infty := by
          simpa using hz
        apply hz'
        apply e.injective
        exact hzy.trans (puncturedSphereCompactificationHomeomorph_infty n y).symm)
      rfl

/-- Helper for Lemma 9.4.7: the standard disk-boundary pair reaches the same compactification
owner used on the punctured side. -/
private noncomputable def standardDiskBoundaryRelativeDiskBoundaryEquivCompactification
    {q n : ℕ} (nPos : ℕ+) (hn : (nPos : ℕ) = n) (y : (𝕊 n : TopCat.{0})) :
    relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat (standardBoundaryRange nPos)
        (standardBoundaryRangeBasepoint nPos) ≃
      relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat
        ({(OnePoint.infty : OnePoint (EuclideanSpace ℝ (Fin n)))}ᶜ :
          Set (OnePoint (EuclideanSpace ℝ (Fin n))))
        (puncturedCompactificationReferenceBasepoint n y) := by
  -- Route correction: the standard-side comparison cannot come from an ambient homeomorphism of
  -- pairs, because `standardBoundaryRangeComplHomeomorphEuclidean` only controls the open-ball
  -- complement. The missing owner is the boundary-collapse/cofiber comparison to the same
  -- compactification model already used on the punctured side.
  -- TODO: build the boundary-collapse quotient owner for `(unitDisk ((n : ℕ) - 1),
  -- standardBoundaryRange nPos)`, identify it with `OnePoint (EuclideanSpace ℝ (Fin n))`,
  -- and descend that comparison to `relativeDiskBoundaryPointedHomotopyClass`.
  sorry

/-- Helper for Lemma 9.4.7: the punctured-sphere pair and the standard disk-boundary pair induce
the same relative disk-boundary homotopy quotient in matching dimension. -/
private noncomputable def puncturedPairRelativeDiskBoundaryEquivStandard
    {q n : ℕ} (nPos : ℕ+) (hn : (nPos : ℕ) = n) (y : (𝕊 n : TopCat.{0})) :
    relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat ({y}ᶜ : Set (𝕊 n))
        (puncturedSphereReferenceBasepoint n y) ≃
      relativeDiskBoundaryPointedHomotopyClass (q + 1).succPNat (standardBoundaryRange nPos)
        (standardBoundaryRangeBasepoint nPos) :=
  -- Route correction: compose through the compactification owner already reached from the
  -- punctured side, and isolate the standard-side boundary-collapse step as the only remaining
  -- geometric bridge.
  (puncturedPairRelativeDiskBoundaryEquivCompactification (q := q) y).trans
    (standardDiskBoundaryRelativeDiskBoundaryEquivCompactification (q := q) nPos hn y).symm

/-- Helper for Lemma 9.4.7: the relative term of the punctured sphere pair at the chosen
reference basepoint compares with the standard disk-boundary pair in the same ambient
dimension. -/
private noncomputable def puncturedPairRelativeEquivStandard
    {q n : ℕ} (nPos : ℕ+) (hn : (nPos : ℕ) = n) (y : (𝕊 n : TopCat.{0})) :
    relativeHomotopyGroup (q + 1).succPNat ({y}ᶜ : Set (𝕊 n))
        (puncturedSphereReferenceBasepoint n y) ≃
      relativeHomotopyGroup (q + 1).succPNat (standardBoundaryRange nPos)
        (standardBoundaryRangeBasepoint nPos) :=
  -- First move both relative groups to the disk-boundary quotient model where the pair
  -- comparison is supposed to live, then insert the explicit quotient-level equivalence.
  (relativeHomotopyGroupEquivRelativeDiskBoundaryClass (q + 1).succPNat ({y}ᶜ : Set (𝕊 n))
      (puncturedSphereReferenceBasepoint n y)).trans
    ((puncturedPairRelativeDiskBoundaryEquivStandard (q := q) nPos hn y).trans
      (relativeHomotopyGroupEquivRelativeDiskBoundaryClass (q + 1).succPNat
        (standardBoundaryRange nPos) (standardBoundaryRangeBasepoint nPos)).symm)

/-- Helper for Lemma 9.4.7: in dimension `n > 1`, the pointed tail relative term of the punctured
sphere pair is trivial. -/
private theorem puncturedPairRelativePiZero_subsingleton
    {n : ℕ} (hn : 1 < n) (y : (𝕊 n : TopCat.{0})) :
    Subsingleton
      (pairRelativePiZeroHomotopyGroup ({y}ᶜ : Set (𝕊 n))
        (puncturedSphereReferenceBasepoint n y)) := by
  let A : Set (𝕊 n) := ({y}ᶜ : Set (𝕊 n))
  let a : A := puncturedSphereReferenceBasepoint n y
  let _ : ContractibleSpace A := spherePuncturedContractible n y
  let _ : Subsingleton (ZerothHomotopy A) := by
    -- Contractibility of the punctured sphere collapses its path-component quotient.
    refine ⟨?_⟩
    intro u v
    refine Quotient.inductionOn₂ u v ?_
    intro u v
    exact Quotient.sound (PathConnectedSpace.joined u v)
  have hn2 : 2 ≤ n := by
    omega
  let _ : Fact (2 ≤ n) := ⟨hn2⟩
  have hAmbientPi1 : Subsingleton (π_ 1 (𝕊 n) a.1) := by
    -- The ambient sphere is simply connected in dimensions `n ≥ 2`, so its `π₁` is trivial.
    let _ : SimplyConnectedSpace (𝕊 n) := sphere_simplyConnectedSpace_of_two_le hn2
    let _ : Subsingleton (FundamentalGroup (𝕊 n) a.1) := by
      change Subsingleton (Path.Homotopic.Quotient a.1 a.1)
      infer_instance
    refine ⟨fun u v ↦ ?_⟩
    apply
      (HomotopyGroup.pi1EquivFundamentalGroup :
        π_ 1 (𝕊 n) a.1 ≃ FundamentalGroup (𝕊 n) a.1).injective
    exact Subsingleton.elim _ _
  have hAmbient :
      Subsingleton (pairAmbientLoopPiZeroHomotopyGroup A a) := by
    -- Translate the ambient loop-space owner to `π₁(S^n)` and use simple connectedness there.
    refine ⟨?_⟩
    intro g h
    apply (loopSpaceHomotopyGroupEquivPiSucc 0 a.1).injective
    exact @Subsingleton.elim _ hAmbientPi1 _ _
  refine ⟨?_⟩
  intro r s
  let a₀ : pairSubspaceLoopPiZeroHomotopyGroup A a := default
  have hBase :
      pairLoopToRelativePiZeroMap A a
          (pairLoopSubspaceInclusionPiZeroMap A a a₀) =
        pairRelativePiZeroBasepoint A a := by
    -- Exactness at the ambient loop owner identifies the image of the inclusion with the kernel
    -- of the relative tail map.
    exact
      (pairHomotopyLongExactSequenceTail_exact_subspace_to_ambient A a
        (pairLoopSubspaceInclusionPiZeroMap A a a₀)).2 ⟨a₀, rfl⟩
  have hrBoundary : pairHomotopyBoundaryZeroMap A a r = ⟦a⟧ := by
    -- The punctured sphere is path connected, so the boundary quotient has only one point.
    exact Subsingleton.elim _ _
  have hsBoundary : pairHomotopyBoundaryZeroMap A a s = ⟦a⟧ := by
    exact Subsingleton.elim _ _
  rcases
      (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative A a r).mp hrBoundary with
    ⟨g, hg⟩
  rcases
      (pairHomotopyLongExactSequenceTail_exact_ambient_to_relative A a s).mp hsBoundary with
    ⟨g', hg'⟩
  have hgBase : g = pairLoopSubspaceInclusionPiZeroMap A a a₀ := by
    exact Subsingleton.elim _ _
  have hg'Base : g' = pairLoopSubspaceInclusionPiZeroMap A a a₀ := by
    exact Subsingleton.elim _ _
  -- Every relative class lifts to the unique ambient loop component, and that component already
  -- maps to the relative basepoint.
  calc
    r = pairLoopToRelativePiZeroMap A a
        (pairLoopSubspaceInclusionPiZeroMap A a a₀) := by
          rw [← hg, hgBase]
    _ = pairRelativePiZeroBasepoint A a := hBase
    _ = pairLoopToRelativePiZeroMap A a
        (pairLoopSubspaceInclusionPiZeroMap A a a₀) := hBase.symm
    _ = s := by
          rw [← hg', hg'Base]

/-- Helper for Lemma 9.4.7: in degrees below `n`, the positive relative homotopy groups of the
punctured sphere pair are trivial. -/
private theorem puncturedPairRelativeSubsingleton_of_lt
    {q n : ℕ} (hqn : q + 2 < n) (y : (𝕊 n : TopCat.{0}))
    (hLower :
      Subsingleton (π_ (q + 1) (𝕊 (n - 1) : TopCat.{0}) (sphereBasepoint (n - 1)))) :
    Subsingleton
      (relativeHomotopyGroup (q + 1).succPNat ({y}ᶜ : Set (𝕊 n))
        (puncturedSphereReferenceBasepoint n y)) := by
  -- Route correction: the higher obstruction only needs the fixed reference basepoint actually
  -- consumed downstream, so the remaining gap is the fixed-basepoint comparison with the standard
  -- disk-boundary pair rather than another arbitrary-basepoint transport layer.
  have hn : 0 < n := by
    omega
  let nPos : ℕ+ := ⟨n, hn⟩
  have hStandard :
      Subsingleton
        (relativeHomotopyGroup (q + 1).succPNat (standardBoundaryRange nPos)
          (standardBoundaryRangeBasepoint nPos)) := by
    -- Collapse the standard disk-boundary pair using the supplied lower-sphere vanishing input.
    simpa [nPos] using
      standardDiskPairRelativeSubsingletonOfSphereSubsingleton (q := q) nPos hLower
  let e := puncturedPairRelativeEquivStandard (q := q) (n := n) nPos rfl y
  -- Transport the already-collapsed standard relative term back across the comparison.
  refine ⟨fun a b ↦ e.injective ?_⟩
  exact Subsingleton.elim (e a) (e b)

/-- Helper for Lemma 9.4.7: for `0 < i < n`, inclusion of the complement of a fixed puncture in
`S^n` is surjective on `π_ i` at the standard basepoint. -/
private theorem puncturedSphereInclusion_surjective_homotopyGroupMap_of_lt_fromLower
    {i n : ℕ} (hi : 0 < i) (h : i < n) (y : (𝕊 n : TopCat.{0})) (hxy : sphereBasepoint n ≠ y)
    (hLower :
      ∀ {q : ℕ}, i = q + 2 →
        Subsingleton (π_ (q + 1) (𝕊 (n - 1) : TopCat.{0}) (sphereBasepoint (n - 1)))) :
    Function.Surjective
      ((puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 n)), 𝕊 n)).eStar i
        ⟨sphereBasepoint n, hxy⟩) := by
  -- Route correction: the main proof now factors through one fixed punctured sphere rather than
  -- constructing a point-avoiding representative for each class separately.
  let xy : ({y}ᶜ : Set (𝕊 n)) := ⟨sphereBasepoint n, hxy⟩
  have hxyRef : puncturedSphereReferenceBasepoint n y = xy := by
    -- The downstream basepoint is exactly the reference one whenever the puncture avoids it.
    simpa [xy] using puncturedSphereReferenceBasepoint_eq_of_ne (n := n) (y := y) hxy
  -- First align the current `eStar` owner with the canonical pair-LES inclusion map.
  rw [puncturedSphereInclusion_eq_pairSubspaceInclusionMap (i := i) y xy]
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi) with ⟨j, rfl⟩
  cases j with
  | zero =>
      -- In degree `1`, exactness of the pointed tail reduces surjectivity to triviality of the
      -- punctured relative tail term.
      let _ :
          Subsingleton
            (pairRelativePiZeroHomotopyGroup ({y}ᶜ : Set (𝕊 n)) xy) :=
        by
          simpa [hxyRef] using puncturedPairRelativePiZero_subsingleton (by simpa using h) y
      have hloop :
          Function.Surjective
            (pairLoopSubspaceInclusionPiZeroMap ({y}ᶜ : Set (𝕊 n)) xy) :=
        pairLoopSubspaceInclusionPiZero_surjective_of_relativePiZeroSubsingleton
          ({y}ᶜ : Set (𝕊 n)) xy
      exact
        pairSubspaceInclusion_surjective_of_loopPiZeroOwnerSurjective
          ({y}ᶜ : Set (𝕊 n)) xy hloop
  | succ q =>
      have hLowerSub :
          Subsingleton (π_ (q + 1) (𝕊 (n - 1) : TopCat.{0}) (sphereBasepoint (n - 1))) :=
        hLower rfl
      -- In higher degrees, consume exactness on the native loop-space owners first, and only then
      -- transfer surjectivity back to the direct inclusion map.
      let _ :
          Subsingleton
            (relativeHomotopyGroup (q + 1).succPNat ({y}ᶜ : Set (𝕊 n)) xy) :=
        by
          simpa [hxyRef] using
            puncturedPairRelativeSubsingleton_of_lt
              (by simpa [Nat.add_assoc] using h) y hLowerSub
      have hloop :
          Function.Surjective
            (pairLoopSubspaceInclusionHomotopyGroupMap ({y}ᶜ : Set (𝕊 n)) xy q) :=
        pairLoopSubspaceInclusion_surjective_of_relativeSubsingleton
          ({y}ᶜ : Set (𝕊 n)) xy q
      exact
        pairSubspaceInclusion_surjective_of_loopOwnerSurjective
          ({y}ᶜ : Set (𝕊 n)) xy q hloop

/-- Helper for Lemma 9.4.7: dimension induction proves the vanishing statement at arbitrary
basepoints once the punctured-pair comparison is available. -/
private theorem sphereHomotopyGroupSubsingletonOfLtAux :
    ∀ n : ℕ, ∀ {i : ℕ}, i < n → ∀ x : (𝕊 n : TopCat.{0}),
      Subsingleton (π_ i (𝕊 n : TopCat.{0}) x)
  | 0, i, h, x => by
      -- There is no sphere of negative dimension to hit, so the inequality `i < 0` is impossible.
      exact False.elim (Nat.not_lt_zero _ h)
  | n + 1, i, h, x => by
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
        let _ : PathConnectedSpace (𝕊 (n + 1) : TopCat.{0}) := sphere_pathConnectedSpace_of_one_le hn1
        let _ : Subsingleton (ZerothHomotopy (𝕊 (n + 1) : TopCat.{0})) := by
          -- Positive-dimensional spheres are path connected, so their path-component quotient is
          -- already trivial.
          refine ⟨fun a b ↦ ?_⟩
          refine Quotient.inductionOn₂ a b ?_
          intro a b
          exact Quotient.sound (PathConnectedSpace.joined a b)
        -- For `π₀`, path connectedness is already the whole argument.
        refine ⟨fun a b ↦ ?_⟩
        apply
          (HomotopyGroup.pi0EquivZerothHomotopy :
            π_ 0 (𝕊 (n + 1) : TopCat.{0}) x ≃ ZerothHomotopy (𝕊 (n + 1) : TopCat.{0})).injective
        exact Subsingleton.elim _ _
      · have hn0 : 0 < n + 1 := Nat.succ_pos n
        have hn1 : 1 ≤ n + 1 := Nat.succ_le_of_lt hn0
        let _ : PathConnectedSpace (𝕊 (n + 1) : TopCat.{0}) := sphere_pathConnectedSpace_of_one_le hn1
        let β : Path x (sphereBasepoint (n + 1) : (𝕊 (n + 1) : TopCat.{0})) :=
          PathConnectedSpace.somePath x (sphereBasepoint (n + 1))
        let e : π_ i (𝕊 (n + 1) : TopCat.{0}) x ≃
            π_ i (𝕊 (n + 1) : TopCat.{0}) (sphereBasepoint (n + 1) : (𝕊 (n + 1) : TopCat.{0})) :=
          sphereHomotopyGroupBasepointChangeEquiv β
        have hStd :
            Subsingleton
              (π_ i (𝕊 (n + 1) : TopCat.{0})
                (sphereBasepoint (n + 1) : (𝕊 (n + 1) : TopCat.{0}))) := by
          refine ⟨?_⟩
          intro a b
          let y : 𝕊 (n + 1) := oppositeSphereBasepoint (n + 1)
          have hxy : sphereBasepoint (n + 1) ≠ y :=
            sphereBasepoint_ne_oppositeSphereBasepoint (n + 1)
          let xy : ({y}ᶜ : Set (𝕊 (n + 1))) := ⟨sphereBasepoint (n + 1), hxy⟩
          let _ : ContractibleSpace ({y}ᶜ : Set (𝕊 (n + 1))) :=
            spherePuncturedContractible (n + 1) y
          let _ : Subsingleton (π_ i ({y}ᶜ : Set (𝕊 (n + 1))) xy) :=
            homotopyGroup_subsingleton_of_contractible i xy
          let constClass :
              π_ i (𝕊 (n + 1) : TopCat.{0})
                (sphereBasepoint (n + 1) : (𝕊 (n + 1) : TopCat.{0})) :=
            ⟦(GenLoop.const :
              Ω^ (Fin i) (𝕊 (n + 1) : TopCat.{0})
                (sphereBasepoint (n + 1) : (𝕊 (n + 1) : TopCat.{0})))⟧
          have hLower :
              ∀ {q : ℕ}, i = q + 2 →
                Subsingleton (π_ (q + 1) (𝕊 n : TopCat.{0}) (sphereBasepoint n)) := by
            intro q hq
            subst hq
            -- This is the unique lower-dimensional vanishing input needed in the higher-degree
            -- punctured-pair comparison.
            simpa using sphereHomotopyGroupSubsingletonOfLtAux n
              (i := q + 1) (by omega) (sphereBasepoint n : (𝕊 n : TopCat.{0}))
          have ha : a = constClass := by
            rcases puncturedSphereInclusion_surjective_homotopyGroupMap_of_lt_fromLower
                hi h y hxy hLower a with ⟨a', ha'⟩
            have hLift :
                (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    a' =
                  (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 (n + 1))) xy)⟧) := by
              -- The contractible punctured sphere has only the constant class.
              exact congrArg
                ((puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy)
                (Subsingleton.elim _ _)
            have hConst :
                (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 (n + 1))) xy)⟧) =
                  constClass := by
              -- Mapping the punctured constant class back to `S^(n + 1)` recovers the ambient
              -- constant class.
              simpa [constClass, xy] using puncturedSphereInclusion_constClass hxy
            -- Lift the class to the contractible punctured sphere, then compare with the
            -- punctured constant class before returning to the ambient sphere.
            exact ha'.symm.trans (hLift.trans hConst)
          have hb : b = constClass := by
            rcases puncturedSphereInclusion_surjective_homotopyGroupMap_of_lt_fromLower
                hi h y hxy hLower b with ⟨b', hb'⟩
            have hLift :
                (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    b' =
                  (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 (n + 1))) xy)⟧) := by
              -- The same contractibility argument identifies every lifted class with the
              -- punctured constant class.
              exact congrArg
                ((puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy)
                (Subsingleton.elim _ _)
            have hConst :
                (puncturedSphereInclusion : C(({y}ᶜ : Set (𝕊 (n + 1))), 𝕊 (n + 1))).eStar i xy
                    (⟦(GenLoop.const : Ω^ (Fin i) ({y}ᶜ : Set (𝕊 (n + 1))) xy)⟧) =
                  constClass := by
              -- The punctured constant class still maps to the same ambient constant class.
              simpa [constClass, xy] using puncturedSphereInclusion_constClass hxy
            -- The same contractible lift kills any other class as well.
            exact hb'.symm.trans (hLift.trans hConst)
          exact ha.trans hb.symm
        -- Move to the standard basepoint, apply the standard-basepoint collapse there, and pull
        -- the result back across the basepoint-change equivalence.
        refine ⟨fun a b ↦ e.injective ?_⟩
        exact Subsingleton.elim (e a) (e b)

/-- Helper for Lemma 9.4.7: for `0 < i < n`, the standard-basepoint homotopy group `π_ i(S^n)` is
subsingleton. -/
private theorem standardSphereHomotopyGroupSubsingletonOfLtPositive {i n : ℕ} (_hi : 0 < i)
    (h : i < n) :
    Subsingleton (π_ i (𝕊 n : TopCat.{0}) (sphereBasepoint n : (𝕊 n : TopCat.{0}))) := by
  -- Specialize the dimension-induction theorem to the standard sphere basepoint.
  simpa using sphereHomotopyGroupSubsingletonOfLtAux n h
    (sphereBasepoint n : (𝕊 n : TopCat.{0}))

/-- Lemma 9.4.7: if `i < n`, then the `i`th homotopy group of `S^n` is trivial. -/
instance sphereHomotopyGroupSubsingletonOfLt {i n : ℕ} (h : i < n)
    (x : (𝕊 n : TopCat.{0})) :
    Subsingleton (π_ i (𝕊 n : TopCat.{0}) x) := by
  -- Delegate the arbitrary-basepoint case to the dimension-induction theorem.
  simpa using sphereHomotopyGroupSubsingletonOfLtAux n h x
