import Mathlib.Topology.Homotopy.HSpaces
import Mathlib.Topology.Subpath
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap01.Definition_1_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1

open CategoryTheory
open scoped Topology Topology.Homotopy unitInterval

noncomputable section

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch` surfaced only unrelated model-category fibrations. The
-- verified local owners are Chapter 8's `actualFiberSet`/`actualFiberBasepoint`/`IsBasedFibration`,
-- Chapter 9's `relativeHomotopyGroup`, and the loop-space owner `Ω B.right (underTopBasepoint B)`.

/-
The projected path of a point in the modeled pair `(E, F)` starts at the basepoint of `B`.
-/
private theorem actualFiberInclusionHomotopyFiberToLoopFun_source {E B : BasedSpace} (p : E ⟶ B)
    (z : inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)) :
    (ContinuousMap.comp p.right.hom z.path.toContinuousMap) 0 = underTopBasepoint B := by
  -- Evaluating at `0` reads the source of `z.path`, namely `actualFiberBasepoint p`.
  calc
    (ContinuousMap.comp p.right.hom z.path.toContinuousMap) 0
        = p.right.hom ((actualFiberBasepoint p).1) := by
            simpa [ContinuousMap.comp] using congrArg p.right.hom z.path.source'
    _ = underTopBasepoint B := actualFiberBasepoint_property p

/-
The projected path of a point in the modeled pair `(E, F)` ends again at the basepoint of `B`.
-/
private theorem actualFiberInclusionHomotopyFiberToLoopFun_target {E B : BasedSpace} (p : E ⟶ B)
    (z : inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)) :
    (ContinuousMap.comp p.right.hom z.path.toContinuousMap) 1 = underTopBasepoint B := by
  -- Evaluating at `1` reads the fiber endpoint `z.endpoint`, whose image is the basepoint of `B`.
  calc
    (ContinuousMap.comp p.right.hom z.path.toContinuousMap) 1
        = p.right.hom z.endpoint.1 := by
            simpa [ContinuousMap.comp] using congrArg p.right.hom z.path.target'
    _ = underTopBasepoint B := z.endpoint.2

/-- Helper for Theorem 9.3.3: loop reversal is continuous on `Ω B`. -/
private theorem loopReverseContinuous (B : BasedSpace) :
    Continuous fun χ : Ω B.right (underTopBasepoint B) ↦ χ.symm := by
  -- Forget the loop-space endpoint conditions; reversal is precomposition by `unitInterval.symm`.
  rw [continuous_induced_rng]
  simpa using
    (ContinuousMap.continuous_precomp
      (⟨unitInterval.symm, unitInterval.continuous_symm⟩ : C(I, I))).comp
      (continuous_induced_dom :
        Continuous fun χ : Ω B.right (underTopBasepoint B) ↦ χ.toContinuousMap)

/-- Helper for Theorem 9.3.3: loop reversal on `Ω B` as a bundled continuous map. -/
private def loopReverseContinuousMap (B : BasedSpace) :
    C(Ω B.right (underTopBasepoint B), Ω B.right (underTopBasepoint B)) :=
  { toFun := fun χ ↦ χ.symm
    continuous_toFun := loopReverseContinuous B }

/-- The inclusion-homotopy-fiber model of `(E, F)` maps to the based loop space of `B` by
projecting the ambient path along `p`. -/
def actualFiberInclusionHomotopyFiberToLoopFun {E B : BasedSpace} (p : E ⟶ B) :
    inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p) →
      Ω B.right (underTopBasepoint B)
  | z =>
      Path.mk (ContinuousMap.comp p.right.hom z.path.toContinuousMap)
        (actualFiberInclusionHomotopyFiberToLoopFun_source p z)
        (actualFiberInclusionHomotopyFiberToLoopFun_target p z)

/-- The loop-valued map on the inclusion-homotopy-fiber model is continuous. -/
theorem continuous_actualFiberInclusionHomotopyFiberToLoopFun {E B : BasedSpace} (p : E ⟶ B) :
    Continuous (actualFiberInclusionHomotopyFiberToLoopFun p) := by
  -- Forgetting the endpoint equations, the map is just postcomposition of the path coordinate by
  -- `p.right.hom`.
  have hproj :
      Continuous fun z : inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p) ↦
        ContinuousMap.comp p.right.hom z.1.2 := by
    exact
      (ContinuousMap.continuous_postcomp p.right.hom).comp
        (continuous_snd.comp continuous_subtype_val)
  -- The loop space inherits the induced topology from the underlying continuous-map space.
  refine continuous_induced_rng.2 ?_
  change Continuous fun z : inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p) ↦
    ((actualFiberInclusionHomotopyFiberToLoopFun p z : Ω B.right (underTopBasepoint B)) :
      C(I, B.right))
  simpa [actualFiberInclusionHomotopyFiberToLoopFun, inclusionHomotopyFiber.path] using hproj

/-- The path-space model of the induced map `π_n(E, F) → π_n(B)` landing in the based loop space
owner for `π_n(B)`. -/
def actualFiberInclusionHomotopyFiberToLoop {E B : BasedSpace} (p : E ⟶ B) :
    C(inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p),
      Ω B.right (underTopBasepoint B)) :=
  { toFun := actualFiberInclusionHomotopyFiberToLoopFun p
    continuous_toFun := continuous_actualFiberInclusionHomotopyFiberToLoopFun p }

/-- The relative path-space model of `(E, F)` maps to the based loop space of `B` by projecting
paths in `E` along the fibration map `p`. -/
def actualFiberRelativeToLoopMap {E B : BasedSpace} (p : E ⟶ B) :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
      Ω B.right (underTopBasepoint B)) :=
  (actualFiberInclusionHomotopyFiberToLoop p).comp
    { toFun := pathToSetToInclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
      continuous_toFun :=
        (pathToSetToInclusionHomotopyFiber_isEmbedding
          (actualFiberSet p) (actualFiberBasepoint p)).continuous }

/-- The relative path-space comparison sends the constant path at `actualFiberBasepoint p` to the
constant loop at `underTopBasepoint B`. -/
@[simp] theorem actualFiberRelativeToLoopMap_refl {E B : BasedSpace} (p : E ⟶ B) :
    actualFiberRelativeToLoopMap p (PathToSet.refl (actualFiberBasepoint p)) =
      Path.refl (underTopBasepoint B) := by
  apply Path.ext
  ext t
  simpa only [actualFiberRelativeToLoopMap, actualFiberInclusionHomotopyFiberToLoop,
    actualFiberInclusionHomotopyFiberToLoopFun, PathToSet.refl,
    pathToSetToInclusionHomotopyFiber, inclusionHomotopyFiber.mk]
    using fundamentalGroupFunctorMap_basepoint p

/-- Helper for Theorem 9.3.3: a based loop in `B` determines the canonical point of
`HomotopyFiber p` obtained by pairing `underTopBasepoint E` with the reversed loop. -/
private theorem loopToActualFiberHomotopyFiberPoint_condition {E B : BasedSpace} (p : E ⟶ B)
    (χ : Ω B.right (underTopBasepoint B)) :
    p.right.hom (underTopBasepoint E) = (PathSpace.ofPath χ.symm).endpoint := by
  -- The reversed loop still ends at the distinguished basepoint of `B`.
  simpa using homotopyFiberLoopInclusion_condition p χ.symm

/-- Helper for Theorem 9.3.3: the canonical homotopy-fiber point attached to a loop in `B`. -/
private def loopToActualFiberHomotopyFiberPoint {E B : BasedSpace} (p : E ⟶ B)
    (χ : Ω B.right (underTopBasepoint B)) :
    HomotopyFiber p :=
  HomotopyFiber.mk (underTopBasepoint E) (PathSpace.ofPath χ.symm)
    (loopToActualFiberHomotopyFiberPoint_condition p χ)

/-- Helper for Theorem 9.3.3: the terminal stage of the lifted contraction of the loop point lands
in the actual fiber of `p`. -/
private theorem loopToActualFiberEndpoint_mem_actualFiberSet {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    p.right.hom ((homotopyFiberLiftTerminal p).right.hom
      (loopToActualFiberHomotopyFiberPoint p χ)) = underTopBasepoint B := by
  -- The Chapter 8 terminal-stage theorem applies directly to the chosen loop point.
  exact homotopyFiberLiftTerminal_mem_actualFiberSet p (loopToActualFiberHomotopyFiberPoint p χ)

/-- Helper for Theorem 9.3.3: the loop lift ends at a point of the actual fiber. -/
private def loopToActualFiberEndpoint {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p]
    (χ : Ω B.right (underTopBasepoint B)) :
    actualFiberSet p :=
  ⟨(homotopyFiberLiftTerminal p).right.hom (loopToActualFiberHomotopyFiberPoint p χ),
    loopToActualFiberEndpoint_mem_actualFiberSet p χ⟩

/-- Helper for Theorem 9.3.3: the lifted contraction path varies continuously in the time
parameter for a fixed loop. -/
private theorem loopToActualFiberPath_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    Continuous fun t : I ↦
      (homotopyFiberContractionLift p).toContinuousMap
        (t, loopToActualFiberHomotopyFiberPoint p χ) := by
  -- Freeze the homotopy-fiber point and compose the chosen lift with the constant pairing map.
  have hpair : Continuous fun t : I ↦ (t, loopToActualFiberHomotopyFiberPoint p χ) := by
    exact continuous_id.prodMk continuous_const
  exact (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair

/-- Helper for Theorem 9.3.3: the lifted contraction path starts at `underTopBasepoint E`. -/
private theorem loopToActualFiberPath_source {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    (homotopyFiberContractionLift p).toContinuousMap
        (0, loopToActualFiberHomotopyFiberPoint p χ) = underTopBasepoint E := by
  -- At time `0`, the lift agrees with `homotopyFiberProjection p`.
  calc
    (homotopyFiberContractionLift p).toContinuousMap
        (0, loopToActualFiberHomotopyFiberPoint p χ)
        = (homotopyFiberPointProjection p).right.hom
            (loopToActualFiberHomotopyFiberPoint p χ) := by
            simpa using (homotopyFiberContractionLift p).map_zero_left
              (loopToActualFiberHomotopyFiberPoint p χ)
    _ = underTopBasepoint E := by
          rfl

/-- Helper for Theorem 9.3.3: the lifted contraction path ends at the chosen actual-fiber
endpoint. -/
private theorem loopToActualFiberPath_target {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    (homotopyFiberContractionLift p).toContinuousMap
        (1, loopToActualFiberHomotopyFiberPoint p χ) =
      (loopToActualFiberEndpoint p χ).1 := by
  -- At time `1`, the lift reaches the terminal point used to define the endpoint.
  simpa [loopToActualFiberEndpoint] using (homotopyFiberContractionLift p).map_one_left
    (loopToActualFiberHomotopyFiberPoint p χ)

/-- Helper for Theorem 9.3.3: the chosen lift of a loop in `B` as a path in `E` ending in the
actual fiber. -/
private def loopToActualFiberPath {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p]
    (χ : Ω B.right (underTopBasepoint B)) :
    Path (underTopBasepoint E) (loopToActualFiberEndpoint p χ).1 :=
  Path.mk
    ⟨fun t ↦
        (homotopyFiberContractionLift p).toContinuousMap
          (t, loopToActualFiberHomotopyFiberPoint p χ),
      loopToActualFiberPath_continuous p χ⟩
    (loopToActualFiberPath_source p χ)
    (loopToActualFiberPath_target p χ)

/-- Helper for Theorem 9.3.3: lifting a based loop in `B` produces a point of the modeled
inclusion homotopy fiber of the actual fiber of `p`. -/
def loopToActualFiberInclusionHomotopyFiber {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Ω B.right (underTopBasepoint B) →
      inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
  | χ => inclusionHomotopyFiber.mk (loopToActualFiberEndpoint p χ) (loopToActualFiberPath p χ)

/-- Helper for Theorem 9.3.3: projecting the chosen lifted loop recovers the original loop
strictly. -/
theorem actualFiberInclusionHomotopyFiberToLoop_rightInverse {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    actualFiberInclusionHomotopyFiberToLoopFun p
        (loopToActualFiberInclusionHomotopyFiber p χ) = χ := by
  -- Evaluate the projected lift pointwise and compare it with the contracted reversed loop.
  apply Path.ext
  ext t
  have hcomm :=
    congrArg
      (fun k : C(I × (homotopyFiber p).right, B.right) ↦
        k (t, loopToActualFiberHomotopyFiberPoint p χ))
      (homotopyFiberContractionLift_comm p)
  calc
    p.right.hom ((homotopyFiberContractionLift p).toContinuousMap
        (t, loopToActualFiberHomotopyFiberPoint p χ))
        = (homotopyFiberPathContraction_liftInput p).toContinuousMap
            (t, loopToActualFiberHomotopyFiberPoint p χ) := by
              simpa using hcomm
    _ = (loopToActualFiberHomotopyFiberPoint p χ).path (oneSub t) := by
          simpa using homotopyFiberPathContraction_liftInput_apply p t
            (loopToActualFiberHomotopyFiberPoint p χ)
    _ = χ t := by
          change χ.symm (oneSub t) = χ t
          change χ (σ (oneSub t)) = χ t
          have hσ : σ (oneSub t) = t := by
            apply Subtype.ext
            simp [oneSub]
          exact congrArg χ hσ

/-- Helper for Theorem 9.3.3: the pointwise loop-lift construction is the homotopy-fiber loop
inclusion applied to the reversed loop. -/
private theorem loopToActualFiberHomotopyFiberPoint_eq {E B : BasedSpace} (p : E ⟶ B)
    (χ : Ω B.right (underTopBasepoint B)) :
    loopToActualFiberHomotopyFiberPoint p χ =
      (homotopyFiberLoopInclusion p).right.hom ((loopReverseContinuousMap B) χ) := by
  -- Both constructions are the same homotopy-fiber point written through the loop-reversal map.
  rfl

/-- Helper for Theorem 9.3.3: the loop-lift homotopy-fiber point varies continuously with the
input loop. -/
private def loopToActualFiberHomotopyFiberPointMap {E B : BasedSpace} (p : E ⟶ B) :
    C(Ω B.right (underTopBasepoint B), HomotopyFiber p) :=
  (homotopyFiberLoopInclusionContinuousMap p).comp (loopReverseContinuousMap B)

/-- Helper for Theorem 9.3.3: evaluating the continuous loop-to-homotopy-fiber map recovers the
pointwise loop-lift construction. -/
@[simp] private theorem loopToActualFiberHomotopyFiberPointMap_apply {E B : BasedSpace} (p : E ⟶ B)
    (χ : Ω B.right (underTopBasepoint B)) :
    loopToActualFiberHomotopyFiberPointMap p χ = loopToActualFiberHomotopyFiberPoint p χ := by
  -- Unfold the composition and use the identification with the reversed-loop inclusion.
  rw [loopToActualFiberHomotopyFiberPoint_eq]
  rfl

/-- Helper for Theorem 9.3.3: the lifted loop endpoint defines a continuous map into the actual
fiber. -/
private def loopToActualFiberEndpointMap {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p] :
    C(Ω B.right (underTopBasepoint B), actualFiberSet p) :=
  ((homotopyFiberToActualFiber p).right.hom).comp (loopToActualFiberHomotopyFiberPointMap p)

/-- Helper for Theorem 9.3.3: evaluating the endpoint map recovers the pointwise lifted endpoint.
-/
@[simp] private theorem loopToActualFiberEndpointMap_apply {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    loopToActualFiberEndpointMap p χ = loopToActualFiberEndpoint p χ := by
  -- The endpoint map is exactly `homotopyFiberToActualFiber` applied to the lifted loop point.
  change (homotopyFiberToActualFiber p).right.hom (loopToActualFiberHomotopyFiberPointMap p χ) =
    loopToActualFiberEndpoint p χ
  rw [loopToActualFiberHomotopyFiberPointMap_apply]
  rfl

/-- Helper for Theorem 9.3.3: the two-parameter lifted-contraction family is continuous. -/
private theorem loopToActualFiberLiftFamily_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun q : Ω B.right (underTopBasepoint B) × I ↦
      (homotopyFiberContractionLift p).toContinuousMap
        (q.2, loopToActualFiberHomotopyFiberPointMap p q.1) := by
  -- Compose the chosen contraction lift with the continuously varying loop-lift point.
  have hpair :
      Continuous fun q : Ω B.right (underTopBasepoint B) × I ↦
        (q.2, loopToActualFiberHomotopyFiberPointMap p q.1) := by
    exact continuous_snd.prodMk
      ((loopToActualFiberHomotopyFiberPointMap p).continuous.comp continuous_fst)
  exact (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair

/-- Helper for Theorem 9.3.3: the chosen lifted contraction, viewed as a two-parameter family on
loops and time. -/
private def loopToActualFiberLiftFamily {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p] :
    C(Ω B.right (underTopBasepoint B) × I, E.right) :=
  { toFun := fun q ↦
      (homotopyFiberContractionLift p).toContinuousMap
        (q.2, loopToActualFiberHomotopyFiberPointMap p q.1)
    continuous_toFun := loopToActualFiberLiftFamily_continuous p }

/-- Helper for Theorem 9.3.3: currying the lifted contraction gives the path family underlying the
reverse map from loops to the relative path-space model. -/
private def loopToActualFiberPathMap {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p] :
    C(Ω B.right (underTopBasepoint B), C(I, E.right)) :=
  ContinuousMap.curry (loopToActualFiberLiftFamily p)

/-- Helper for Theorem 9.3.3: the curried lifted-contraction family evaluates by the expected
pointwise formula. -/
@[simp] private theorem loopToActualFiberPathMap_apply {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) (t : I) :
    loopToActualFiberPathMap p χ t =
      (homotopyFiberContractionLift p).toContinuousMap
        (t, loopToActualFiberHomotopyFiberPoint p χ) := by
  -- Expand the curry construction and rewrite the lifted loop point through the bundled map.
  simp [loopToActualFiberPathMap, loopToActualFiberLiftFamily]

/-- Helper for Theorem 9.3.3: loop lifting is continuous into the modeled inclusion homotopy
fiber. -/
private theorem continuous_loopToActualFiberInclusionHomotopyFiber {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous (loopToActualFiberInclusionHomotopyFiber p) := by
  -- Package the continuous endpoint and path coordinates into the subtype model.
  have hpair :
      Continuous fun χ : Ω B.right (underTopBasepoint B) ↦
        (loopToActualFiberEndpointMap p χ, loopToActualFiberPathMap p χ) := by
    exact (loopToActualFiberEndpointMap p).continuous.prodMk (loopToActualFiberPathMap p).continuous
  have hsub :
      Continuous fun χ : Ω B.right (underTopBasepoint B) ↦
        (⟨(loopToActualFiberEndpointMap p χ, loopToActualFiberPathMap p χ), by
          constructor
          · -- The lifted path still starts at the chosen basepoint of `E`.
            change loopToActualFiberPathMap p χ 0 = (actualFiberBasepoint p).1
            simpa using loopToActualFiberPath_source p χ
          · -- The terminal value of the lifted path is the endpoint chosen in the actual fiber.
            change loopToActualFiberPathMap p χ 1 = (loopToActualFiberEndpointMap p χ).1
            simpa using loopToActualFiberPath_target p χ⟩ :
          inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)) := by
    exact hpair.subtype_mk fun χ ↦ by
      constructor
      · change loopToActualFiberPathMap p χ 0 = (actualFiberBasepoint p).1
        simpa using loopToActualFiberPath_source p χ
      · change loopToActualFiberPathMap p χ 1 = (loopToActualFiberEndpointMap p χ).1
        simpa using loopToActualFiberPath_target p χ
  -- Unfold both models to compare the packaged subtype map with `loopToActualFiberPath`.
  simpa [loopToActualFiberInclusionHomotopyFiber, inclusionHomotopyFiber.mk, loopToActualFiberPath,
    loopToActualFiberEndpointMap_apply, loopToActualFiberPathMap, loopToActualFiberLiftFamily]
    using hsub

/-- Helper for Theorem 9.3.3: the continuous reverse loop-lift as a map into the modeled
inclusion homotopy fiber. -/
def loopToActualFiberInclusionHomotopyFiberMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(Ω B.right (underTopBasepoint B),
      inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)) :=
  { toFun := loopToActualFiberInclusionHomotopyFiber p
    continuous_toFun := continuous_loopToActualFiberInclusionHomotopyFiber p }

/-- Helper for Theorem 9.3.3: the loop-lift map is continuous on the relative path-space model.
-/
private theorem continuous_loopToActualFiberRelativeMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun χ : Ω B.right (underTopBasepoint B) ↦
      inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p)
        (loopToActualFiberInclusionHomotopyFiber p χ) := by
  -- Compose the modeled loop-lift map with the canonical homeomorphism to `PathToSet`.
  exact
    (inclusionHomotopyFiberHomeomorphPathToSet
      (actualFiberSet p) (actualFiberBasepoint p)).continuous_toFun.comp
      (loopToActualFiberInclusionHomotopyFiberMap p).continuous

/-- Helper for Theorem 9.3.3: the reverse map on the Chapter 9 path-space model of the relative
homotopy group. -/
def loopToActualFiberRelativeMap {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p] :
    C(Ω B.right (underTopBasepoint B),
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  { toFun := fun χ ↦
      inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p)
        (loopToActualFiberInclusionHomotopyFiber p χ)
    continuous_toFun := continuous_loopToActualFiberRelativeMap p }

/-- Helper for Theorem 9.3.3: `actualFiberRelativeToLoopMap p` composed with the reverse
path-space map is strictly the identity on the loop space. -/
theorem actualFiberRelativeToLoopMap_rightInverse {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Function.RightInverse (loopToActualFiberRelativeMap p) (actualFiberRelativeToLoopMap p) := by
  intro χ
  -- Move to the inclusion-homotopy-fiber model, where the strict right inverse is already known.
  change actualFiberInclusionHomotopyFiberToLoop p
      (pathToSetToInclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
        (loopToActualFiberRelativeMap p χ)) = χ
  rw [show loopToActualFiberRelativeMap p χ =
      (inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p))
        (loopToActualFiberInclusionHomotopyFiber p χ) by
        rfl]
  rw [inclusionHomotopyFiberHomeomorphPathToSet_apply]
  simpa [actualFiberRelativeToLoopMap] using
    actualFiberInclusionHomotopyFiberToLoop_rightInverse p χ

/-- Helper for Theorem 9.3.3: the reverse path-space map sends the constant loop to the constant
relative-path basepoint. -/
@[simp] theorem loopToActualFiberRelativeMap_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    loopToActualFiberRelativeMap p (Path.refl (underTopBasepoint B)) =
      PathToSet.refl (actualFiberBasepoint p) := by
  -- Identify the constant loop with the constant point of the modeled inclusion homotopy fiber.
  have hpoint :
      loopToActualFiberHomotopyFiberPoint p (Path.refl (underTopBasepoint B)) =
        underTopBasepoint (homotopyFiber p) := by
    calc
      loopToActualFiberHomotopyFiberPoint p (Path.refl (underTopBasepoint B))
          = (homotopyFiberLoopInclusion p).right.hom
              ((loopReverseContinuousMap B) (Path.refl (underTopBasepoint B))) := by
                exact loopToActualFiberHomotopyFiberPoint_eq p (Path.refl (underTopBasepoint B))
      _ = (homotopyFiberLoopInclusion p).right.hom (Path.refl (underTopBasepoint B)) := by
            rfl
      _ = underTopBasepoint (homotopyFiber p) := by
            simpa using basedMapUnderTopBasepoint (homotopyFiberLoopInclusion p)
  have hendpoint :
      loopToActualFiberEndpoint p (Path.refl (underTopBasepoint B)) = actualFiberBasepoint p := by
    have hbase :
        (homotopyFiberToActualFiber p).right.hom (underTopBasepoint (homotopyFiber p)) =
          actualFiberBasepoint p := by
      simpa [homotopyFiberToActualFiber] using homotopyFiberToActualFiberFun_basepoint p
    rw [show loopToActualFiberEndpoint p (Path.refl (underTopBasepoint B)) =
        (homotopyFiberToActualFiber p).right.hom
          (loopToActualFiberHomotopyFiberPoint p (Path.refl (underTopBasepoint B))) by
          rfl]
    rw [hpoint]
    exact hbase
  have hmodel :
      loopToActualFiberInclusionHomotopyFiber p (Path.refl (underTopBasepoint B)) =
        inclusionHomotopyFiber.mk (actualFiberBasepoint p) (Path.refl (underTopBasepoint E)) := by
    -- Compare the endpoint/path pair in the concrete modeled homotopy fiber.
    apply Subtype.ext
    change
      ((loopToActualFiberEndpoint p (Path.refl (underTopBasepoint B))),
          (loopToActualFiberPath p (Path.refl (underTopBasepoint B))).toContinuousMap) =
        ((actualFiberBasepoint p), (Path.refl (underTopBasepoint E)).toContinuousMap)
    refine Prod.ext hendpoint ?_
    ext t
    have hmem :
        loopToActualFiberHomotopyFiberPoint p (Path.refl (underTopBasepoint B)) ∈
          basedBasepointSet (homotopyFiber p) := by
      simpa [basedBasepointSet, hpoint]
    have hstage :
        (homotopyFiberContractionLift p).toContinuousMap
          (t, loopToActualFiberHomotopyFiberPoint p (Path.refl (underTopBasepoint B))) =
          underTopBasepoint E := by
      simpa [hpoint, homotopyFiberPointProjectionHom_apply, underTopBasepoint_homotopyFiber] using
        (homotopyFiberContractionLift p).eq_fst t hmem
    simpa [loopToActualFiberPath, hstage]
  -- Push the modeled-basepoint computation through the Chapter 9 homeomorphism.
  rw [show loopToActualFiberRelativeMap p (Path.refl (underTopBasepoint B)) =
      (inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p))
        (loopToActualFiberInclusionHomotopyFiber p (Path.refl (underTopBasepoint B))) by
        rfl]
  rw [inclusionHomotopyFiberHomeomorphPathToSet_apply, hmodel]
  rfl

/-- Helper for Theorem 9.3.3: the shifted induced map on homotopy groups with an explicit target
basepoint equality. -/
private def homotopyGroupMapOverEq
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (hf : f a = b) (q : ℕ) :
    π_ q A a → π_ q B b :=
  cast
    (congrArg (fun y ↦ π_ q A a → π_ q B y) hf)
    (homotopyGroupMap f q a)

/-- Helper for Theorem 9.3.3: changing only the proof of the target-basepoint equality does not
change the transported homotopy-group map. -/
private theorem homotopyGroupMapOverEq_proofIrrel
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : C(A, B)) {a : A} {b : B} (h₁ h₂ : f a = b) (q : ℕ) :
    homotopyGroupMapOverEq f h₁ q = homotopyGroupMapOverEq f h₂ q := by
  -- The codomain transport only depends on a proposition-valued equality witness.
  cases h₁
  cases h₂
  rfl

/-- Helper for Theorem 9.3.3: equal continuous maps induce equal transported homotopy-group maps.
-/
private theorem homotopyGroupMapOverEq_congr
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (hfg : f = g) {a : A} {b : B} (hf : f a = b) (hg : g a = b) (q : ℕ) :
    homotopyGroupMapOverEq f hf q = homotopyGroupMapOverEq g hg q := by
  -- After identifying the maps, only proof irrelevance remains.
  subst hfg
  exact homotopyGroupMapOverEq_proofIrrel f hf hg q

/-- Helper for Theorem 9.3.3: postcomposition on homotopy groups respects composition. -/
private theorem homotopyGroupMap_comp
    {A : Type*} {B : Type*} {C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C)) (q : ℕ) (a : A) :
    homotopyGroupMap (g.comp f) q a =
      (homotopyGroupMap g q (f a)) ∘ homotopyGroupMap f q a := by
  -- On quotient representatives, both sides are literally postcomposition by `g.comp f`.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rfl

/-- Helper for Theorem 9.3.3: transporting across composition agrees with composing the
transported homotopy-group maps. -/
private theorem homotopyGroupMapOverEq_comp
    {A : Type*} {B : Type*} {C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : C(A, B)) (g : C(B, C))
    {a : A} {b : B} {c : C} (hf : f a = b) (hg : g b = c) (q : ℕ) :
    (homotopyGroupMapOverEq g hg q) ∘ (homotopyGroupMapOverEq f hf q) =
      homotopyGroupMapOverEq (g.comp f)
        (by simpa [ContinuousMap.comp_apply, hf] using hg) q := by
  -- Remove the transport proofs, then apply functoriality of `homotopyGroupMap`.
  funext x
  cases hg
  cases hf
  simpa [homotopyGroupMapOverEq] using congrFun (homotopyGroupMap_comp f g q a).symm x

/-- Helper for Theorem 9.3.3: the transported map of the identity is the identity. -/
private theorem homotopyGroupMapOverEq_id
    {A : Type*} [TopologicalSpace A] (a : A) (q : ℕ) :
    homotopyGroupMapOverEq (ContinuousMap.id A) (a := a) (b := a) rfl q = id := by
  -- There is no transport, so this is the identity-induced map on homotopy groups.
  funext x
  simp [homotopyGroupMapOverEq, homotopyGroupMap_id]

/-- Helper for Theorem 9.3.3: a singleton-relative homotopy induces a quotient-level homotopy of
generalized loops after postcomposition. -/
private theorem genLoopMap_homotopicRel_of_homotopyRel_singleton
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {f g : C(A, B)} (H : f.HomotopyRel g ({a} : Set A)) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    (genLoopMap f γ).1.HomotopicRel (genLoopMap g γ).1 (Cube.boundary (Fin q)) := by
  -- Postcompose the singleton-relative homotopy with the generalized-loop representative.
  refine ⟨{
    toHomotopy := H.toHomotopy.compContinuousMap γ.1
    prop' := ?_
  }⟩
  intro t x hx
  have hx' : γ x ∈ ({a} : Set A) := by
    simpa using γ.2 x hx
  simpa using H.prop t (γ x) hx'

/-- Helper for Theorem 9.3.3: postcomposing a generalized loop and then viewing the result at the
chosen target basepoint `b` produces a generalized loop based at `b`. -/
private theorem genLoopMapOverEqLoop_boundary
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    ∀ t ∈ Cube.boundary (Fin q), (genLoopMap f γ).1 t = b := by
  intro t ht
  calc
    (genLoopMap f γ).1 t = f a := by
      simpa using congrArg f (γ.2 t ht)
    _ = b := hf

/-- Helper for Theorem 9.3.3: the postcomposed generalized loop, regarded at the target
basepoint determined by `hf`. -/
private def genLoopMapOverEqLoop
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) {q : ℕ}
    (γ : Ω^ (Fin q) A a) :
    Ω^ (Fin q) B b :=
  ⟨(genLoopMap f γ).1, genLoopMapOverEqLoop_boundary f hf q γ⟩

/-- Helper for Theorem 9.3.3: the transported map on `π_ q` sends a representative to the class
of its postcomposition, viewed at the chosen target basepoint. -/
private theorem homotopyGroupMapOverEq_mk
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} (f : C(A, B)) (hf : f a = b) (q : ℕ)
    (γ : Ω^ (Fin q) A a) :
    homotopyGroupMapOverEq f hf q ⟦γ⟧ =
      (⟦genLoopMapOverEqLoop f hf γ⟧ : π_ q B b) := by
  -- Reduce to the definitional case where the chosen target point is literally `f a`.
  cases hf
  simpa [homotopyGroupMapOverEq, genLoopMapOverEqLoop] using homotopyGroupMap_mk f q a γ

/-- Helper for Theorem 9.3.3: a singleton-relative homotopy gives equal transported induced maps
on all homotopy groups. -/
private theorem homotopyGroupMapOverEq_eq_of_homotopyRel_singleton
    {A : Type*} {B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a : A} {b : B} {f g : C(A, B)}
    (H : f.HomotopyRel g ({a} : Set A)) (hf : f a = b) (hg : g a = b) (q : ℕ) :
    homotopyGroupMapOverEq f hf q = homotopyGroupMapOverEq g hg q := by
  -- After removing the endpoint transports, compare the two quotient maps on representatives.
  funext x
  refine Quotient.inductionOn x ?_
  intro γ
  rw [homotopyGroupMapOverEq_mk f hf q γ, homotopyGroupMapOverEq_mk g hg q γ]
  exact Quotient.sound (genLoopMap_homotopicRel_of_homotopyRel_singleton H q γ)

/-- Helper for Theorem 9.3.3: splitting a relative path at time `u` produces the homotopy-fiber
point whose stored path is the reversed projected tail from `u` to the endpoint. -/
private theorem actualFiberSplitPointPath_source {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    (((actualFiberRelativeToLoopMap p γ).subpath u 1).symm.toContinuousMap) 0 =
      underTopBasepoint B := by
  -- The reversed tail starts where the original projected path ends, namely at the basepoint.
  simpa using (((actualFiberRelativeToLoopMap p γ).subpath u 1).symm).source'

/-- Helper for Theorem 9.3.3: the reversed projected tail regarded as a point of `P[*]`. -/
private def actualFiberSplitPointPath {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    PathSpace (underTopBasepoint B) :=
  PathSpace.mk
    (((actualFiberRelativeToLoopMap p γ).subpath u 1).symm.toContinuousMap)
    (actualFiberSplitPointPath_source p γ u)

/-- Helper for Theorem 9.3.3: the split-point path ends at the projected point `p (γ u)`. -/
private theorem actualFiberSplitPoint_condition {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    p.right.hom (γ.path u) = (actualFiberSplitPointPath p γ u).endpoint := by
  -- Evaluate the reversed projected tail at its endpoint and read off the original path at `u`.
  rw [actualFiberSplitPointPath, PathSpace.endpoint_mk]
  have hloop : actualFiberRelativeToLoopMap p γ u = p.right.hom (γ.path u) := by
    -- Expanding the projected-loop map shows it is literally evaluation of `p ∘ γ.path`.
    rfl
  calc
    p.right.hom (γ.path u) = actualFiberRelativeToLoopMap p γ u := hloop.symm
    _ = (((actualFiberRelativeToLoopMap p γ).subpath u 1).symm.toContinuousMap) 1 := by
          simp [Path.subpath]

/-- Helper for Theorem 9.3.3: the split-point object feeding the direct round-trip family. -/
private def actualFiberSplitPoint {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    HomotopyFiber p :=
  HomotopyFiber.mk (γ.path u)
    (actualFiberSplitPointPath p γ u)
    (actualFiberSplitPoint_condition p γ u)

/-- Helper for Theorem 9.3.3: at `u = 0`, the split-point object is exactly the loop point used
by the reverse map. -/
private theorem actualFiberSplitPoint_zero {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitPoint p γ 0 =
      loopToActualFiberHomotopyFiberPoint p (actualFiberRelativeToLoopMap p γ) := by
  -- The initial split point keeps the basepoint of `E` and the full reversed projected loop.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change γ.path 0 = underTopBasepoint E
    exact γ.path.source'
  · apply Subtype.ext
    ext t
    change (((actualFiberRelativeToLoopMap p γ).subpath 0 1).symm.toContinuousMap) t =
      (Path.symm (actualFiberRelativeToLoopMap p γ)).toContinuousMap t
    simp [Path.subpath_zero_one, Path.cast_coe]

/-- Helper for Theorem 9.3.3: at `u = 1`, the split-point object has already reached the constant
actual-fiber representative of the endpoint. -/
private theorem actualFiberSplitPoint_one {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitPoint p γ 1 = actualFiberToHomotopyFiberFun p γ.endpoint := by
  -- The terminal split point keeps only the endpoint of `γ` together with the constant path.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change γ.path 1 = γ.endpoint.1
    exact γ.path.target'
  · apply Subtype.ext
    ext t
    change (((actualFiberRelativeToLoopMap p γ).subpath 1 1).symm.toContinuousMap) t =
      (Path.refl (underTopBasepoint B)).toContinuousMap t
    simp [Path.subpath_self]

/-- Helper for Theorem 9.3.3: the reversed projected tail used in `actualFiberSplitPoint`
varies continuously with the path and split parameter. -/
private theorem actualFiberSplitPointPath_continuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      actualFiberSplitPointPath p q.1 q.2 := by
  let family :
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I → C(I, B.right) :=
    fun q ↦ ((actualFiberRelativeToLoopMap p q.1).subpath 1 q.2).toContinuousMap
  have hfamily : Continuous family := by
    have hloop :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          ((actualFiberRelativeToLoopMap p r.1.1 : Ω B.right (underTopBasepoint B)) :
            C(I, B.right)) := by
      -- Forget the endpoint equations on the loop space and keep only the compact-open path
      -- coordinate coming from `actualFiberRelativeToLoopMap p`.
      exact
        continuous_induced_dom.comp
          ((actualFiberRelativeToLoopMap p).continuous.comp continuous_fst.fst)
    have hparam :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          Set.Icc.convexCombo (1 : I) r.1.2 r.2 := by
      -- The normalized subpath parameter is an explicit continuous formula in `(u, t)`.
      fun_prop
    have huncurry :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          family r.1 r.2 := by
      -- Expand the reversed subpath pointwise and apply compact-open continuity of evaluation.
      simpa [family, Path.subpath] using
        (continuous_eval.comp (hloop.prodMk hparam) :
          Continuous fun r :
              (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
            (((actualFiberRelativeToLoopMap p r.1.1 : Ω B.right (underTopBasepoint B)) :
                C(I, B.right))
              (Set.Icc.convexCombo (1 : I) r.1.2 r.2)))
    exact ContinuousMap.continuous_of_continuous_uncurry family huncurry
  -- Package the continuous underlying path family back into `PathSpace`.
  have hsource :
      ∀ q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
        family q 0 = underTopBasepoint B := by
    intro q
    change (((actualFiberRelativeToLoopMap p q.1).subpath 1 q.2).toContinuousMap) 0 =
      underTopBasepoint B
    simpa using actualFiberSplitPointPath_source p q.1 q.2
  have hpathSpace :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (⟨family q, hsource q⟩ : PathSpace (underTopBasepoint B)) := by
    exact hfamily.subtype_mk hsource
  simpa [actualFiberSplitPointPath, PathSpace.mk] using
    hpathSpace

/-- Helper for Theorem 9.3.3: the split-point object depends continuously on the path and split
parameter. -/
private theorem actualFiberSplitPoint_continuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      actualFiberSplitPoint p q.1 q.2 := by
  have hpath :
      Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
        (γ.path.toContinuousMap : C(I, E.right)) := by
    -- `PathToSet` carries the induced topology from endpoint/path coordinates, so the path
    -- coordinate is continuous by projection.
    exact
      continuous_snd.comp
        (continuous_induced_dom :
          Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
            PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ)
  have hpoint :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        q.1.path q.2 := by
    -- Evaluate the continuously varying path coordinate at the continuously varying time.
    exact continuous_eval.comp ((hpath.comp continuous_fst).prodMk continuous_snd)
  have hpair :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (q.1.path q.2, actualFiberSplitPointPath p q.1 q.2) := by
    -- The split-point object is determined by its `E`-coordinate and reversed-tail path.
    exact hpoint.prodMk (actualFiberSplitPointPath_continuous p)
  -- Repackage the continuous pair into the `HomotopyFiber p` subtype.
  simpa [actualFiberSplitPoint, HomotopyFiber.mk] using
    hpair.subtype_mk (fun q ↦ actualFiberSplitPoint_condition p q.1 q.2)

/-- Helper for Theorem 9.3.3: lifting the split point by the chosen contraction gives the moving
tail in `E`. -/
private theorem actualFiberSplitLiftPath_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    Continuous fun t : I ↦
      (homotopyFiberContractionLift p).toContinuousMap (t, actualFiberSplitPoint p γ u) := by
  -- Freeze the split point and compose the chosen lift with the constant pairing map.
  have hpair : Continuous fun t : I ↦ (t, actualFiberSplitPoint p γ u) := by
    exact continuous_id.prodMk continuous_const
  exact (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair

/-- Helper for Theorem 9.3.3: the split lift starts at the split point of `γ` in `E`. -/
private theorem actualFiberSplitLiftPath_source {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    (homotopyFiberContractionLift p).toContinuousMap (0, actualFiberSplitPoint p γ u) = γ.path u := by
  -- At time `0`, the chosen lift agrees with the point projection of the split point.
  calc
    (homotopyFiberContractionLift p).toContinuousMap (0, actualFiberSplitPoint p γ u)
        = (homotopyFiberPointProjection p).right.hom (actualFiberSplitPoint p γ u) := by
            simpa using (homotopyFiberContractionLift p).map_zero_left
              (actualFiberSplitPoint p γ u)
    _ = γ.path u := by
          rfl

/-- Helper for Theorem 9.3.3: the split lift ends at the actual-fiber image of the split point.
-/
private theorem actualFiberSplitLiftPath_target {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    (homotopyFiberContractionLift p).toContinuousMap (1, actualFiberSplitPoint p γ u) =
      ((homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p γ u)).1 := by
  -- At time `1`, the lift reaches the terminal actual-fiber point chosen in Chapter 8.
  simpa [homotopyFiberToActualFiber_hom_apply] using
    (homotopyFiberContractionLift p).map_one_left (actualFiberSplitPoint p γ u)

/-- Helper for Theorem 9.3.3: the split lift packaged as a path in `E`. -/
private def actualFiberSplitLiftPath {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p]
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    Path (γ.path u) (((homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p γ u)).1) :=
  Path.mk
    ⟨fun t ↦
        (homotopyFiberContractionLift p).toContinuousMap
          (t, actualFiberSplitPoint p γ u),
      actualFiberSplitLiftPath_continuous p γ u⟩
    (actualFiberSplitLiftPath_source p γ u)
    (actualFiberSplitLiftPath_target p γ u)

/-- Helper for Theorem 9.3.3: the Chapter 8 actual-fiber retraction family is a path from a fiber
point to its chosen retraction image. -/
private def actualFiberRetractionPath {E B : BasedSpace} (p : E ⟶ B) [IsBasedFibration p]
    (x : actualFiberSet p) :
    Path x ((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom x) :=
  Path.mk
    (actualFiberRetractionFamily p x)
    (actualFiberRetractionFamily_zero p x)
    (actualFiberRetractionFamily_one p x)

/-- Helper for Theorem 9.3.3: at `u = 0`, the split lift recovers the existing loop-lift path. -/
private theorem actualFiberSplitLiftPath_zero {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitLiftPath p γ 0 =
      (loopToActualFiberPath p (actualFiberRelativeToLoopMap p γ)).cast
        γ.path.source'
        (congrArg Subtype.val <| by
          rw [actualFiberSplitPoint_zero]
          rfl) := by
  -- The initial split point is exactly the Chapter 8 loop point, after aligning the endpoints.
  apply Path.ext
  ext t
  simpa [Path.cast, actualFiberSplitLiftPath, loopToActualFiberPath, actualFiberSplitPoint_zero]

/-- Helper for Theorem 9.3.3: at `u = 1`, the split lift is the Chapter 8 actual-fiber
retraction path of `γ.endpoint`. -/
private theorem actualFiberSplitLiftPath_one {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitLiftPath p γ 1 =
      ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val).cast
        γ.path.target'
        (congrArg Subtype.val <| by
          rw [actualFiberSplitPoint_one]
          rfl) := by
  -- The terminal split point is the constant actual-fiber representative of `γ.endpoint`.
  apply Path.ext
  ext t
  change
    (homotopyFiberContractionLift p).toContinuousMap (t, actualFiberSplitPoint p γ 1) =
      (actualFiberRetractionFamily p γ.endpoint t).1
  rw [actualFiberSplitPoint_one]
  simp [actualFiberRetractionFamily]

/-- Helper for Theorem 9.3.3: the underlying path coordinate on the relative path-space model is
continuous. -/
private theorem actualFiberPathToSet_pathContinuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
      (γ.path.toContinuousMap : C(I, E.right)) := by
  -- `PathToSet` uses the induced endpoint/path topology, so the path coordinate is the second
  -- projection after forgetting the subtype equations.
  exact
    continuous_snd.comp
      (continuous_induced_dom :
        Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
          PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ)

/-- Helper for Theorem 9.3.3: the split-point object of the constant relative path is the
basepoint of the homotopy fiber for every split parameter. -/
private theorem actualFiberSplitPoint_refl {E B : BasedSpace} (p : E ⟶ B) (u : I) :
    actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u =
      underTopBasepoint (homotopyFiber p) := by
  -- Both the point coordinate and the stored reversed projected tail collapse to the chosen
  -- homotopy-fiber basepoint when the input relative path is constant.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change (Path.refl (underTopBasepoint E)) u = underTopBasepoint E
    simp
  · apply Subtype.ext
    ext t
    change
      (((actualFiberRelativeToLoopMap p
            (PathToSet.refl (actualFiberBasepoint p))).subpath u 1).symm.toContinuousMap) t =
        underTopBasepoint B
    rw [actualFiberRelativeToLoopMap_refl p]
    simp [Path.subpath]

/-- Helper for Theorem 9.3.3: the split-lift family packages continuously as a map into
continuous paths in `E`. -/
private def actualFiberSplitLiftFamilyMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I, C(I, E.right)) :=
  { toFun := fun q ↦ (actualFiberSplitLiftPath p q.1 q.2).toContinuousMap
    continuous_toFun := by
      -- Uncurry the split lift to the Chapter 8 contraction lift on the continuously varying
      -- split-point object.
      refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
      have hsplit :
          Continuous fun r :
              (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
            actualFiberSplitPoint p r.1.1 r.1.2 := by
        exact (actualFiberSplitPoint_continuous p).comp continuous_fst
      have hpair :
          Continuous fun r :
              (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
            (r.2, actualFiberSplitPoint p r.1.1 r.1.2) := by
        exact continuous_snd.prodMk hsplit
      simpa [actualFiberSplitLiftPath] using
        (homotopyFiberContractionLift p).toContinuousMap.continuous.comp hpair }

/-- Helper for Theorem 9.3.3: the initial segment of a relative path, recast so its source is the
fixed actual-fiber basepoint. -/
private def actualFiberSplitFrontPath {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    Path (actualFiberBasepoint p).1 (γ.path u) :=
  -- Recast the front subpath so later stage maps can compare sources without transport noise.
  (γ.path.subpath 0 u).cast γ.path.source'.symm rfl

/-- Helper for Theorem 9.3.3: the split-front adapter still starts at the fixed actual-fiber
basepoint. -/
private theorem actualFiberSplitFrontPath_source {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    actualFiberSplitFrontPath p γ u 0 = (actualFiberBasepoint p).1 := by
  -- This is the source field of the recast initial subpath.
  exact (actualFiberSplitFrontPath p γ u).source'

/-- Helper for Theorem 9.3.3: the split-front adapter ends at the point `γ.path u`. -/
private theorem actualFiberSplitFrontPath_target {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    actualFiberSplitFrontPath p γ u 1 = γ.path u := by
  -- This is the target field of the recast initial subpath.
  exact (actualFiberSplitFrontPath p γ u).target'

/-- Helper for Theorem 9.3.3: the split-front adapter starts at the constant basepoint path when
`u = 0`. -/
@[simp] private theorem actualFiberSplitFrontPath_zero {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitFrontPath p γ 0 =
      (Path.refl (actualFiberBasepoint p).1).cast rfl γ.path.source' := by
  -- Compare the underlying pointwise formula; at `u = 0` the front subpath is constant.
  apply Path.ext
  ext t
  change γ.path (Set.Icc.convexCombo 0 0 t) = (actualFiberBasepoint p).1
  have hzero : Set.Icc.convexCombo (0 : I) 0 t = 0 := by
    apply Subtype.ext
    simp
  rw [hzero]
  exact γ.path.source'

/-- Helper for Theorem 9.3.3: the split-front adapter recovers the original relative path when
`u = 1`. -/
@[simp] private theorem actualFiberSplitFrontPath_one {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitFrontPath p γ 1 = γ.path.cast rfl γ.path.target' := by
  -- Compare the underlying pointwise formula; at `u = 1` the front subpath is the original path.
  apply Path.ext
  ext t
  change γ.path (Set.Icc.convexCombo 0 1 t) = γ.path t
  have hone : Set.Icc.convexCombo (0 : I) 1 t = t := by
    apply Subtype.ext
    simp
  rw [hone]

/-- Helper for Theorem 9.3.3: truncating the Chapter 8 endpoint-retraction family at `u` gives the
tail path from `γ.endpoint` to the stage-`u` retraction point. -/
private def actualFiberRetractionTailPath {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    Path γ.endpoint.1 ((actualFiberRetractionFamily p γ.endpoint u).1) :=
  Path.mk
    ⟨fun t ↦ (actualFiberRetractionFamily p γ.endpoint (Set.Icc.convexCombo 0 u t)).1,
      by
        -- Compose the Chapter 8 retraction family with the affine parameter on `[0, u]`.
        exact
          continuous_subtype_val.comp <|
            (continuous_eval.comp <|
              (((actualFiberRetractionFamily p).continuous.comp continuous_const).prodMk <|
                by
                  fun_prop))⟩
    (by
      -- At `t = 0`, the truncated tail starts at the original endpoint.
      simpa using congrArg Subtype.val (actualFiberRetractionFamily_zero p γ.endpoint))
    (by
      -- At `t = 1`, the affine parameter reaches `u`.
      simp)

/-- Helper for Theorem 9.3.3: the truncated retraction tail still starts at `γ.endpoint`. -/
private theorem actualFiberRetractionTailPath_source {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    actualFiberRetractionTailPath p γ u 0 = γ.endpoint.1 := by
  -- This is the source field of the truncated Chapter 8 retraction tail.
  exact (actualFiberRetractionTailPath p γ u).source'

/-- Helper for Theorem 9.3.3: the truncated retraction tail ends at the stage-`u` retraction
point. -/
private theorem actualFiberRetractionTailPath_target {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) (u : I) :
    actualFiberRetractionTailPath p γ u 1 = (actualFiberRetractionFamily p γ.endpoint u).1 := by
  -- This is the target field of the truncated Chapter 8 retraction tail.
  exact (actualFiberRetractionTailPath p γ u).target'

/-- Helper for Theorem 9.3.3: the truncated retraction tail is constant at the endpoint when
`u = 0`. -/
@[simp] private theorem actualFiberRetractionTailPath_zero {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRetractionTailPath p γ 0 =
      (Path.refl γ.endpoint.1).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_zero p γ.endpoint)) := by
  -- Compare the underlying pointwise formula; the `u = 0` tail is constant at the endpoint.
  apply Path.ext
  ext t
  change (actualFiberRetractionFamily p γ.endpoint (Set.Icc.convexCombo 0 0 t)).1 =
    γ.endpoint.1
  have hzero : Set.Icc.convexCombo (0 : I) 0 t = 0 := by
    apply Subtype.ext
    simp
  rw [hzero]
  simpa using congrArg Subtype.val (actualFiberRetractionFamily_zero p γ.endpoint)

/-- Helper for Theorem 9.3.3: at `u = 1`, the truncated retraction tail is the full Chapter 8
endpoint-retraction path. -/
@[simp] private theorem actualFiberRetractionTailPath_one {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRetractionTailPath p γ 1 =
      ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_one p γ.endpoint)) := by
  -- Compare the underlying pointwise formula; the `u = 1` tail is the full retraction path.
  apply Path.ext
  ext t
  change (actualFiberRetractionFamily p γ.endpoint (Set.Icc.convexCombo 0 1 t)).1 =
    (actualFiberRetractionFamily p γ.endpoint t).1
  have hone : Set.Icc.convexCombo (0 : I) 1 t = t := by
    apply Subtype.ext
    simp
  rw [hone]

/-- Helper for Theorem 9.3.3: the intermediate path-space endomorphism obtained by appending the
Chapter 8 actual-fiber retraction path at the endpoint. -/
private def actualFiberRetractionPathToSetMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) := by
  -- Package the endpoint-retraction correction as a continuous endomorphism of the path-space
  -- model, so both later homotopies can target the same named map.
  refine
    { toFun := fun γ ↦
        { endpoint := (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint
          path := γ.path.trans
            ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val) }
      continuous_toFun := ?_ }
  rw [continuous_induced_rng]
  change Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
    (((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint),
      (γ.path.trans
        ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).toContinuousMap)
  have hendpoint :
      Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
        (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint := by
    -- The endpoint coordinate is the path endpoint followed by the Chapter 8 retraction.
    exact
      (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom.continuous.comp
        (continuous_fst.comp (continuous_induced_dom :
          Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
            PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ))
  let family :
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 → C(I, E.right) := fun γ ↦
        (γ.path.trans
          ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).toContinuousMap
  have hpathCoord :
      Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
        (γ.path.toContinuousMap : C(I, E.right)) := by
    -- `PathToSet` uses the induced endpoint/path topology, so the path coordinate is a
    -- projection.
    exact
      continuous_snd.comp
        (continuous_induced_dom :
          Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
            PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ)
  have htail :
      Continuous ↿fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
        (actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val := by
    -- The endpoint-retraction path is controlled by the Chapter 8 actual-fiber deformation
    -- family, viewed after forgetting the subtype coordinate.
    have huncurry :
        Continuous fun q :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) × I ↦
          ((((actualFiberRetractionPath p q.1.endpoint).map continuous_subtype_val) :
              Path q.1.endpoint.1
                ((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom
                  q.1.endpoint).1) : C(I, E.right)) q.2 := by
      have hendpointEval :
          Continuous fun q :
              (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) × I ↦
            (actualFiberRetractionFamily p q.1.endpoint q.2).1 := by
        -- Evaluate the Chapter 8 endpoint family at the moving endpoint and time parameter.
        have hendpointCoord :
            Continuous fun q :
                (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) × I ↦ q.1.endpoint := by
          exact
            continuous_fst.comp
              ((continuous_induced_dom :
                Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
                  PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ).comp
                continuous_fst)
        exact
          continuous_subtype_val.comp <|
            (continuous_eval.comp <|
              (((actualFiberRetractionFamily p).continuous.comp hendpointCoord).prodMk
                continuous_snd))
      simpa [actualFiberRetractionPath, family] using hendpointEval
    simpa [family] using huncurry
  have hpath :
      Continuous family := by
    -- Turn the path-family continuity into continuity of the underlying continuous maps.
    refine ContinuousMap.continuous_of_continuous_uncurry family ?_
    let front :
        ∀ γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
          Path (actualFiberBasepoint p).1 γ.endpoint.1 := fun γ ↦ γ.path
    let tail :
        ∀ γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
          Path γ.endpoint.1
            ((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom
              γ.endpoint).1 := fun γ ↦
        (actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val
    have hfront :
        Continuous ↿front := by
      -- The front segment is just the original varying relative path.
      have huncurry :
          Continuous fun q :
              (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) × I ↦
            ((front q.1 : Path (actualFiberBasepoint p).1 q.1.endpoint.1) : C(I, E.right)) q.2 := by
        exact continuous_eval.comp ((hpathCoord.comp continuous_fst).prodMk continuous_snd)
      simpa [front] using huncurry
    have htrans :
        Continuous ↿fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
          (front γ).trans (tail γ) := by
      exact Path.trans_continuous_family front hfront tail (by simpa [tail] using htail)
    simpa [family, front, tail] using htrans
  exact hendpoint.prodMk hpath

/-- Helper for Theorem 9.3.3: the endpoint coordinate on the actual-fiber path-space model is
continuous. -/
private theorem actualFiberPathToSet_endpointContinuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦ γ.endpoint := by
  -- `PathToSet` carries the induced endpoint/path topology, so the endpoint coordinate is the
  -- first projection after forgetting the subtype equations.
  exact
    continuous_fst.comp
      (continuous_induced_dom :
        Continuous fun γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 ↦
          PathToSet.endpointAndPath (actualFiberSet p) (actualFiberBasepoint p) γ)

/-- Helper for Theorem 9.3.3: delaying a constant path on the left does not change it. -/
private theorem delayReflLeft_refl {X : Type*} [TopologicalSpace X] (x : X) (θ : I) :
    Path.delayReflLeft θ (Path.refl x) = Path.refl x := by
  -- The left-delay family is pointwise constant on a constant path.
  ext t
  simp [Path.delayReflLeft, Path.delayReflRight]

/-- Helper for Theorem 9.3.3: delaying a constant path on the right does not change it. -/
private theorem delayReflRight_refl {X : Type*} [TopologicalSpace X] (x : X) (θ : I) :
    Path.delayReflRight θ (Path.refl x) = Path.refl x := by
  -- The right-delay family is pointwise constant on a constant path.
  ext t
  simp [Path.delayReflRight]

/-- Helper for Theorem 9.3.3: the reverse loop-lift map is the explicit endpoint-plus-path pair
on `PathToSet`. -/
@[simp] private theorem loopToActualFiberRelativeMap_apply {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (χ : Ω B.right (underTopBasepoint B)) :
    loopToActualFiberRelativeMap p χ =
      { endpoint := loopToActualFiberEndpoint p χ
        path := loopToActualFiberPath p χ } := by
  -- Push the modeled loop-lift through the Chapter 9 homeomorphism back to its endpoint/path
  -- coordinates.
  change
    inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p)
      (loopToActualFiberInclusionHomotopyFiber p χ) =
    { endpoint := loopToActualFiberEndpoint p χ
      path := loopToActualFiberPath p χ }
  rw [inclusionHomotopyFiberHomeomorphPathToSet_apply]
  rfl

/-- Helper for Theorem 9.3.3: singleton-relative homotopies on the modeled inclusion homotopy
fiber transport across the Chapter 9 homeomorphism to singleton-relative homotopies on
`PathToSet`. -/
private def actualFiberModelHomotopyRelToPathToSet {E B : BasedSpace} (p : E ⟶ B)
    {f g :
      C(inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p),
        inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p))}
    (H : f.HomotopyRel g
      ({inclusionHomotopyFiber.mk (actualFiberBasepoint p)
          (Path.refl (actualFiberBasepoint p).1)} :
        Set (inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)))) :
    ((((inclusionHomotopyFiberHomeomorphPathToSet
          (actualFiberSet p) (actualFiberBasepoint p)) :
          C(inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p),
            PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)).comp f).comp
        { toFun := pathToSetToInclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
          continuous_toFun :=
            (pathToSetToInclusionHomotopyFiber_isEmbedding
              (actualFiberSet p) (actualFiberBasepoint p)).continuous }).HomotopyRel
      ((((inclusionHomotopyFiberHomeomorphPathToSet
            (actualFiberSet p) (actualFiberBasepoint p)) :
            C(inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p),
              PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)).comp g).comp
          { toFun := pathToSetToInclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
            continuous_toFun :=
              (pathToSetToInclusionHomotopyFiber_isEmbedding
                (actualFiberSet p) (actualFiberBasepoint p)).continuous })
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) := by
  let e :
      C(inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p),
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
    inclusionHomotopyFiberHomeomorphPathToSet (actualFiberSet p) (actualFiberBasepoint p)
  let j :
      C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
        inclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)) :=
    { toFun := pathToSetToInclusionHomotopyFiber (actualFiberSet p) (actualFiberBasepoint p)
      continuous_toFun :=
        (pathToSetToInclusionHomotopyFiber_isEmbedding
          (actualFiberSet p) (actualFiberBasepoint p)).continuous }
  -- Transport the modeled homotopy by postcomposing with the homeomorphism and precomposing with
  -- its inverse model map.
  refine { toHomotopy := (H.compContinuousMap e).toHomotopy.compContinuousMap j, prop' := ?_ }
  intro t γ hγ
  rcases hγ with rfl
  have hj :
      j (PathToSet.refl (actualFiberBasepoint p)) =
        inclusionHomotopyFiber.mk (actualFiberBasepoint p)
          (Path.refl (actualFiberBasepoint p).1) := by
    rfl
  have hprop :=
    (H.compContinuousMap e).prop t
      (j (PathToSet.refl (actualFiberBasepoint p))) (by simpa [hj])
  simpa [e, j, hj] using hprop

/-- Helper for Theorem 9.3.3: a bundled `PathToSet` family with fixed singleton basepoint slices
packages to a singleton-relative homotopy. -/
private def pathToSetHomotopyRelSingletonOfFamilyMap {E B : BasedSpace} (p : E ⟶ B)
    {f₀ f₁ :
      C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)}
    (H :
      C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1))
    (h₀ : ∀ γ, H (γ, 0) = f₀ γ)
    (h₁ : ∀ γ, H (γ, 1) = f₁ γ)
    (hrel : ∀ θ, H (PathToSet.refl (actualFiberBasepoint p), θ) =
      PathToSet.refl (actualFiberBasepoint p)) :
    f₀.HomotopyRel f₁
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) := by
  -- Package the bundled family by reading it as a homotopy in the `I`-direction.
  refine { toHomotopy := ContinuousMap.Homotopy.ofProdSwap H ?_ ?_, prop' := ?_ }
  · intro γ
    simpa using h₀ γ
  · intro γ
    simpa using h₁ γ
  · intro θ γ hγ
    rcases hγ with rfl
    calc
      H (PathToSet.refl (actualFiberBasepoint p), θ)
          = PathToSet.refl (actualFiberBasepoint p) := hrel θ
      _ = H (PathToSet.refl (actualFiberBasepoint p), 0) := (hrel 0).symm
      _ = f₀ (PathToSet.refl (actualFiberBasepoint p)) := h₀ _

/-- Helper for Theorem 9.3.3: the left-unit delay family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberRoundTripLeftUnitFamily_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      ({ endpoint :=
          (loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).endpoint
         path :=
          Path.delayReflLeft q.2
            ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).path) } :
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) := by
  -- Record the strict round-trip endpoint/path coordinates explicitly, then evaluate the delayed
  -- left path through the `delayReflRight` formula on the reversed path.
  rw [continuous_induced_rng]
  change Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).endpoint,
      (Path.delayReflLeft q.2
        ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).path)).toContinuousMap)
  let roundTrip :
      C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
    (loopToActualFiberRelativeMap p).comp (actualFiberRelativeToLoopMap p)
  have hendpoint :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (roundTrip q.1).endpoint := by
    exact (actualFiberPathToSet_endpointContinuous p).comp (roundTrip.continuous.comp continuous_fst)
  let family :
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I → C(I, E.right) := fun q ↦
        (Path.delayReflLeft q.2 (roundTrip q.1).path).toContinuousMap
  have hpathCoord :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((roundTrip q.1).path.toContinuousMap : C(I, E.right)) := by
    exact (actualFiberPathToSet_pathContinuous p).comp (roundTrip.continuous.comp continuous_fst)
  have hpath : Continuous family := by
    refine ContinuousMap.continuous_of_continuous_uncurry family ?_
    have hparam :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          (σ (unitInterval.qRight (σ r.2, r.1.2)) : I) := by
      exact unitInterval.continuous_symm.comp <|
        unitInterval.continuous_qRight.comp <|
          ((unitInterval.continuous_symm.comp continuous_snd).prodMk
            (continuous_snd.comp continuous_fst))
    simpa [family, roundTrip, Path.delayReflLeft, Path.delayReflRight, Path.symm] using
      (continuous_eval.comp ((hpathCoord.comp continuous_fst).prodMk hparam) :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          ((roundTrip r.1.1).path.toContinuousMap
            (σ (unitInterval.qRight (σ r.2, r.1.2)))))
  exact hendpoint.prodMk hpath

/-- Helper for Theorem 9.3.3: the bundled left-unit delay family on the actual-fiber
`PathToSet` model. -/
private def actualFiberRoundTripLeftUnitFamilyMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Package the strict round-trip path with the standard left-unit delay deformation.
  { toFun := fun q ↦
      { endpoint :=
          (loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).endpoint
        path :=
          Path.delayReflLeft q.2
            ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p q.1)).path) }
    continuous_toFun := actualFiberRoundTripLeftUnitFamily_continuous p }

/-- Helper for Theorem 9.3.3: the explicit left-unit normal form of the round-trip map. -/
private def actualFiberRoundTripLeftUnitMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Evaluate the bundled left-unit delay family at `0`.
  { toFun := fun γ ↦ actualFiberRoundTripLeftUnitFamilyMap p (γ, 0)
    continuous_toFun :=
      (actualFiberRoundTripLeftUnitFamilyMap p).continuous.comp
        (continuous_id.prodMk continuous_const) }

/-- Helper for Theorem 9.3.3: at `u = 1`, the left-unit delay family recovers the strict
round-trip map. -/
@[simp] private theorem actualFiberRoundTripLeftUnitFamily_one {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRoundTripLeftUnitFamilyMap p (γ, 1) =
      ((loopToActualFiberRelativeMap p).comp (actualFiberRelativeToLoopMap p)) γ := by
  -- Compare endpoint and path coordinates; at `u = 1` the delay family is the original path.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro t
  change
    Path.delayReflLeft 1
      ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).path) t =
      (loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).path t
  simpa using
    congrArg (fun η : Path (actualFiberBasepoint p).1
        (loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).endpoint.1 ↦ η t)
      (Path.delayReflLeft_one
        ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).path))

/-- Helper for Theorem 9.3.3: the left-unit delay family fixes the constant relative path at every
stage. -/
private theorem actualFiberRoundTripLeftUnitFamily_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (θ : I) :
    actualFiberRoundTripLeftUnitFamilyMap p (PathToSet.refl (actualFiberBasepoint p), θ) =
      PathToSet.refl (actualFiberBasepoint p) := by
  -- The strict round trip fixes the constant path, and the left delay keeps a constant path
  -- constant.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change
      (actualFiberRoundTripLeftUnitFamilyMap p
          (PathToSet.refl (actualFiberBasepoint p), θ)).endpoint =
        (PathToSet.refl (actualFiberBasepoint p)).endpoint
    change
      (loopToActualFiberRelativeMap p
          (actualFiberRelativeToLoopMap p (PathToSet.refl (actualFiberBasepoint p)))).endpoint =
        actualFiberBasepoint p
    rw [actualFiberRelativeToLoopMap_refl p, loopToActualFiberRelativeMap_refl p]
    rfl
  · apply ContinuousMap.ext
    intro t
    change
      (actualFiberRoundTripLeftUnitFamilyMap p
          (PathToSet.refl (actualFiberBasepoint p), θ)).path t =
        (PathToSet.refl (actualFiberBasepoint p)).path t
    change
      Path.delayReflLeft θ
          ((loopToActualFiberRelativeMap p
              (actualFiberRelativeToLoopMap p (PathToSet.refl (actualFiberBasepoint p)))).path) t =
        (Path.refl (actualFiberBasepoint p).1) t
    rw [actualFiberRelativeToLoopMap_refl p, loopToActualFiberRelativeMap_refl p]
    simpa using
      congrArg (fun η : Path (actualFiberBasepoint p).1 (actualFiberBasepoint p).1 ↦ η t)
        (delayReflLeft_refl (actualFiberBasepoint p).1 θ)

/-- Helper for Theorem 9.3.3: the right-unit delay family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberRightUnitFamily_continuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      ({ endpoint := q.1.endpoint
         path := Path.delayReflRight q.2 q.1.path } :
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) := by
  -- Record the endpoint/path coordinates explicitly, then use the compact-open formula for
  -- `delayReflRight` on the underlying path coordinate.
  rw [continuous_induced_rng]
  change Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    (q.1.endpoint, (Path.delayReflRight q.2 q.1.path).toContinuousMap)
  have hendpoint :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        q.1.endpoint := by
    exact (actualFiberPathToSet_endpointContinuous p).comp continuous_fst
  let family :
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I → C(I, E.right) := fun q ↦
        (Path.delayReflRight q.2 q.1.path).toContinuousMap
  have hpathCoord :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (q.1.path.toContinuousMap : C(I, E.right)) := by
    exact (actualFiberPathToSet_pathContinuous p).comp continuous_fst
  have hpath : Continuous family := by
    -- Uncurry the delayed path and evaluate the original path at the right-delay parameter.
    refine ContinuousMap.continuous_of_continuous_uncurry family ?_
    have hparam :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          unitInterval.qRight (r.2, r.1.2) := by
      exact unitInterval.continuous_qRight.comp
        (continuous_snd.prodMk (continuous_snd.comp continuous_fst))
    simpa [family, Path.delayReflRight] using
      (continuous_eval.comp ((hpathCoord.comp continuous_fst).prodMk hparam) :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          ((r.1.1.path.toContinuousMap : C(I, E.right))
            (unitInterval.qRight (r.2, r.1.2))))
  exact hendpoint.prodMk hpath

/-- Helper for Theorem 9.3.3: the bundled right-unit delay family on the actual-fiber
`PathToSet` model. -/
private def actualFiberRightUnitFamilyMap {E B : BasedSpace} (p : E ⟶ B) :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Package the identity-side path with the standard right-unit delay deformation.
  { toFun := fun q ↦
      { endpoint := q.1.endpoint
        path := Path.delayReflRight q.2 q.1.path }
    continuous_toFun := actualFiberRightUnitFamily_continuous p }

/-- Helper for Theorem 9.3.3: the explicit right-unit normal form of the identity-side map. -/
private def actualFiberRightUnitMap {E B : BasedSpace} (p : E ⟶ B) :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Evaluate the bundled right-unit delay family at `0`.
  { toFun := fun γ ↦ actualFiberRightUnitFamilyMap p (γ, 0)
    continuous_toFun :=
      (actualFiberRightUnitFamilyMap p).continuous.comp (continuous_id.prodMk continuous_const) }

/-- Helper for Theorem 9.3.3: the split-front family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberSplitFrontPath_familyContinuous {E B : BasedSpace} (p : E ⟶ B) :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      (actualFiberSplitFrontPath p q.1 q.2).toContinuousMap := by
  -- Uncurry the recast front subpath and evaluate the original path at the affine subpath
  -- parameter.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hpath :
      Continuous fun r :
          (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
        ((r.1.1.path.toContinuousMap : C(I, E.right))
          (Set.Icc.convexCombo (0 : I) r.1.2 r.2)) := by
    have hpathCoord :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          (r.1.1.path.toContinuousMap : C(I, E.right)) := by
      exact (actualFiberPathToSet_pathContinuous p).comp (continuous_fst.comp continuous_fst)
    have hparam :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          Set.Icc.convexCombo (0 : I) r.1.2 r.2 := by
      fun_prop
    exact continuous_eval.comp (hpathCoord.prodMk hparam)
  simpa [actualFiberSplitFrontPath, Path.subpath, Path.cast] using hpath

/-- Helper for Theorem 9.3.3: the split-stage family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberSplitStageFamily_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      ({ endpoint := (homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p q.1 q.2)
         path := (actualFiberSplitFrontPath p q.1 q.2).trans (actualFiberSplitLiftPath p q.1 q.2) } :
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) := by
  -- Record the endpoint/path coordinates explicitly, then use continuity of front paths and
  -- Chapter 8 split lifts before concatenating them.
  rw [continuous_induced_rng]
  change Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    ((homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p q.1 q.2),
      ((actualFiberSplitFrontPath p q.1 q.2).trans
        (actualFiberSplitLiftPath p q.1 q.2)).toContinuousMap)
  have hendpoint :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p q.1 q.2) := by
    exact ((homotopyFiberToActualFiber p).right.hom.continuous).comp
      (actualFiberSplitPoint_continuous p)
  let front := fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    actualFiberSplitFrontPath p q.1 q.2
  let tail := fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    actualFiberSplitLiftPath p q.1 q.2
  have hfrontMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((front q).toContinuousMap : C(I, E.right)) := by
    simpa [front] using actualFiberSplitFrontPath_familyContinuous p
  have htailMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((tail q).toContinuousMap : C(I, E.right)) := by
    simpa [tail] using (actualFiberSplitLiftFamilyMap p).continuous
  have hfront : Continuous ↿front := by
    simpa [front] using ContinuousMap.continuous_uncurry_of_continuous ⟨_, hfrontMap⟩
  have htail : Continuous ↿tail := by
    simpa [tail] using ContinuousMap.continuous_uncurry_of_continuous ⟨_, htailMap⟩
  have hpath :
      Continuous ↿fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (front q).trans (tail q) := by
    exact Path.trans_continuous_family front hfront tail htail
  have hpathMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((((front q).trans (tail q)) :
          Path (actualFiberBasepoint p).1
              (((homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p q.1 q.2)).1)).toContinuousMap :
          C(I, E.right)) := ContinuousMap.continuous_of_continuous_uncurry _ hpath
  exact hendpoint.prodMk (by simpa [front, tail] using hpathMap)

/-- Helper for Theorem 9.3.3: the bundled split-stage family on the actual-fiber `PathToSet`
model. -/
private def actualFiberSplitStageFamilyMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Package the split-front and split-lift midpoint comparison into one bundled family.
  { toFun := fun q ↦
      { endpoint := (homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p q.1 q.2)
        path := (actualFiberSplitFrontPath p q.1 q.2).trans (actualFiberSplitLiftPath p q.1 q.2) }
    continuous_toFun := actualFiberSplitStageFamily_continuous p }

/-- Helper for Theorem 9.3.3: the endpoint-retraction tail family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberRetractionTailPath_familyContinuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      (actualFiberRetractionTailPath p q.1 q.2).toContinuousMap := by
  -- Uncurry the truncated Chapter 8 retraction tail and evaluate the endpoint family at the
  -- affine parameter on `[0, u]`.
  refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
  have hfamily :
      Continuous fun r :
          (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
        (actualFiberRetractionFamily p r.1.1.endpoint
          (Set.Icc.convexCombo (0 : I) r.1.2 r.2)).1 := by
    have hendpoint :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          r.1.1.endpoint := by
      exact (actualFiberPathToSet_endpointContinuous p).comp (continuous_fst.comp continuous_fst)
    have hparam :
        Continuous fun r :
            (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I) × I ↦
          Set.Icc.convexCombo (0 : I) r.1.2 r.2 := by
      fun_prop
    exact continuous_subtype_val.comp <|
      (continuous_eval.comp <|
        (((actualFiberRetractionFamily p).continuous.comp hendpoint).prodMk hparam))
  simpa [actualFiberRetractionTailPath] using hfamily

/-- Helper for Theorem 9.3.3: the endpoint-retraction tail family is continuous on the actual-fiber
`PathToSet` model. -/
private theorem actualFiberRetractionTailStageFamily_continuous {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
      ({ endpoint := actualFiberRetractionFamily p q.1.endpoint q.2
         path := q.1.path.trans (actualFiberRetractionTailPath p q.1 q.2) } :
        PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) := by
  -- Record the endpoint/path coordinates explicitly, then concatenate the original varying path
  -- with the truncated Chapter 8 retraction tail.
  rw [continuous_induced_rng]
  change Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    (actualFiberRetractionFamily p q.1.endpoint q.2,
      (q.1.path.trans (actualFiberRetractionTailPath p q.1 q.2)).toContinuousMap)
  have hendpoint :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        actualFiberRetractionFamily p q.1.endpoint q.2 := by
    have hpair :
        Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
          ((q.1.endpoint, q.2) : actualFiberSet p × I) := by
      exact ((actualFiberPathToSet_endpointContinuous p).comp continuous_fst).prodMk continuous_snd
    simpa using
      (ContinuousMap.continuous_uncurry_of_continuous (actualFiberRetractionFamily p)).comp hpair
  let front := fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    q.1.path
  let tail := fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
    actualFiberRetractionTailPath p q.1 q.2
  have hfrontMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((front q).toContinuousMap : C(I, E.right)) := by
    exact (actualFiberPathToSet_pathContinuous p).comp continuous_fst
  have htailMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((tail q).toContinuousMap : C(I, E.right)) := by
    simpa [tail] using actualFiberRetractionTailPath_familyContinuous p
  have hfront : Continuous ↿front := by
    simpa [front] using ContinuousMap.continuous_uncurry_of_continuous ⟨_, hfrontMap⟩
  have htail : Continuous ↿tail := by
    simpa [tail] using ContinuousMap.continuous_uncurry_of_continuous ⟨_, htailMap⟩
  have hpath :
      Continuous ↿fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        (front q).trans (tail q) := by
    exact Path.trans_continuous_family front hfront tail htail
  have hpathMap :
      Continuous fun q : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I ↦
        ((((front q).trans (tail q)) :
            Path (actualFiberBasepoint p).1 ((actualFiberRetractionFamily p q.1.endpoint q.2).1)).toContinuousMap :
          C(I, E.right)) := ContinuousMap.continuous_of_continuous_uncurry _ hpath
  exact hendpoint.prodMk (by simpa [front, tail] using hpathMap)

/-- Helper for Theorem 9.3.3: the bundled endpoint-retraction tail family on the actual-fiber
`PathToSet` model. -/
private def actualFiberRetractionTailStageFamilyMap {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    C(PathToSet (actualFiberSet p) (actualFiberBasepoint p).1 × I,
      PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :=
  -- Package the endpoint-retraction midpoint comparison into one bundled family.
  { toFun := fun q ↦
      { endpoint := actualFiberRetractionFamily p q.1.endpoint q.2
        path := q.1.path.trans (actualFiberRetractionTailPath p q.1 q.2) }
    continuous_toFun := actualFiberRetractionTailStageFamily_continuous p }

/-- Helper for Theorem 9.3.3: the left-unit normal form deforms to the strict round-trip map
relative to the constant path. -/
private def actualFiberRoundTripLeftUnitHomotopyRel {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    (actualFiberRoundTripLeftUnitMap p).HomotopyRel
      ((loopToActualFiberRelativeMap p).comp (actualFiberRelativeToLoopMap p))
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) :=
  -- Package the bundled left-unit delay family as a singleton-relative homotopy.
  pathToSetHomotopyRelSingletonOfFamilyMap p
    (actualFiberRoundTripLeftUnitFamilyMap p)
    (fun _ ↦ rfl)
    (actualFiberRoundTripLeftUnitFamily_one p)
    (actualFiberRoundTripLeftUnitFamily_refl p)

/-- Helper for Theorem 9.3.3: at `u = 0`, the split-stage family agrees with the left-unit normal
form. -/
private theorem actualFiberSplitZeroPath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    (actualFiberSplitFrontPath p γ 0).trans (actualFiberSplitLiftPath p γ 0) =
      ((Path.refl (actualFiberBasepoint p).1).trans
        (loopToActualFiberPath p (actualFiberRelativeToLoopMap p γ))).cast rfl
        (by
          simpa [loopToActualFiberEndpoint, actualFiberSplitPoint_zero]) := by
  -- Normalize both split-stage factors at `u = 0`, then collapse the remaining casted
  -- concatenation to the left-unit normal form in one `Path.cast_trans` step.
  rw [actualFiberSplitFrontPath_zero, actualFiberSplitLiftPath_zero]
  simpa using
    (Path.cast_trans (Path.refl (actualFiberBasepoint p).1)
      (loopToActualFiberPath p (actualFiberRelativeToLoopMap p γ)) rfl γ.path.source'
      (by
        simpa [loopToActualFiberEndpoint, actualFiberSplitPoint_zero])).symm

/-- Helper for Theorem 9.3.3: at `u = 1`, the split-stage endpoint already agrees with the
Chapter 8 actual-fiber retraction owner. -/
private theorem actualFiberSplitPointOneEndpoint {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    (homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p γ 1) =
      (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint := by
  -- Rewrite the split point at `u = 1`, then compare the two owner-level spellings of the same
  -- actual-fiber point coming from the Chapter 8 retraction.
  rw [actualFiberSplitPoint_one]
  simpa [Category.assoc, actualFiberToHomotopyFiberFun, actualFiberToHomotopyFiber_hom_apply,
    homotopyFiberToActualFiber_hom_apply]

/-- Helper for Theorem 9.3.3: the underlying endpoint values match after the owner-level split
`u = 1` bridge is established. -/
private theorem actualFiberSplitOneEndpoint_val {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    (((homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p γ 1)).1) =
      (((actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint).1) := by
  -- Forget the subtype proof and keep only the underlying point equality needed for `Path.cast`.
  exact congrArg Subtype.val (actualFiberSplitPointOneEndpoint p γ)

private theorem actualFiberSplitOnePath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    (actualFiberSplitFrontPath p γ 1).trans (actualFiberSplitLiftPath p γ 1) =
      (γ.path.trans ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).cast rfl
        (actualFiberSplitOneEndpoint_val p γ) := by
  -- Normalize the front and lift factors separately, then collapse the remaining endpoint casts
  -- by the canonical `Path.cast_trans` identity.
  rw [actualFiberSplitFrontPath_one, actualFiberSplitLiftPath_one]
  simpa using
    (Path.cast_trans γ.path ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)
      rfl γ.path.target' (actualFiberSplitOneEndpoint_val p γ)).symm

/-- Helper for Theorem 9.3.3: the split front of the constant relative path is constant. -/
private theorem actualFiberSplitFrontPath_refl {E B : BasedSpace} (p : E ⟶ B) (u : I) :
    actualFiberSplitFrontPath p (PathToSet.refl (actualFiberBasepoint p)) u =
      Path.refl (actualFiberBasepoint p).1 :=
  -- Unfold the front subpath of the constant path; every evaluation is the basepoint.
  by
    apply Path.ext
    ext t
    change (Path.refl (underTopBasepoint E)) (Set.Icc.convexCombo 0 u t) =
      (Path.refl (underTopBasepoint E)) t
    simp

/-- Helper for Theorem 9.3.3: concatenating a constant path with a casted constant path leaves the
casted constant path unchanged. -/
private theorem reflTransCastRefl {X : Type*} [TopologicalSpace X] {x y : X} (h : y = x) :
    (Path.refl x).trans ((Path.refl x).cast rfl h) = (Path.refl x).cast rfl h := by
  -- Reassociate the cast across concatenation, then collapse the doubled constant path.
  simpa using
    (Path.cast_trans (Path.refl x) (Path.refl x) rfl rfl h).symm

/-- Helper for Theorem 9.3.3: the split lift of the constant relative path is constant. -/
private theorem actualFiberSplitReflEndpoint_val {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    (((homotopyFiberToActualFiber p).right.hom
      (actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u)).1) =
      (actualFiberBasepoint p).1 := by
  -- On the singleton slice, the split point is the based homotopy-fiber point.
  rw [actualFiberSplitPoint_refl]
  simpa [homotopyFiberToActualFiber] using
    congrArg Subtype.val (homotopyFiberToActualFiberFun_basepoint p)

private theorem actualFiberSplitLiftPath_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    actualFiberSplitLiftPath p (PathToSet.refl (actualFiberBasepoint p)) u =
      (Path.refl (actualFiberBasepoint p).1).cast rfl
        (actualFiberSplitReflEndpoint_val p u) := by
  -- Route correction: use the Chapter 8 basepoint-fixing property of the contraction lift instead
  -- of rewriting the split lift through more `PathToSet` transports.
  have hpoint := actualFiberSplitPoint_refl p u
  have hmem :
      actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u ∈
        basedBasepointSet (homotopyFiber p) := by
    rw [hpoint, basedBasepointSet]
    exact Set.mem_singleton _
  apply Path.ext
  ext t
  have hstage :
      (homotopyFiberContractionLift p).toContinuousMap
        (t, actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u) =
        underTopBasepoint E := by
    simpa [hpoint, homotopyFiberPointProjectionHom_apply, underTopBasepoint_homotopyFiber] using
      (homotopyFiberContractionLift p).eq_fst t hmem
  change (homotopyFiberContractionLift p).toContinuousMap
      (t, actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u) =
    (actualFiberBasepoint p).1
  simpa using hstage

/-- Helper for Theorem 9.3.3: on the singleton basepoint, the split-stage path stays constant. -/
private theorem actualFiberSplitReflPath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    (actualFiberSplitFrontPath p (PathToSet.refl (actualFiberBasepoint p)) u).trans
      (actualFiberSplitLiftPath p (PathToSet.refl (actualFiberBasepoint p)) u) =
      (Path.refl (actualFiberBasepoint p).1).cast rfl
        (actualFiberSplitReflEndpoint_val p u) := by
  -- Rewrite both factors to constant paths, then use the generic cast-stable constant-path
  -- concatenation normalization.
  rw [actualFiberSplitFrontPath_refl, actualFiberSplitLiftPath_refl]
  exact reflTransCastRefl (actualFiberSplitReflEndpoint_val p u)

@[simp] private theorem actualFiberSplitStageFamily_zero {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitStageFamilyMap p (γ, 0) = actualFiberRoundTripLeftUnitMap p γ := by
  -- Compare endpoint and path coordinates after normalizing the split-stage path at `u = 0`.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change (homotopyFiberToActualFiber p).right.hom (actualFiberSplitPoint p γ 0) =
      (loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).endpoint
    rw [loopToActualFiberRelativeMap_apply, actualFiberSplitPoint_zero]
    rfl
  · apply ContinuousMap.ext
    intro t
    change ((actualFiberSplitFrontPath p γ 0).trans (actualFiberSplitLiftPath p γ 0)).toContinuousMap t =
      (Path.delayReflLeft 0
        ((loopToActualFiberRelativeMap p (actualFiberRelativeToLoopMap p γ)).path)).toContinuousMap t
    rw [loopToActualFiberRelativeMap_apply, Path.delayReflLeft_zero]
    simpa [Path.cast] using
      congrArg (fun η : C(I, E.right) ↦ η t) <|
        congrArg Path.toContinuousMap (actualFiberSplitZeroPath_normalize p γ)

/-- Helper for Theorem 9.3.3: at `u = 1`, the split-stage family reaches the common midpoint map.
-/
@[simp] private theorem actualFiberSplitStageFamily_one {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberSplitStageFamilyMap p (γ, 1) = actualFiberRetractionPathToSetMap p γ :=
  -- Compare endpoint and path coordinates after rewriting the split stage into the shared
  -- Chapter 8 midpoint normal form.
  by
    apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
    refine Prod.ext ?_ ?_
    · exact actualFiberSplitPointOneEndpoint p γ
    · apply ContinuousMap.ext
      intro t
      change ((actualFiberSplitFrontPath p γ 1).trans (actualFiberSplitLiftPath p γ 1)).toContinuousMap t =
        (γ.path.trans
          ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).toContinuousMap t
      simpa [Path.cast] using
        congrArg (fun η : C(I, E.right) ↦ η t) <|
          congrArg Path.toContinuousMap (actualFiberSplitOnePath_normalize p γ)

/-- Helper for Theorem 9.3.3: the split-stage family fixes the singleton basepoint at every stage.
-/
private theorem actualFiberSplitStageFamily_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    actualFiberSplitStageFamilyMap p (PathToSet.refl (actualFiberBasepoint p), u) =
      PathToSet.refl (actualFiberBasepoint p) := by
  -- Both the split point and the concatenated path collapse to the chosen basepoint on the
  -- singleton-relative slice.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change (homotopyFiberToActualFiber p).right.hom
      (actualFiberSplitPoint p (PathToSet.refl (actualFiberBasepoint p)) u) = actualFiberBasepoint p
    simpa [actualFiberSplitPoint_refl, homotopyFiberToActualFiber] using
      homotopyFiberToActualFiberFun_basepoint p
  · apply ContinuousMap.ext
    intro t
    change
      ((actualFiberSplitFrontPath p (PathToSet.refl (actualFiberBasepoint p)) u).trans
        (actualFiberSplitLiftPath p (PathToSet.refl (actualFiberBasepoint p)) u)).toContinuousMap t =
      (Path.refl (actualFiberBasepoint p).1).toContinuousMap t
    simpa [Path.cast] using
      congrArg (fun η : C(I, E.right) ↦ η t) <|
        congrArg Path.toContinuousMap (actualFiberSplitReflPath_normalize p u)

/-- Helper for Theorem 9.3.3: the split-front and split-lift family deforms the left-unit normal
form to the common midpoint map relative to the constant path. -/
private def actualFiberSplitStageHomotopyRel {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    (actualFiberRoundTripLeftUnitMap p).HomotopyRel
      (actualFiberRetractionPathToSetMap p)
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) :=
  -- Package the bundled split-stage family after recording its zero, one, and singleton slices.
  pathToSetHomotopyRelSingletonOfFamilyMap p
    (actualFiberSplitStageFamilyMap p)
    (actualFiberSplitStageFamily_zero p)
    (actualFiberSplitStageFamily_one p)
    (actualFiberSplitStageFamily_refl p)

/-- Helper for Theorem 9.3.3: at `u = 0`, the endpoint-retraction tail family agrees with the
right-unit normal form. -/
private theorem actualFiberRetractionTailZeroPath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    γ.path.trans (actualFiberRetractionTailPath p γ 0) =
      (Path.delayReflRight 0 γ.path).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_zero p γ.endpoint)) := by
  -- Rewrite the truncated tail to the constant endpoint path, then compare the two concatenation
  -- formulas through the canonical `Path.cast_trans` bridge.
  rw [actualFiberRetractionTailPath_zero]
  rw [Path.delayReflRight_zero]
  simpa using
    (Path.cast_trans γ.path (Path.refl γ.endpoint.1) rfl rfl
      (congrArg Subtype.val (actualFiberRetractionFamily_zero p γ.endpoint))).symm

/-- Helper for Theorem 9.3.3: at `u = 0`, the endpoint-retraction tail family agrees with the
right-unit normal form. -/
@[simp] private theorem actualFiberRetractionTailStageFamily_zero {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRetractionTailStageFamilyMap p (γ, 0) = actualFiberRightUnitMap p γ := by
  -- Compare endpoint and path coordinates after the zero-stage tail is normalized to the
  -- right-unit path.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change actualFiberRetractionFamily p γ.endpoint 0 = γ.endpoint
    exact actualFiberRetractionFamily_zero p γ.endpoint
  · apply ContinuousMap.ext
    intro t
    change (γ.path.trans (actualFiberRetractionTailPath p γ 0)).toContinuousMap t =
      (Path.delayReflRight 0 γ.path).toContinuousMap t
    simpa [Path.cast] using
      congrArg (fun η : C(I, E.right) ↦ η t) <|
        congrArg Path.toContinuousMap (actualFiberRetractionTailZeroPath_normalize p γ)

/-- Helper for Theorem 9.3.3: evaluating the Chapter 8 endpoint-retraction family at the actual
fiber basepoint is constant. -/
private theorem actualFiberRetractionFamily_basepoint_eval {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    actualFiberRetractionFamily p (actualFiberBasepoint p) u = actualFiberBasepoint p := by
  -- The Chapter 8 retraction family is constant on the singleton basepoint subset of the actual
  -- fiber.
  simpa using
    congrArg (fun f : C(I, actualFiberSet p) ↦ f u) <|
      actualFiberRetractionFamily_rel p (actualFiberBasepoint p)
        (by simpa [basedBasepointSet, underTopBasepoint_actualFiber])

/-- Helper for Theorem 9.3.3: at `u = 1`, the truncated endpoint-retraction family reaches the
common midpoint map. -/
private theorem actualFiberRetractionTailOnePath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    γ.path.trans (actualFiberRetractionTailPath p γ 1) =
      (γ.path.trans ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_one p γ.endpoint)) := by
  -- Replace the truncated tail by the full Chapter 8 retraction path, then collapse the casted
  -- concatenation in one step.
  rw [actualFiberRetractionTailPath_one]
  simpa using
    (Path.cast_trans γ.path
      ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val) rfl rfl
      (congrArg Subtype.val (actualFiberRetractionFamily_one p γ.endpoint))).symm

/-- Helper for Theorem 9.3.3: the truncated endpoint-retraction path is constant on the singleton
basepoint. -/
private theorem actualFiberRetractionTailPath_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    actualFiberRetractionTailPath p (PathToSet.refl (actualFiberBasepoint p)) u =
      (Path.refl (actualFiberBasepoint p).1).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_basepoint_eval p u)) := by
  -- Every point of the truncated tail is an evaluation of the constant Chapter 8 retraction
  -- family at the actual-fiber basepoint.
  apply Path.ext
  ext t
  change (actualFiberRetractionFamily p (actualFiberBasepoint p)
      (Set.Icc.convexCombo 0 u t)).1 = (actualFiberBasepoint p).1
  simpa using
    congrArg Subtype.val (actualFiberRetractionFamily_basepoint_eval p
      (Set.Icc.convexCombo 0 u t))

/-- Helper for Theorem 9.3.3: on the singleton basepoint, the endpoint-retraction stage path stays
constant. -/
private theorem actualFiberRetractionTailReflPath_normalize {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    (Path.refl (actualFiberBasepoint p).1).trans
      (actualFiberRetractionTailPath p (PathToSet.refl (actualFiberBasepoint p)) u) =
      (Path.refl (actualFiberBasepoint p).1).cast rfl
        (congrArg Subtype.val (actualFiberRetractionFamily_basepoint_eval p u)) :=
  -- Rewrite the truncated tail to a casted constant path, then reuse the same generic
  -- constant-path concatenation normalization as in the split-stage singleton slice.
  by
    rw [actualFiberRetractionTailPath_refl]
    exact reflTransCastRefl (congrArg Subtype.val (actualFiberRetractionFamily_basepoint_eval p u))

/-- Helper for Theorem 9.3.3: at `u = 1`, the endpoint-retraction stage reaches the common
midpoint map. -/
@[simp] private theorem actualFiberRetractionTailStageFamily_one {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRetractionTailStageFamilyMap p (γ, 1) = actualFiberRetractionPathToSetMap p γ := by
  -- Compare endpoint and path coordinates after normalizing the truncated tail at `u = 1`.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change actualFiberRetractionFamily p γ.endpoint 1 =
      (actualFiberToHomotopyFiber p ≫ homotopyFiberToActualFiber p).right.hom γ.endpoint
    exact actualFiberRetractionFamily_one p γ.endpoint
  · apply ContinuousMap.ext
    intro t
    change (γ.path.trans (actualFiberRetractionTailPath p γ 1)).toContinuousMap t =
      (γ.path.trans
        ((actualFiberRetractionPath p γ.endpoint).map continuous_subtype_val)).toContinuousMap t
    simpa [Path.cast] using
      congrArg (fun η : C(I, E.right) ↦ η t) <|
        congrArg Path.toContinuousMap (actualFiberRetractionTailOnePath_normalize p γ)

/-- Helper for Theorem 9.3.3: the endpoint-retraction stage fixes the singleton basepoint at every
stage. -/
private theorem actualFiberRetractionTailStageFamily_refl {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (u : I) :
    actualFiberRetractionTailStageFamilyMap p (PathToSet.refl (actualFiberBasepoint p), u) =
      PathToSet.refl (actualFiberBasepoint p) := by
  -- Both the endpoint and the truncated tail collapse to the actual-fiber basepoint on the
  -- singleton-relative slice.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext ?_ ?_
  · change actualFiberRetractionFamily p (actualFiberBasepoint p) u = actualFiberBasepoint p
    exact actualFiberRetractionFamily_basepoint_eval p u
  · apply ContinuousMap.ext
    intro t
    change
      ((Path.refl (actualFiberBasepoint p).1).trans
        (actualFiberRetractionTailPath p (PathToSet.refl (actualFiberBasepoint p)) u)).toContinuousMap t =
      (Path.refl (actualFiberBasepoint p).1).toContinuousMap t
    simpa [Path.cast] using
      congrArg (fun η : C(I, E.right) ↦ η t) <|
        congrArg Path.toContinuousMap (actualFiberRetractionTailReflPath_normalize p u)

/-- Helper for Theorem 9.3.3: the truncated endpoint-retraction family deforms the right-unit
normal form to the common midpoint map relative to the constant path. -/
private def actualFiberRetractionTailStageHomotopyRel {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    (actualFiberRightUnitMap p).HomotopyRel
      (actualFiberRetractionPathToSetMap p)
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) :=
  -- Package the bundled endpoint-retraction family after recording its zero, one, and singleton
  -- slices.
  pathToSetHomotopyRelSingletonOfFamilyMap p
    (actualFiberRetractionTailStageFamilyMap p)
    (actualFiberRetractionTailStageFamily_zero p)
    (actualFiberRetractionTailStageFamily_one p)
    (actualFiberRetractionTailStageFamily_refl p)

/-- Helper for Theorem 9.3.3: at `u = 1`, the right-unit delay family recovers the identity map. -/
@[simp] private theorem actualFiberRightUnitFamily_one {E B : BasedSpace} (p : E ⟶ B)
    (γ : PathToSet (actualFiberSet p) (actualFiberBasepoint p).1) :
    actualFiberRightUnitFamilyMap p (γ, 1) = γ := by
  -- Compare endpoint and path coordinates; at `u = 1` the right delay is the original path.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro t
  change Path.delayReflRight 1 γ.path t = γ.path t
  simpa using
    congrArg (fun η : Path (actualFiberBasepoint p).1 γ.endpoint.1 ↦ η t)
      (Path.delayReflRight_one γ.path)

/-- Helper for Theorem 9.3.3: the right-unit delay family fixes the constant relative path at
every stage. -/
private theorem actualFiberRightUnitFamily_refl {E B : BasedSpace} (p : E ⟶ B) (θ : I) :
    actualFiberRightUnitFamilyMap p (PathToSet.refl (actualFiberBasepoint p), θ) =
      PathToSet.refl (actualFiberBasepoint p) := by
  -- Delaying the constant path on the right is still the constant path.
  apply (PathToSet.endpointAndPath_injective (A := actualFiberSet p) (x := actualFiberBasepoint p))
  refine Prod.ext rfl ?_
  apply ContinuousMap.ext
  intro t
  change Path.delayReflRight θ (Path.refl (actualFiberBasepoint p).1) t =
    (Path.refl (actualFiberBasepoint p).1) t
  simpa [delayReflRight_refl]

/-- Helper for Theorem 9.3.3: the right-unit normal form deforms to the identity relative to the
constant path. -/
private def actualFiberRightUnitHomotopyRel {E B : BasedSpace} (p : E ⟶ B) :
    (actualFiberRightUnitMap p).HomotopyRel
      (ContinuousMap.id (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1))
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) :=
  -- Package the bundled right-unit delay family as a singleton-relative homotopy.
  pathToSetHomotopyRelSingletonOfFamilyMap p
    (actualFiberRightUnitFamilyMap p)
    (fun _ ↦ rfl)
    (fun γ ↦ by
      simpa [ContinuousMap.id, id_def] using actualFiberRightUnitFamily_one p γ)
    (actualFiberRightUnitFamily_refl p)

/-- Helper for Theorem 9.3.3: the round-trip endomorphism on the relative path-space model should
be homotopic to the identity relative to the constant path at `actualFiberBasepoint p`. -/
private def actualFiberRelativeRoundTripHomotopyRel {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] :
    ((loopToActualFiberRelativeMap p).comp (actualFiberRelativeToLoopMap p)).HomotopyRel
      (ContinuousMap.id (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1))
      ({PathToSet.refl (actualFiberBasepoint p)} :
        Set (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1)) :=
  -- Route correction: instead of forcing a direct comparison between the strict round-trip and the
  -- identity on `PathToSet`, compose four small relative homotopies: left-unit normalization,
  -- split-stage deformation to the midpoint map, reversed retraction-tail deformation back to the
  -- identity-side normal form, and final right-unit normalization.
  (((actualFiberRoundTripLeftUnitHomotopyRel p).symm.trans
      (actualFiberSplitStageHomotopyRel p)).trans
      ((actualFiberRetractionTailStageHomotopyRel p).symm.trans
        (actualFiberRightUnitHomotopyRel p)))

/-- The induced map on the Chapter 9 relative-homotopy-group owner for the pair `(E, F)`, written
with codomain in the standard constant-loop model of `π_n(B)`. -/
def fibrationRelativeHomotopyGroupToLoopMap {E B : BasedSpace} (p : E ⟶ B) (n : ℕ+) :
    relativeHomotopyGroup n (actualFiberSet p) (actualFiberBasepoint p) →
      π_ ((n : ℕ) - 1) (Ω B.right (underTopBasepoint B))
        (Path.refl (underTopBasepoint B)) :=
  cast
    (congrArg
      (fun y ↦
        relativeHomotopyGroup n (actualFiberSet p) (actualFiberBasepoint p) →
          π_ ((n : ℕ) - 1) (Ω B.right (underTopBasepoint B)) y)
      (actualFiberRelativeToLoopMap_refl p))
    (homotopyGroupMap (actualFiberRelativeToLoopMap p) ((n : ℕ) - 1)
      (PathToSet.refl (actualFiberBasepoint p)))

/-- Theorem 9.3.3: for a based fibration `p : E ⟶ B`, the induced map from the relative homotopy
group of the pair `(E, F)` to the loop-space model of `π_n(B)` is bijective in every positive
degree `n`. Here `F = p⁻¹' {underTopBasepoint B}` is the actual fiber over the chosen basepoint,
and the codomain is the standard constant-loop model of the source target `π_n(B)`. -/
theorem fibrationRelativeHomotopyGroupToLoopMap_bijective {E B : BasedSpace} (p : E ⟶ B)
    [IsBasedFibration p] (n : ℕ+) :
    Function.Bijective (fibrationRelativeHomotopyGroupToLoopMap p n) := by
  let q : ℕ := ((n : ℕ) - 1)
  -- Rewrite the target map in the local transported-`π` API so the one-sided inverse algebra
  -- can be expressed by `homotopyGroupMapOverEq_comp`.
  change Function.Bijective
    (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
      (actualFiberRelativeToLoopMap_refl p) q)
  have hright :
      (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) q) ∘
        (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
          (loopToActualFiberRelativeMap_refl p) q) = id := by
    -- The strict right inverse on the continuous maps gives a strict right inverse after applying
    -- the transported homotopy-group functor.
    have hrightToIdMap :
        (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
            (actualFiberRelativeToLoopMap_refl p) q) ∘
          (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
            (loopToActualFiberRelativeMap_refl p) q) =
          homotopyGroupMapOverEq
            (ContinuousMap.id (Ω B.right (underTopBasepoint B)))
            rfl q := by
      calc
        (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
            (actualFiberRelativeToLoopMap_refl p) q) ∘
          (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
            (loopToActualFiberRelativeMap_refl p) q)
            =
            homotopyGroupMapOverEq
              ((actualFiberRelativeToLoopMap p).comp (loopToActualFiberRelativeMap p))
              (by
                show
                  (actualFiberRelativeToLoopMap p)
                      ((loopToActualFiberRelativeMap p) (Path.refl (underTopBasepoint B))) =
                    Path.refl (underTopBasepoint B)
                exact
                  actualFiberRelativeToLoopMap_rightInverse p (Path.refl (underTopBasepoint B)))
              q := by
                simpa using
                  (homotopyGroupMapOverEq_comp
                    (loopToActualFiberRelativeMap p)
                    (actualFiberRelativeToLoopMap p)
                    (loopToActualFiberRelativeMap_refl p)
                    (actualFiberRelativeToLoopMap_refl p) q)
        _ = homotopyGroupMapOverEq
              (ContinuousMap.id (Ω B.right (underTopBasepoint B)))
              rfl q := by
                -- Replace the composite by the strict identity coming from the pointwise right inverse.
                apply homotopyGroupMapOverEq_congr
                apply ContinuousMap.ext
                intro χ
                exact actualFiberRelativeToLoopMap_rightInverse p χ
    exact hrightToIdMap.trans <|
      by
        simpa using homotopyGroupMapOverEq_id (Path.refl (underTopBasepoint B)) q
  have hleft :
      (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
          (loopToActualFiberRelativeMap_refl p) q) ∘
        (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) q) = id := by
    -- The remaining geometric input is the singleton-relative round-trip homotopy on `PathToSet`.
    have hleftToIdMap :
        (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
            (loopToActualFiberRelativeMap_refl p) q) ∘
          (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
            (actualFiberRelativeToLoopMap_refl p) q) =
          homotopyGroupMapOverEq
            (ContinuousMap.id (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1))
            rfl q := by
      calc
        (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
            (loopToActualFiberRelativeMap_refl p) q) ∘
          (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
            (actualFiberRelativeToLoopMap_refl p) q)
            =
            homotopyGroupMapOverEq
              ((loopToActualFiberRelativeMap p).comp (actualFiberRelativeToLoopMap p))
              (by
                show
                  (loopToActualFiberRelativeMap p)
                      ((actualFiberRelativeToLoopMap p)
                        (PathToSet.refl (actualFiberBasepoint p))) =
                    PathToSet.refl (actualFiberBasepoint p)
                rw [actualFiberRelativeToLoopMap_refl p]
                exact loopToActualFiberRelativeMap_refl p)
              q := by
                simpa using
                  (homotopyGroupMapOverEq_comp
                    (actualFiberRelativeToLoopMap p)
                    (loopToActualFiberRelativeMap p)
                    (actualFiberRelativeToLoopMap_refl p)
                    (loopToActualFiberRelativeMap_refl p) q)
        _ = homotopyGroupMapOverEq
              (ContinuousMap.id (PathToSet (actualFiberSet p) (actualFiberBasepoint p).1))
              rfl q := by
                -- Route correction: the left inverse is not strict, so we invoke the dedicated
                -- singleton-relative homotopy comparison proved above.
                exact homotopyGroupMapOverEq_eq_of_homotopyRel_singleton
                  (actualFiberRelativeRoundTripHomotopyRel p)
                  (by
                    show
                      (loopToActualFiberRelativeMap p)
                          ((actualFiberRelativeToLoopMap p)
                            (PathToSet.refl (actualFiberBasepoint p))) =
                        PathToSet.refl (actualFiberBasepoint p)
                    rw [actualFiberRelativeToLoopMap_refl p]
                    exact loopToActualFiberRelativeMap_refl p)
                  rfl q
    exact hleftToIdMap.trans <|
      by
        simpa using homotopyGroupMapOverEq_id (PathToSet.refl (actualFiberBasepoint p)) q
  -- Package the two one-sided inverse identities into injectivity and surjectivity.
  let leftInv :
      Function.LeftInverse
        (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
          (loopToActualFiberRelativeMap_refl p) q)
        (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) q) := by
    intro x
    exact congrFun hleft x
  let rightInv :
      Function.RightInverse
        (homotopyGroupMapOverEq (loopToActualFiberRelativeMap p)
          (loopToActualFiberRelativeMap_refl p) q)
        (homotopyGroupMapOverEq (actualFiberRelativeToLoopMap p)
          (actualFiberRelativeToLoopMap_refl p) q) := by
    intro x
    exact congrFun hright x
  exact ⟨leftInv.injective, rightInv.surjective⟩
