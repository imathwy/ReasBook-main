import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_8.Comparison

open CategoryTheory
open scoped unitInterval Topology.Homotopy PathSpace

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced generic compact-open and loop-space homeomorphisms
-- such as `Homeomorph.curry`, but not a ready-made owner for `Ω F_f ≃ F_(Ωf)`. This file uses
-- the local Chapter 8 owners `homotopyFiber`, `loopBasedMap`, and `signedLoopBasedMap`.

/-- Projecting a loop in `F_f` to its `X`-coordinate gives a loop in `X`. -/
private def loopHomotopyFiberPointLoop {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    Ω X.right (underTopBasepoint X) :=
  (ω.map (TopCat.Hom.hom (homotopyFiberProjectionHom f)).continuous).cast
    (by
      rw [underTopBasepoint_homotopyFiber]
      exact HomotopyFiber.point_basepoint f)
    (by
      rw [underTopBasepoint_homotopyFiber]
      exact HomotopyFiber.point_basepoint f)

/-- Evaluating `loopHomotopyFiberPointLoop` at `t` recovers the `X`-coordinate of `ω t`. -/
private theorem loopHomotopyFiberPointLoop_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (t : I) :
    loopHomotopyFiberPointLoop f ω t = HomotopyFiber.point (ω t) := by
  -- The projected loop is defined by mapping `ω` along the homotopy-fiber projection.
  rfl

/-- The square `(t, s) ↦ HomotopyFiber.path (ω t) s` is continuous. -/
private theorem loopHomotopyFiberPathSquareContinuous {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    Continuous (fun p : I × I ↦ HomotopyFiber.path (ω p.1) p.2) := by
  -- First project the `Y`-path coordinate out of the homotopy fiber along the loop `ω`.
  have hpathCoord : Continuous fun z : HomotopyFiber f ↦ HomotopyFiber.path z := by
    simpa [HomotopyFiber.path] using
      (continuous_snd.comp
        (continuous_subtype_val :
          Continuous fun z : HomotopyFiber f ↦ z.1))
  have hpath : Continuous fun p : I × I ↦ HomotopyFiber.path (ω p.1) := by
    exact hpathCoord.comp (ω.continuous.comp continuous_fst)
  -- Then evaluate the resulting path at the second interval coordinate.
  exact (continuous_subtype_val.comp hpath).eval continuous_snd

/-- For fixed `s : I`, evaluating the path-coordinate of a loop in `F_f` at `s` gives a loop in
`Y`. -/
private theorem loopHomotopyFiberSwappedLoop_continuousToFun {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (s : I) :
    Continuous (fun t : I ↦ HomotopyFiber.path (ω t) s) := by
  -- Freeze the second coordinate of the continuous square.
  simpa using
    (loopHomotopyFiberPathSquareContinuous f ω).comp (continuous_id.prodMk continuous_const)

/-- The swapped loop starts at `underTopBasepoint Y`. -/
private theorem loopHomotopyFiberSwappedLoop_source {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (s : I) :
    (fun t : I ↦ HomotopyFiber.path (ω t) s) 0 = underTopBasepoint Y := by
  -- Evaluate at the source point of the loop `ω` and identify the homotopy-fiber basepoint.
  calc
    HomotopyFiber.path (ω 0) s = HomotopyFiber.path (HomotopyFiber.basepoint f) s := by
      have hω : ω 0 = HomotopyFiber.basepoint f := by
        convert ω.source' using 1
      exact congrArg (fun z ↦ HomotopyFiber.path z s) hω
    _ = underTopBasepoint Y := by
      rfl

/-- The swapped loop ends at `underTopBasepoint Y`. -/
private theorem loopHomotopyFiberSwappedLoop_target {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (s : I) :
    (fun t : I ↦ HomotopyFiber.path (ω t) s) 1 = underTopBasepoint Y := by
  -- The target point of the loop `ω` is the same homotopy-fiber basepoint.
  calc
    HomotopyFiber.path (ω 1) s = HomotopyFiber.path (HomotopyFiber.basepoint f) s := by
      have hω : ω 1 = HomotopyFiber.basepoint f := by
        convert ω.target' using 1
      exact congrArg (fun z ↦ HomotopyFiber.path z s) hω
    _ = underTopBasepoint Y := by
      rfl

/-- For fixed `s : I`, evaluating the path-coordinate of a loop in `F_f` at `s` gives a loop in
`Y`. -/
private def loopHomotopyFiberSwappedLoop {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (s : I) :
    Ω Y.right (underTopBasepoint Y) where
  toContinuousMap :=
    { toFun := fun t ↦ HomotopyFiber.path (ω t) s
      continuous_toFun := loopHomotopyFiberSwappedLoop_continuousToFun f ω s }
  source' := loopHomotopyFiberSwappedLoop_source f ω s
  target' := loopHomotopyFiberSwappedLoop_target f ω s

/-- The family of swapped loops varies continuously with the outer loop coordinate. -/
private theorem loopHomotopyFiberSwappedLoop_continuous {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    Continuous (fun s : I ↦ loopHomotopyFiberSwappedLoop f ω s) := by
  -- Forget the endpoint conditions and curry the continuous square in the remaining variable.
  rw [continuous_induced_rng]
  let swappedFamily : I → C(I, Y.right) := fun s ↦
    { toFun := fun t ↦ HomotopyFiber.path (ω t) s
      continuous_toFun := loopHomotopyFiberSwappedLoop_continuousToFun f ω s }
  have huncurry :
      Continuous (Function.uncurry fun s t ↦ swappedFamily s t) := by
    simpa [swappedFamily, Function.uncurry] using
      (loopHomotopyFiberPathSquareContinuous f ω).comp continuous_swap
  simpa [swappedFamily, loopHomotopyFiberSwappedLoop] using
    (ContinuousMap.continuous_of_continuous_uncurry swappedFamily huncurry)

/-- The swapped family of loops starts at the constant loop in `ΩY`. -/
private theorem loopHomotopyFiberSwappedPath_source {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    (fun s : I ↦ loopHomotopyFiberSwappedLoop f ω s) 0 =
      underTopBasepoint (Ωᵇ Y) := by
  -- At `s = 0` every path in the homotopy fiber is at the basepoint of `Y`.
  ext t
  simp [loopHomotopyFiberSwappedLoop, underTopBasepoint_loopBasedSpace]

/-- Swapping loop coordinates in a loop of `F_f` gives a path in `ΩY` starting at the constant
loop. -/
private def loopHomotopyFiberSwappedPath {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    PathSpace (underTopBasepoint (Ωᵇ Y)) :=
  PathSpace.mk
    { toFun := fun s ↦ loopHomotopyFiberSwappedLoop f ω s
      continuous_toFun := loopHomotopyFiberSwappedLoop_continuous f ω }
    (loopHomotopyFiberSwappedPath_source f ω)

/-- The endpoint of the swapped path is the loop induced by `f` on the projected loop in `X`. -/
private theorem loopHomotopyFiberSwappedPath_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    (loopBasedMap f).right.hom (loopHomotopyFiberPointLoop f ω) =
      (loopHomotopyFiberSwappedPath f ω).endpoint := by
  -- Evaluate the endpoint loop pointwise and use the defining equation of each homotopy-fiber
  -- point on the loop `ω`.
  apply Path.ext
  funext t
  calc
    (((loopBasedMap f).right.hom (loopHomotopyFiberPointLoop f ω)).1 t)
      = f.right.hom (loopHomotopyFiberPointLoop f ω t) := by
          simpa [loopBasedMapPath] using
            congrArg (fun χ : Ω Y.right (underTopBasepoint Y) ↦ χ t)
              (loopBasedMap_hom_apply f (loopHomotopyFiberPointLoop f ω))
    _ = f.right.hom (HomotopyFiber.point (ω t)) := by
          rw [loopHomotopyFiberPointLoop_apply]
    _ = HomotopyFiber.path (ω t) 1 := by
          change f.right.hom (HomotopyFiber.point (ω t)) =
            (HomotopyFiber.path (ω t)).endpoint
          exact HomotopyFiber.endpoint_eq (ω t)
    _ = ((loopHomotopyFiberSwappedPath f ω).endpoint).1 t := by
          rfl

/-- Swapping the two loop coordinates turns a loop in `F_f` into a point of `F_(Ωf)`. -/
private def loopHomotopyFiberToLoopFiber {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    HomotopyFiber (loopBasedMap f) :=
  HomotopyFiber.mk
    (loopHomotopyFiberPointLoop f ω)
    (loopHomotopyFiberSwappedPath f ω)
    (loopHomotopyFiberSwappedPath_endpoint f ω)

private abbrev loopFiberPointAsLoop {X Y : BasedSpace} {f : X ⟶ Y}
    (z : HomotopyFiber (loopBasedMap f)) :
    Ω X.right (underTopBasepoint X) :=
  HomotopyFiber.point z

private abbrev loopFiberPathAsLoop {X Y : BasedSpace} {f : X ⟶ Y}
    (z : HomotopyFiber (loopBasedMap f)) (s : I) :
    Ω Y.right (underTopBasepoint Y) :=
  HomotopyFiber.path z s

/-- The square `(s, t) ↦ loopFiberPathAsLoop z s t` is continuous. -/
private theorem loopFiberPathSquareContinuous {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) :
    Continuous (fun p : I × I ↦ loopFiberPathAsLoop z p.1 p.2) := by
  -- View `z.path` as a path in the loop space, then evaluate first in the path coordinate and
  -- then in the loop coordinate.
  have hloops : Continuous fun p : I × I ↦ loopFiberPathAsLoop z p.1 := by
    simpa [loopFiberPathAsLoop] using
      (PathSpace.toPath (HomotopyFiber.path z)).continuous.comp continuous_fst
  exact hloops.eval continuous_snd

/-- For fixed `t : I`, evaluating the path coordinate of a point in `F_(Ωf)` at `t` gives a path
in `Y` starting at `underTopBasepoint Y`. -/
private theorem loopFiberPathAt_continuousToFun {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) (t : I) :
    Continuous (fun s : I ↦ loopFiberPathAsLoop z s t) := by
  -- Freeze the second coordinate of the continuous square.
  simpa using
    (loopFiberPathSquareContinuous f z).comp (continuous_id.prodMk continuous_const)

/-- The path `loopFiberPathAt f z t` starts at the basepoint of `Y`. -/
private theorem loopFiberPathAt_source {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) (t : I) :
    (fun s : I ↦ loopFiberPathAsLoop z s t) 0 = underTopBasepoint Y := by
  -- The path coordinate of `z` starts at the constant loop in `ΩY`.
  simpa [loopFiberPathAsLoop, underTopBasepoint_loopBasedSpace] using
    congrArg (fun γ : Ω Y.right (underTopBasepoint Y) ↦ γ t)
      (PathSpace.source_eq (HomotopyFiber.path z))

/-- For fixed `t : I`, evaluating the path coordinate of a point in `F_(Ωf)` at `t` gives a path
in `Y` starting at `underTopBasepoint Y`. -/
private def loopFiberPathAt {X Y : BasedSpace} (f : X ⟶ Y) (z : HomotopyFiber (loopBasedMap f))
    (t : I) :
    PathSpace (underTopBasepoint Y) :=
  PathSpace.mk
    { toFun := fun s ↦ loopFiberPathAsLoop z s t
      continuous_toFun := loopFiberPathAt_continuousToFun f z t }
    (loopFiberPathAt_source f z t)

/-- The endpoint of `loopFiberPathAt f z t` is `f` applied to the `t`th point of the loop
underlying `z.point`. -/
private theorem loopFiberPathAt_endpoint {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f))
    (t : I) :
    f.right.hom (loopFiberPointAsLoop z t) = (loopFiberPathAt f z t).endpoint := by
  -- Evaluate the defining homotopy-fiber endpoint equation pointwise at `t`.
  simpa [loopFiberPointAsLoop, loopFiberPathAt, loopFiberPathAsLoop, loopBasedMap_hom_apply,
    PathSpace.endpoint] using
    congrArg (fun γ : Ω Y.right (underTopBasepoint Y) ↦ γ t) (HomotopyFiber.endpoint_eq z)

/-- Evaluating the `ΩY`-path of a point in `F_(Ωf)` pointwise produces a loop in `F_f`. -/
private theorem loopFiberToLoopHomotopyFiber_continuousToFun {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) :
    Continuous
      (fun t : I ↦
        HomotopyFiber.mk (loopFiberPointAsLoop z t) (loopFiberPathAt f z t)
          (loopFiberPathAt_endpoint f z t)) := by
  -- Build the point and path coordinates separately, then lift the resulting pair to the
  -- homotopy-fiber subtype.
  have hpath :
      Continuous fun t : I ↦ loopFiberPathAt f z t := by
    let pathFamily : I → C(I, Y.right) := fun t ↦
      { toFun := fun s ↦ loopFiberPathAsLoop z s t
        continuous_toFun := loopFiberPathAt_continuousToFun f z t }
    have huncurry :
        Continuous (Function.uncurry fun t s ↦ pathFamily t s) := by
      simpa [pathFamily, Function.uncurry] using
        (loopFiberPathSquareContinuous f z).comp continuous_swap
    exact (ContinuousMap.continuous_of_continuous_uncurry pathFamily huncurry).subtype_mk
      (fun t ↦ loopFiberPathAt_source f z t)
  have hpair :
      Continuous fun t : I ↦ (loopFiberPointAsLoop z t, loopFiberPathAt f z t) := by
    exact (HomotopyFiber.point z).continuous.prodMk hpath
  exact hpair.subtype_mk (fun t ↦ loopFiberPathAt_endpoint f z t)

/-- The reconstructed loop in `F_f` starts at the chosen basepoint of `homotopyFiber f`. -/
private theorem loopFiberToLoopHomotopyFiber_source {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) :
    (fun t : I ↦
      HomotopyFiber.mk (loopFiberPointAsLoop z t) (loopFiberPathAt f z t)
        (loopFiberPathAt_endpoint f z t)) 0 =
      underTopBasepoint (homotopyFiber f) := by
  -- At `t = 0`, the point loop and every loop in the path coordinate are both at their
  -- distinguished basepoints.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change loopFiberPointAsLoop z 0 = underTopBasepoint X
    exact (HomotopyFiber.point z).source'
  · apply Subtype.ext
    ext s
    change (loopFiberPathAsLoop z s) 0 = underTopBasepoint Y
    exact (loopFiberPathAsLoop z s).source'

/-- The reconstructed loop in `F_f` ends at the chosen basepoint of `homotopyFiber f`. -/
private theorem loopFiberToLoopHomotopyFiber_target {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) :
    (fun t : I ↦
      HomotopyFiber.mk (loopFiberPointAsLoop z t) (loopFiberPathAt f z t)
        (loopFiberPathAt_endpoint f z t)) 1 =
      underTopBasepoint (homotopyFiber f) := by
  -- The same coordinatewise argument at `t = 1` uses the endpoint condition of the loops.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change loopFiberPointAsLoop z 1 = underTopBasepoint X
    exact (HomotopyFiber.point z).target'
  · apply Subtype.ext
    ext s
    change (loopFiberPathAsLoop z s) 1 = underTopBasepoint Y
    exact (loopFiberPathAsLoop z s).target'

/-- Evaluating the `ΩY`-path of a point in `F_(Ωf)` pointwise produces a loop in `F_f`. -/
private def loopFiberToLoopHomotopyFiber {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) :
    Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) where
  toContinuousMap :=
    { toFun := fun t ↦
        HomotopyFiber.mk (loopFiberPointAsLoop z t) (loopFiberPathAt f z t)
          (loopFiberPathAt_endpoint f z t)
      continuous_toFun := loopFiberToLoopHomotopyFiber_continuousToFun f z }
  source' := loopFiberToLoopHomotopyFiber_source f z
  target' := loopFiberToLoopHomotopyFiber_target f z

/-- Reconstructing the `Y`-path coordinate from a swapped loop recovers the original path. -/
private theorem loopFiberPathAt_ofLoopHomotopyFiber {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (t : I) :
    loopFiberPathAt f (loopHomotopyFiberToLoopFiber f ω) t = HomotopyFiber.path (ω t) := by
  -- Both sides are packaged from the same square `(s ↦ HomotopyFiber.path (ω t) s)`.
  apply Subtype.ext
  ext s
  rfl

/-- The coordinate-swap function has the loop reconstruction above as a left inverse. -/
private theorem loopFiberToLoopHomotopyFiber_left_inv {X Y : BasedSpace} (f : X ⟶ Y) :
    Function.LeftInverse (loopFiberToLoopHomotopyFiber f) (loopHomotopyFiberToLoopFiber f) := by
  intro ω
  -- Equality of loops in the homotopy fiber is pointwise equality of their `X`- and `Y`-parts.
  ext t
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · simpa [loopFiberToLoopHomotopyFiber, loopHomotopyFiberToLoopFiber, loopFiberPointAsLoop] using
      loopHomotopyFiberPointLoop_apply f ω t
  · exact loopFiberPathAt_ofLoopHomotopyFiber f ω t

/-- Swapping the reconstructed loop of a point in `F_(Ωf)` recovers the original `ΩY`-loop at
each path parameter. -/
private theorem loopHomotopyFiberSwappedLoop_ofLoopFiber {X Y : BasedSpace} (f : X ⟶ Y)
    (z : HomotopyFiber (loopBasedMap f)) (s : I) :
    loopHomotopyFiberSwappedLoop f (loopFiberToLoopHomotopyFiber f z) s =
      loopFiberPathAsLoop z s := by
  -- The reconstructed loop was defined so that its path coordinate is exactly the stored loop.
  apply Path.ext
  funext t
  rfl

/-- The loop reconstruction function has coordinate swap as a left inverse. -/
private theorem loopFiberToLoopHomotopyFiber_right_inv {X Y : BasedSpace} (f : X ⟶ Y) :
    Function.RightInverse (loopFiberToLoopHomotopyFiber f) (loopHomotopyFiberToLoopFiber f) := by
  intro z
  -- Equality in the target homotopy fiber reduces to the point loop and the path in `ΩY`.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · apply Path.ext
    funext t
    change loopHomotopyFiberPointLoop f (loopFiberToLoopHomotopyFiber f z) t =
      loopFiberPointAsLoop z t
    rw [loopHomotopyFiberPointLoop_apply]
    simp [loopFiberToLoopHomotopyFiber, loopFiberPointAsLoop]
  · apply Subtype.ext
    ext s
    exact loopHomotopyFiberSwappedLoop_ofLoopFiber f z s

/-- Coordinate swap is continuous from `ΩF_f` to `F_(Ωf)`. -/
private theorem loopHomotopyFiberToLoopFiber_continuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (loopHomotopyFiberToLoopFiber f) := by
  -- The point coordinate is the ordinary induced loop map of the projection `F_f ⟶ X`.
  have hpoint :
      Continuous fun ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) ↦
        loopHomotopyFiberPointLoop f ω := by
    simpa [loopHomotopyFiberPointLoop, loopBasedMapPath, homotopyFiberProjection_hom_apply,
      homotopyFiberProjectionHom_apply] using loopBasedMapContinuous (homotopyFiberProjection f)
  -- Next package the doubly-curried `Y`-square as a continuous path-valued map.
  have hswappedLoopCoord :
      Continuous fun q : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) × I ↦
        (⟨fun t ↦ HomotopyFiber.path (q.1 t) q.2,
          loopHomotopyFiberSwappedLoop_continuousToFun f q.1 q.2⟩ : C(I, Y.right)) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    have hpathCoord :
        Continuous fun z : HomotopyFiber f ↦ HomotopyFiber.path z := by
      simpa [HomotopyFiber.path] using
        (continuous_snd.comp
          (continuous_subtype_val :
            Continuous fun z : HomotopyFiber f ↦ z.1))
    have huncurried :
        Continuous fun r :
            (Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) × I) × I ↦
          HomotopyFiber.path (r.1.1 r.2) r.1.2 := by
      have hpath :
          Continuous fun r :
              (Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) × I) × I ↦
            HomotopyFiber.path (r.1.1 r.2) := by
        exact hpathCoord.comp
          (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
      exact (continuous_subtype_val.comp hpath).eval (continuous_snd.comp continuous_fst)
    simpa [Function.uncurry] using huncurried
  have hswappedLoop :
      Continuous fun q : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) × I ↦
        loopHomotopyFiberSwappedLoop f q.1 q.2 := by
    rw [continuous_induced_rng]
    simpa [loopHomotopyFiberSwappedLoop] using hswappedLoopCoord
  have hswappedPathCoord :
      Continuous fun ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) ↦
        (⟨fun s ↦ loopHomotopyFiberSwappedLoop f ω s,
          loopHomotopyFiberSwappedLoop_continuous f ω⟩ :
          C(I, Ω Y.right (underTopBasepoint Y))) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simpa [Function.uncurry] using hswappedLoop
  have hswappedPath :
      Continuous fun ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) ↦
        loopHomotopyFiberSwappedPath f ω := by
    exact hswappedPathCoord.subtype_mk (fun ω ↦ loopHomotopyFiberSwappedPath_source f ω)
  -- Finally lift the continuous point/path pair into the homotopy-fiber subtype for `Ωf`.
  exact (hpoint.prodMk hswappedPath).subtype_mk (fun ω ↦ loopHomotopyFiberSwappedPath_endpoint f ω)

/-- Loop reconstruction is continuous from `F_(Ωf)` to `ΩF_f`. -/
private theorem loopFiberToLoopHomotopyFiber_continuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (loopFiberToLoopHomotopyFiber f) := by
  let liftPoint : HomotopyFiber (loopBasedMap f) × I → HomotopyFiber f := fun q ↦
    HomotopyFiber.mk (loopFiberPointAsLoop q.1 q.2) (loopFiberPathAt f q.1 q.2)
      (loopFiberPathAt_endpoint f q.1 q.2)
  have hliftPoint : Continuous liftPoint := by
    have hpointLoop :
        Continuous fun z : HomotopyFiber (loopBasedMap f) ↦ loopFiberPointAsLoop z := by
      simpa [loopFiberPointAsLoop, HomotopyFiber.point] using
        (continuous_fst.comp
          (continuous_subtype_val :
            Continuous fun z : HomotopyFiber (loopBasedMap f) ↦ z.1))
    -- The point coordinate is evaluation of the projected `ΩX`-loop.
    have houter :
        Continuous fun q : HomotopyFiber (loopBasedMap f) × I ↦ loopFiberPointAsLoop q.1 q.2 := by
      exact continuous_eval.comp
        ((hpointLoop.comp continuous_fst).prodMk continuous_snd)
    -- The path coordinate is obtained by currying the continuous three-variable `Y`-square.
    have hpath :
        Continuous fun q : HomotopyFiber (loopBasedMap f) × I ↦
          (loopFiberPathAt f q.1 q.2 : P[underTopBasepoint Y]) := by
      have hcoord :
          Continuous fun q : HomotopyFiber (loopBasedMap f) × I ↦
            (⟨fun s ↦ loopFiberPathAsLoop q.1 s q.2,
              loopFiberPathAt_continuousToFun f q.1 q.2⟩ : C(I, Y.right)) := by
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        have hpathCoord :
            Continuous fun z : HomotopyFiber (loopBasedMap f) ↦ HomotopyFiber.path z := by
          simpa [HomotopyFiber.path] using
            (continuous_snd.comp
              (continuous_subtype_val :
                Continuous fun z : HomotopyFiber (loopBasedMap f) ↦
                  z.1))
        have huncurried :
            Continuous fun r : (HomotopyFiber (loopBasedMap f) × I) × I ↦
              loopFiberPathAsLoop r.1.1 r.2 r.1.2 := by
          have hloop :
              Continuous fun r : (HomotopyFiber (loopBasedMap f) × I) × I ↦
                loopFiberPathAsLoop r.1.1 r.2 := by
            exact (continuous_subtype_val.comp
              (hpathCoord.comp (continuous_fst.comp continuous_fst))).eval continuous_snd
          exact hloop.eval (continuous_snd.comp continuous_fst)
        simpa [Function.uncurry, loopFiberPathAsLoop] using huncurried
      exact hcoord.subtype_mk (fun q ↦ loopFiberPathAt_source f q.1 q.2)
    exact (houter.prodMk hpath).subtype_mk (fun q ↦ loopFiberPathAt_endpoint f q.1 q.2)
  let liftPath : HomotopyFiber (loopBasedMap f) → C(I, HomotopyFiber f) := fun z ↦
    ⟨fun t ↦ liftPoint (z, t), hliftPoint.comp (continuous_const.prodMk continuous_id)⟩
  have hliftPath : Continuous liftPath := by
    -- Curry the continuous `(z, t)`-family into a path-valued map.
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    simpa [liftPoint, liftPath, Function.uncurry] using hliftPoint
  rw [continuous_induced_rng]
  simpa [loopFiberToLoopHomotopyFiber, liftPoint, liftPath] using hliftPath

/-- Helper for Lemma 8.6.8: for any based map `f`, interchanging the two loop coordinates gives a
homeomorphism `Ω F_f ≃ F_(Ωf)`, formalized as a homeomorphism between the loop space of the
homotopy fiber of `f` and the homotopy fiber of the induced loop map `loopBasedMap f`. -/
def loopHomotopyFiberHomeomorph {X Y : BasedSpace} (f : X ⟶ Y) :
    Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f)) ≃ₜ
      HomotopyFiber (loopBasedMap f) where
  toEquiv :=
    { toFun := loopHomotopyFiberToLoopFiber f
      invFun := loopFiberToLoopHomotopyFiber f
      left_inv := loopFiberToLoopHomotopyFiber_left_inv f
      right_inv := loopFiberToLoopHomotopyFiber_right_inv f }
  continuous_toFun := loopHomotopyFiberToLoopFiber_continuous f
  continuous_invFun := loopFiberToLoopHomotopyFiber_continuous f

/-- The coordinate-swap homeomorphism sends the constant loop in `F_f` to the canonical basepoint
of `F_(Ωf)`. -/
private theorem loopHomotopyFiberHomeomorph_basepoint {X Y : BasedSpace} (f : X ⟶ Y) :
    loopHomotopyFiberHomeomorph f (underTopBasepoint (Ωᵇ (homotopyFiber f))) =
      underTopBasepoint (homotopyFiber (loopBasedMap f)) := by
  -- Identify the inverse image of the basepoint, then use the proven right-inverse formula.
  have hbase :
      loopFiberToLoopHomotopyFiber f (underTopBasepoint (homotopyFiber (loopBasedMap f))) =
        underTopBasepoint (Ωᵇ (homotopyFiber f)) := by
    ext t
    apply Subtype.ext
    refine Prod.ext ?_ ?_
    · change loopFiberPointAsLoop (HomotopyFiber.basepoint (loopBasedMap f)) t =
        HomotopyFiber.point (Path.refl (underTopBasepoint (homotopyFiber f)) t)
      simp [loopFiberPointAsLoop]
    · apply Subtype.ext
      ext s
      rfl
  rw [← hbase]
  simpa [loopHomotopyFiberHomeomorph] using
    loopFiberToLoopHomotopyFiber_right_inv f (underTopBasepoint (homotopyFiber (loopBasedMap f)))

/-- The topological isomorphism underlying `loopHomotopyFiberHomeomorph` preserves the
distinguished basepoints. -/
private theorem loopHomotopyFiberIso_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (Ωᵇ (homotopyFiber f)).hom ≫
        (TopCat.isoOfHomeo (loopHomotopyFiberHomeomorph f)).hom =
      (homotopyFiber (loopBasedMap f)).hom := by
  -- Both maps out of the terminal object evaluate to the canonical basepoint of `F_(Ωf)`.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((Ωᵇ (homotopyFiber f)).hom ≫
        (TopCat.isoOfHomeo (loopHomotopyFiberHomeomorph f)).hom) x
      = loopHomotopyFiberHomeomorph f (underTopBasepoint (Ωᵇ (homotopyFiber f))) := rfl
    _ = (homotopyFiber (loopBasedMap f)).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
      rw [loopHomotopyFiberHomeomorph_basepoint]
      rfl
    _ = (homotopyFiber (loopBasedMap f)).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
      rw [hx]
    _ = (homotopyFiber (loopBasedMap f)).hom x := by
      simp

/-- In `BasedSpace`, the coordinate-swap homeomorphism gives an isomorphism
`Ωᵇ F_f ≅ F_(Ωf)`. -/
def loopHomotopyFiberIso {X Y : BasedSpace} (f : X ⟶ Y) :
    Ωᵇ (homotopyFiber f) ≅ homotopyFiber (loopBasedMap f) :=
  Under.isoMk
    (TopCat.isoOfHomeo (loopHomotopyFiberHomeomorph f))
    (loopHomotopyFiberIso_w f)

/-- The forward morphism of `loopHomotopyFiberIso` is induced by
`loopHomotopyFiberHomeomorph`. -/
private theorem loopHomotopyFiberIso_hom_right {X Y : BasedSpace} (f : X ⟶ Y) :
    (loopHomotopyFiberIso f).hom.right =
      (TopCat.isoOfHomeo (loopHomotopyFiberHomeomorph f)).hom := rfl

/-- Composing the coordinate-swap comparison with the projection `F_(Ωf) ⟶ ΩX` recovers the
underlying loop of the projection `F_f ⟶ X`; this is the raw coordinate-swap identity before the
sign convention built into `fiberSequenceGeneratedBy`. -/
private theorem loopHomotopyFiberHomeomorph_projection_raw {X Y : BasedSpace} (f : X ⟶ Y) :
    (loopHomotopyFiberIso f).hom ≫ homotopyFiberProjection (loopBasedMap f) =
      loopBasedMap (homotopyFiberProjection f) := by
  -- Both sides evaluate a loop in `F_f` by projecting to its `X`-coordinate.
  ext ω
  apply Path.ext
  funext t
  change loopHomotopyFiberPointLoop f ω t =
    (((loopBasedMap (homotopyFiberProjection f)).right.hom ω).1 t)
  rw [loopBasedMap_hom_apply]
  rfl

/-- The homeomorphism `ΩF_f ≃ₜ F_(Ωf)` identifies the outgoing map in the fiber sequence of
Definition 8.6.5 with the signed stage-4 loop map after postcomposing with loop reversal on `ΩX`,
so the comparison is compatible with `fiberSequenceGeneratedBy` on the correct sign layer. -/
theorem loopHomotopyFiberHomeomorph_projection {X Y : BasedSpace} (f : X ⟶ Y) :
    (loopHomotopyFiberIso f).hom ≫ homotopyFiberProjection (loopBasedMap f) ≫
        loopBasedSpaceNeg X =
      signedLoopBasedMap (homotopyFiberProjection f) := by
  -- This is just the raw projection identity followed by the chosen sign convention on loops.
  simpa [signedLoopBasedMap] using
    congrArg (fun k ↦ k ≫ loopBasedSpaceNeg X) (loopHomotopyFiberHomeomorph_projection_raw f)

/-- Evaluating `loopBasedMap f` at `t` applies `f` pointwise. -/
private theorem loopBasedMap_eval_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) (t : I) :
    (((loopBasedMap f).right.hom χ).1 t) = f.right.hom (χ t) := by
  -- The induced loop map is postcomposition by the underlying based map.
  rw [loopBasedMap_hom_apply]
  simp [loopBasedMapPath]

/-- Evaluating the signed loop of `homotopyFiberLoopInclusion f` pointwise produces the reversed
family of constant-point loops in `F_f`. -/
private theorem signedLoopHomotopyFiberLoopInclusion_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (t : I) :
    (((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ).1 t) =
      HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath (χ (unitInterval.symm t)))
        (homotopyFiberLoopInclusion_condition f (χ (unitInterval.symm t))) := by
  -- Evaluate the source loop at the reversed outer parameter and then apply the inclusion.
  simpa [signedLoopBasedMap, loopBasedSpaceNeg, loopBasedSpaceNegContinuousMap,
    loopBasedSpaceNegPath, homotopyFiberLoopInclusion_hom_apply] using
    (loopBasedMap_eval_apply (homotopyFiberLoopInclusion f) χ (unitInterval.symm t))

/-- The path coordinate of `loopHomotopyFiberToLoopFiber f ω` is the swapped evaluation
`(s, t) ↦ HomotopyFiber.path (ω t) s`. -/
private theorem loopHomotopyFiberToLoopFiber_path_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) (s t : I) :
    ((HomotopyFiber.path (loopHomotopyFiberToLoopFiber f ω) s).1 t) =
      HomotopyFiber.path (ω t) s := by
  -- The path field of `loopHomotopyFiberToLoopFiber` was defined by swapping the two parameters.
  rfl

/-- The forward map of `loopHomotopyFiberIso f` is `loopHomotopyFiberToLoopFiber f`. -/
private theorem loopHomotopyFiberIso_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (ω : Ω (HomotopyFiber f) (underTopBasepoint (homotopyFiber f))) :
    (loopHomotopyFiberIso f).hom.right.hom ω = loopHomotopyFiberToLoopFiber f ω := rfl

/-- The path coordinate of `homotopyFiberLoopInclusion f` is the input loop itself. -/
private theorem homotopyFiberLoopInclusion_path_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) (s : I) :
    HomotopyFiber.path ((homotopyFiberLoopInclusion f).right.hom χ) s = χ s := by
  -- The loop inclusion stores the given loop as the `Y`-path coordinate of the homotopy fiber.
  rw [homotopyFiberLoopInclusion_hom_apply]
  rfl

/-- Helper for Lemma 8.6.8: the point coordinate of the left composite is the constant
basepoint loop in `X`. -/
private theorem leftComposite_pointCoordinate_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (t : I) :
    ((HomotopyFiber.point
        (((signedLoopBasedMap (homotopyFiberLoopInclusion f) ≫
            (loopHomotopyFiberIso f).hom).right.hom χ))).1 t) =
      underTopBasepoint X := by
  -- First expose the coordinate-swap homeomorphism on the left composite.
  change
    ((HomotopyFiber.point
        ((loopHomotopyFiberIso f).hom.right.hom
          ((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ))).1 t) =
      underTopBasepoint X
  rw [loopHomotopyFiberIso_hom_apply]
  -- Then project the `X`-coordinate of the resulting loop in `F_f`.
  change
    loopHomotopyFiberPointLoop f
        ((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ) t =
      underTopBasepoint X
  rw [loopHomotopyFiberPointLoop_apply]
  change
    HomotopyFiber.point
        (((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ).1 t) =
      underTopBasepoint X
  rw [signedLoopHomotopyFiberLoopInclusion_apply]
  rfl

/-- Helper for Lemma 8.6.8: the point coordinate of the right composite is the constant
basepoint loop in `X`. -/
private theorem rightComposite_pointCoordinate_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (t : I) :
    ((HomotopyFiber.point
        (((signedLoopBasedMap (𝟙 (Ωᵇ Y)) ≫ doubleLoopCoordinateSwap Y ≫
            homotopyFiberLoopInclusion (loopBasedMap f)).right.hom χ))).1 t) =
      underTopBasepoint X := by
  -- Expose the final loop-fiber inclusion on the right composite.
  change
    ((HomotopyFiber.point
        ((homotopyFiberLoopInclusion (loopBasedMap f)).right.hom
          ((doubleLoopCoordinateSwap Y).right.hom
            ((signedLoopBasedMap (𝟙 (Ωᵇ Y))).right.hom χ)))).1 t) =
      underTopBasepoint X
  rw [homotopyFiberLoopInclusion_hom_apply]
  rfl

/-- The left composite has path coordinate `(s, t) ↦ χ (unitInterval.symm t) s`. -/
private theorem leftComposite_pathCoordinate_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s t : I) :
    ((HomotopyFiber.path
        (((signedLoopBasedMap (homotopyFiberLoopInclusion f) ≫
            (loopHomotopyFiberIso f).hom).right.hom χ))
        s).1 t) =
      χ (unitInterval.symm t) s := by
  -- Rewrite the target value through the explicit forward map of `loopHomotopyFiberIso`.
  change ((HomotopyFiber.path
      ((loopHomotopyFiberIso f).hom.right.hom
        ((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ))
      s).1 t) =
    χ (unitInterval.symm t) s
  -- Then expose the swapped path coordinate and the pointwise formula for the signed inclusion.
  rw [loopHomotopyFiberIso_hom_apply, loopHomotopyFiberToLoopFiber_path_apply]
  change
    HomotopyFiber.path
        (((signedLoopBasedMap (homotopyFiberLoopInclusion f)).right.hom χ).1 t) s =
      χ (unitInterval.symm t) s
  rw [signedLoopHomotopyFiberLoopInclusion_apply]
  rfl

/-- The source-corrected right composite has path coordinate
`(s, t) ↦ χ (unitInterval.symm t) s`. -/
private theorem rightComposite_pathCoordinate_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s t : I) :
    ((HomotopyFiber.path
        (((signedLoopBasedMap (𝟙 (Ωᵇ Y)) ≫ doubleLoopCoordinateSwap Y ≫
            homotopyFiberLoopInclusion (loopBasedMap f)).right.hom
            χ))
        s).1 t) =
      χ (unitInterval.symm t) s := by
  -- First expose the stored outer loop in `F_(Ωf)` after the signed coordinate swap on `Ω²Y`.
  change ((HomotopyFiber.path
      ((homotopyFiberLoopInclusion (loopBasedMap f)).right.hom
        ((doubleLoopCoordinateSwap Y).right.hom
          ((signedLoopBasedMap (𝟙 (Ωᵇ Y))).right.hom χ)))
      s).1 t) =
    χ (unitInterval.symm t) s
  rw [homotopyFiberLoopInclusion_path_apply]
  -- Then evaluate the signed source loop at the swapped coordinates.
  change ((((doubleLoopCoordinateSwap Y).right.hom
      ((signedLoopBasedMap (𝟙 (Ωᵇ Y))).right.hom χ)).1 s).1 t) =
    χ (unitInterval.symm t) s
  rw [doubleLoopCoordinateSwap_hom_apply]
  change ((((signedLoopBasedMap (𝟙 (Ωᵇ Y))).right.hom χ).1 t).1 s) =
    χ (unitInterval.symm t) s
  simpa [signedLoopBasedMap, loopBasedSpaceNeg, loopBasedSpaceNegContinuousMap,
    loopBasedSpaceNegPath] using
    congrArg (fun γ : Ω Y.right (underTopBasepoint Y) ↦ γ s)
      (loopBasedMap_eval_apply (𝟙 (Ωᵇ Y)) χ (unitInterval.symm t))

/-- Lemma 8.6.8. The coordinate-swap comparison identifies the `Ω²Y ⟶ ΩF_f` map in the fiber
sequence of `f` with the loop-fiber inclusion for `Ωf` after the source-side signed coordinate
swap coming from interchanging the loop coordinates. -/
theorem loopHomotopyFiberHomeomorph_loopInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    signedLoopBasedMap (homotopyFiberLoopInclusion f) ≫ (loopHomotopyFiberIso f).hom =
      signedLoopBasedMap (𝟙 (Ωᵇ Y)) ≫ doubleLoopCoordinateSwap Y ≫
        homotopyFiberLoopInclusion (loopBasedMap f) := by
  -- Compare the two composites pointwise on a double loop `χ`.
  ext χ
  -- Equality in `F_(Ωf)` reduces to equality of the point loop and the `ΩY`-path coordinate.
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · -- Both point coordinates are the constant loop at `underTopBasepoint X`.
    apply Path.ext
    funext t
    exact
      (leftComposite_pointCoordinate_apply f χ t).trans
        (rightComposite_pointCoordinate_apply f χ t).symm
  · -- Both path coordinates normalize to the same swapped evaluation of `χ`.
    apply Subtype.ext
    ext s
    apply Path.ext
    funext t
    change
      ((HomotopyFiber.path
          (((signedLoopBasedMap (homotopyFiberLoopInclusion f) ≫
              (loopHomotopyFiberIso f).hom).right.hom χ))
          s).1 t) =
        ((HomotopyFiber.path
          (((signedLoopBasedMap (𝟙 (Ωᵇ Y)) ≫ doubleLoopCoordinateSwap Y ≫
              homotopyFiberLoopInclusion (loopBasedMap f)).right.hom χ))
          s).1 t)
    rw [leftComposite_pathCoordinate_apply, rightComposite_pathCoordinate_apply]
