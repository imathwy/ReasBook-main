import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_5

open CategoryTheory
open scoped unitInterval Topology.Homotopy PathSpace

noncomputable section

private theorem doubleLoopCoordinateSwapSquareContinuous {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) :
    Continuous (fun p : I × I ↦ χ p.2 p.1) := by
  exact (χ.continuous.comp continuous_snd).eval continuous_fst

private theorem doubleLoopCoordinateSwapLoop_continuousToFun {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s : I) :
    Continuous (fun t : I ↦ χ t s) := by
  simpa using
    (doubleLoopCoordinateSwapSquareContinuous χ).comp (continuous_const.prodMk continuous_id)

private theorem doubleLoopCoordinateSwapLoop_source {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s : I) :
    (fun t : I ↦ χ t s) 0 = underTopBasepoint Y := by
  simpa [underTopBasepoint_loopBasedSpace] using
    congrArg (fun γ : Ω Y.right (underTopBasepoint Y) ↦ γ s) χ.source'

private theorem doubleLoopCoordinateSwapLoop_target {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s : I) :
    (fun t : I ↦ χ t s) 1 = underTopBasepoint Y := by
  simpa [underTopBasepoint_loopBasedSpace] using
    congrArg (fun γ : Ω Y.right (underTopBasepoint Y) ↦ γ s) χ.target'

private def doubleLoopCoordinateSwapLoop {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s : I) :
    Ω Y.right (underTopBasepoint Y) where
  toContinuousMap :=
    { toFun := fun t ↦ χ t s
      continuous_toFun := doubleLoopCoordinateSwapLoop_continuousToFun χ s }
  source' := doubleLoopCoordinateSwapLoop_source χ s
  target' := doubleLoopCoordinateSwapLoop_target χ s

private theorem doubleLoopCoordinateSwap_continuous {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) :
    Continuous (fun s : I ↦ doubleLoopCoordinateSwapLoop χ s) := by
  rw [continuous_induced_rng]
  let swappedFamily : I → C(I, Y.right) := fun s ↦
    { toFun := fun t ↦ χ t s
      continuous_toFun := doubleLoopCoordinateSwapLoop_continuousToFun χ s }
  have huncurry :
      Continuous (Function.uncurry fun s t ↦ swappedFamily s t) := by
    simpa [swappedFamily, Function.uncurry] using
      doubleLoopCoordinateSwapSquareContinuous χ
  simpa [swappedFamily, doubleLoopCoordinateSwapLoop] using
    (ContinuousMap.continuous_of_continuous_uncurry swappedFamily huncurry)

private theorem doubleLoopCoordinateSwap_source {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) :
    (fun s : I ↦ doubleLoopCoordinateSwapLoop χ s) 0 = underTopBasepoint (Ωᵇ Y) := by
  ext t
  simp [doubleLoopCoordinateSwapLoop, underTopBasepoint_loopBasedSpace]

private theorem doubleLoopCoordinateSwap_target {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) :
    (fun s : I ↦ doubleLoopCoordinateSwapLoop χ s) 1 = underTopBasepoint (Ωᵇ Y) := by
  ext t
  simp [doubleLoopCoordinateSwapLoop, underTopBasepoint_loopBasedSpace]

private def doubleLoopCoordinateSwapFun {Y : BasedSpace} :
    Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)) →
      Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))
  | χ =>
      { toContinuousMap :=
          { toFun := fun s ↦ doubleLoopCoordinateSwapLoop χ s
            continuous_toFun := doubleLoopCoordinateSwap_continuous χ }
        source' := doubleLoopCoordinateSwap_source χ
        target' := doubleLoopCoordinateSwap_target χ }

private theorem doubleLoopCoordinateSwapContinuous {Y : BasedSpace} :
    Continuous (@doubleLoopCoordinateSwapFun Y) := by
  rw [continuous_induced_rng]
  let swappedFamily :
      Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)) →
        C(I, Ω Y.right (underTopBasepoint Y)) := fun χ ↦
      { toFun := fun s ↦ doubleLoopCoordinateSwapLoop χ s
        continuous_toFun := doubleLoopCoordinateSwap_continuous χ }
  have huncurry :
      Continuous (Function.uncurry fun χ s ↦ swappedFamily χ s) := by
    rw [continuous_induced_rng]
    let swappedSquare :
        Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)) × I →
          C(I, Y.right) := fun q ↦
        { toFun := fun t ↦ q.1 t q.2
          continuous_toFun := doubleLoopCoordinateSwapLoop_continuousToFun q.1 q.2 }
    have hsquare :
        Continuous (Function.uncurry fun q t ↦ swappedSquare q t) := by
      have houter :
          Continuous fun r :
              (Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)) × I) × I ↦
            r.1.1 r.2 := by
        exact continuous_eval.comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
      have hsquare' :
          Continuous fun r :
              (Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)) × I) × I ↦
            r.1.1 r.2 r.1.2 := by
        exact houter.eval (continuous_snd.comp continuous_fst)
      simpa [swappedSquare, Function.uncurry] using hsquare'
    simpa [swappedFamily, swappedSquare, Function.uncurry, doubleLoopCoordinateSwapLoop] using
      (ContinuousMap.continuous_of_continuous_uncurry swappedSquare hsquare)
  simpa [doubleLoopCoordinateSwapFun, swappedFamily] using
    (ContinuousMap.continuous_of_continuous_uncurry swappedFamily huncurry)

private def doubleLoopCoordinateSwapContinuousMap (Y : BasedSpace) :
    C(Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y)),
      Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) :=
  { toFun := @doubleLoopCoordinateSwapFun Y
    continuous_toFun := doubleLoopCoordinateSwapContinuous }

private theorem doubleLoopCoordinateSwap_w (Y : BasedSpace) :
    (Ωᵇ (Ωᵇ Y)).hom ≫ TopCat.ofHom (doubleLoopCoordinateSwapContinuousMap Y) =
      (Ωᵇ (Ωᵇ Y)).hom := by
  ext x s t
  rfl

/-- The based self-map of `Ω²Y` that swaps the two loop coordinates. -/
def doubleLoopCoordinateSwap (Y : BasedSpace) : Ωᵇ (Ωᵇ Y) ⟶ Ωᵇ (Ωᵇ Y) :=
  Under.homMk
    (TopCat.ofHom (doubleLoopCoordinateSwapContinuousMap Y))
    (doubleLoopCoordinateSwap_w Y)

/-- Evaluating `doubleLoopCoordinateSwap Y` swaps the two loop parameters. -/
theorem doubleLoopCoordinateSwap_hom_apply {Y : BasedSpace}
    (χ : Ω (Ω Y.right (underTopBasepoint Y)) (underTopBasepoint (Ωᵇ Y))) (s t : I) :
    ((((doubleLoopCoordinateSwap Y).right.hom χ).1 s).1 t) = χ t s := by
  rfl
