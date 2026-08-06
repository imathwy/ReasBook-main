import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1

open CategoryTheory Limits
open scoped Topology.Homotopy

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `LoopSpace` as mathlib's canonical owner for
-- loops, and the verified local Chapter 8 owners here are `PathSpace` and `HomotopyFiber`.

universe u

/-- The based loop space of a based topological space `Y`. -/
abbrev loopBasedSpace (Y : BasedSpace) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (Path.refl (underTopBasepoint Y))))

notation "Ωᵇ " Y:max => loopBasedSpace Y

/-- The chosen basepoint of `Ωᵇ Y` is the constant loop at `underTopBasepoint Y`. -/
@[simp] theorem underTopBasepoint_loopBasedSpace (Y : BasedSpace) :
    underTopBasepoint (Ωᵇ Y) = Path.refl (underTopBasepoint Y) := rfl

/-- Pairing the basepoint of `X` with a loop in `Y` satisfies the defining equation of
`HomotopyFiber f`. -/
theorem homotopyFiberLoopInclusion_condition {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    f.right.hom (underTopBasepoint X) = (PathSpace.ofPath χ).endpoint := by
  calc
    f.right.hom (underTopBasepoint X)
      = (PathSpace.basepoint (underTopBasepoint Y)).endpoint := HomotopyFiber.basepoint_condition f
    _ = (PathSpace.ofPath χ).endpoint := by simp

/-- The raw function `χ ↦ (underTopBasepoint X, χ)` landing in `HomotopyFiber f`. -/
def homotopyFiberLoopInclusionFun {X Y : BasedSpace} (f : X ⟶ Y) :
    Ω Y.right (underTopBasepoint Y) → HomotopyFiber f :=
  fun χ ↦
    HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
      (homotopyFiberLoopInclusion_condition f χ)

/-- The raw inclusion function sends `χ` to the pair `(underTopBasepoint X, χ)`. -/
@[simp] theorem homotopyFiberLoopInclusionFun_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    homotopyFiberLoopInclusionFun f χ =
      HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
        (homotopyFiberLoopInclusion_condition f χ) := rfl

/-- Helper for Definition 8.6.4: forgetting the terminal endpoint sends a loop continuously into
`P[underTopBasepoint Y]`. -/
theorem loopToPathSpaceContinuous {Y : BasedSpace} :
    Continuous (fun χ : Ω Y.right (underTopBasepoint Y) ↦ PathSpace.ofPath χ) := by
  -- The loop-to-path-space map is the canonical lift of the induced-domain forgetful map.
  simpa [PathSpace.ofPath, PathSpace.mk] using
    (continuous_induced_dom :
      Continuous fun χ : Ω Y.right (underTopBasepoint Y) ↦ χ.toContinuousMap).subtype_mk
      (fun χ ↦ χ.source')

/-- Helper for Definition 8.6.4: pairing a loop with the fixed basepoint of `X` is continuous as
a map into `X.right × P[underTopBasepoint Y]`. -/
theorem homotopyFiberLoopInclusionPairContinuous {X Y : BasedSpace} :
    Continuous
      (fun χ : Ω Y.right (underTopBasepoint Y) ↦
        (underTopBasepoint X, PathSpace.ofPath χ)) := by
  -- Continuity reduces to continuity of the loop coordinate because the point of `X` is constant.
  exact Continuous.prodMk continuous_const loopToPathSpaceContinuous

/-- Definition 8.6.4. The inclusion sending a loop `χ` to the pair
`(underTopBasepoint X, χ)` is continuous as a map into `HomotopyFiber f`. -/
theorem homotopyFiberLoopInclusionContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous (homotopyFiberLoopInclusionFun f) := by
  -- First build the continuous product map, then lift it into the homotopy-fiber subtype.
  simpa [homotopyFiberLoopInclusionFun] using
    (homotopyFiberLoopInclusionPairContinuous (X := X) (Y := Y)).subtype_mk
      (fun χ ↦ homotopyFiberLoopInclusion_condition f χ)

/-- The continuous map underlying the inclusion of loops into the homotopy fiber. -/
def homotopyFiberLoopInclusionContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(Ω Y.right (underTopBasepoint Y), HomotopyFiber f) :=
  { toFun := homotopyFiberLoopInclusionFun f
    continuous_toFun := homotopyFiberLoopInclusionContinuous f }

/-- The underlying continuous map sends the constant loop at `underTopBasepoint Y` to the
canonical basepoint of `homotopyFiber f`. -/
theorem homotopyFiberLoopInclusion_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (Ωᵇ Y).hom ≫ TopCat.ofHom (homotopyFiberLoopInclusionContinuousMap f) =
      (homotopyFiber f).hom := by
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((Ωᵇ Y).hom ≫ TopCat.ofHom (homotopyFiberLoopInclusionContinuousMap f)) x
        = homotopyFiberLoopInclusionFun f (Path.refl (underTopBasepoint Y)) := rfl
    _ = (homotopyFiber f).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = (homotopyFiber f).hom (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x)) := by
        rw [hx]
    _ = (homotopyFiber f).hom x := by simp

/-- Helper for Definition 8.6.4: the inclusion `ι : Ω Y ⟶ F_f` packaged as a based-space
morphism `Ωᵇ Y ⟶ homotopyFiber f`. It sends a loop `χ` to the pair
`(underTopBasepoint X, χ)`, realized in `HomotopyFiber f` as the basepoint of `X` together with
the same loop viewed via `PathSpace.ofPath` as an element of
`PathSpace (underTopBasepoint Y)`. -/
def homotopyFiberLoopInclusion {X Y : BasedSpace} (f : X ⟶ Y) :
    Ωᵇ Y ⟶ homotopyFiber f :=
  Under.homMk
    (TopCat.ofHom (homotopyFiberLoopInclusionContinuousMap f))
    (homotopyFiberLoopInclusion_w f)

/-- The underlying map of `homotopyFiberLoopInclusion f` sends `χ` to the pair
`(underTopBasepoint X, χ)`. -/
@[simp] theorem homotopyFiberLoopInclusion_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω Y.right (underTopBasepoint Y)) :
    (homotopyFiberLoopInclusion f).right.hom χ =
      HomotopyFiber.mk (underTopBasepoint X) (PathSpace.ofPath χ)
        (homotopyFiberLoopInclusion_condition f χ) := rfl
