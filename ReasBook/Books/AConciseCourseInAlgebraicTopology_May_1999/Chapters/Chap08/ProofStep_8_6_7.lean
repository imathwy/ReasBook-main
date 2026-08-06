import Mathlib.Topology.Homotopy.Path
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap06.Reformulation_6_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_1

open CategoryTheory
open scoped PathSpace unitInterval

noncomputable section

/- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopy.evalAt` turns a homotopy
`const ~ f ∘ g` into pointwise paths. Chapter 8 already packages the based relative homotopy
relation as `HRel[Z]`, the target path space as `PathSpace`, and the pullback owner as
`homotopyFiber f`. -/
section

variable {Z X Y : BasedSpace} {f : X ⟶ Y} (g : Z ⟶ X)
variable (H : (constantBasedMap Z Y).right.hom HRel[Z] (g ≫ f).right.hom)

/-- The pointwise track of a nullhomotopy of `g ≫ f` starts at the basepoint of `Y`. -/
theorem homotopyFiberLiftPathPoint_source (z : Z.right) :
    (H.toHomotopy.evalAt z) 0 = underTopBasepoint Y := by
  -- Evaluate the homotopy at time `0`, where it agrees with the constant map.
  simpa [ContinuousMap.Homotopy.evalAt, constantBasedMap] using H.toHomotopy.apply_zero z

/-- The pointwise track of a nullhomotopy of `g ≫ f` gives a path in `Y` starting at the
basepoint. -/
def homotopyFiberLiftPathPoint (z : Z.right) :
    P[underTopBasepoint Y] :=
  PathSpace.ofPath (H.toHomotopy.evalAt z)

/-- The endpoint of the path determined by the nullhomotopy at `z` is `f (g z)`. -/
theorem homotopyFiberLiftPathPoint_endpoint (z : Z.right) :
    f.right.hom (g.right.hom z) = (homotopyFiberLiftPathPoint g H z).endpoint := by
  -- Evaluate the homotopy at time `1`, where it agrees with the composite `g ≫ f`.
  rw [homotopyFiberLiftPathPoint, PathSpace.endpoint_ofPath]
  simp [ContinuousMap.comp_apply]

/-- The path assignment associated to a nullhomotopy is continuous. -/
theorem homotopyFiberLiftPathContinuous :
    Continuous (homotopyFiberLiftPathPoint g H) := by
  -- First regard the nullhomotopy as a continuous map into the ambient path space `C(I, Y)`.
  have hzero :
      ∀ z : Z.right, H.toHomotopy.toPathSpaceMap z 0 = underTopBasepoint Y := by
    intro z
    have hzero' :
        H.toHomotopy.toPathSpaceMap z 0 = (constantBasedMap Z Y).right.hom z := by
      exact
        ContinuousMap.congr_fun H.toHomotopy.pathSpaceEvalAtZero_comp_toPathSpaceMap z
    have hconst : (constantBasedMap Z Y).right.hom z = underTopBasepoint Y := by
      rfl
    rw [← hconst]
    exact hzero'
  -- Then lift once into the subtype `P[underTopBasepoint Y]`.
  simpa [homotopyFiberLiftPathPoint, PathSpace.ofPath, PathSpace.mk,
      ContinuousMap.Homotopy.toPathSpaceMap_apply, ContinuousMap.Homotopy.evalAt] using
    H.toHomotopy.toPathSpaceMap.continuous.subtype_mk hzero

/-- Helper for ProofStep 8.6.7: the nullhomotopy defines a continuous map `Z → PY` by
sending `z` to the path `t ↦ H(t, z)`. -/
def homotopyFiberLiftPathContinuousMap :
    C(Z.right, P[underTopBasepoint Y]) :=
  { toFun := homotopyFiberLiftPathPoint g H
    continuous_toFun := homotopyFiberLiftPathContinuous g H }

/-- Helper for ProofStep 8.6.7: the nullhomotopy defines the corresponding map
`Z.right ⟶ TopCat.of P[underTopBasepoint Y]`. -/
def homotopyFiberLiftPath :
    Z.right ⟶ TopCat.of P[underTopBasepoint Y] :=
  TopCat.ofHom (homotopyFiberLiftPathContinuousMap g H)

/-- Evaluating the lifted path map returns the pointwise path determined by the nullhomotopy. -/
@[simp] theorem homotopyFiberLiftPath_apply (z : Z.right) :
    homotopyFiberLiftPath g H z = homotopyFiberLiftPathPoint g H z := rfl

/-- Pairing `g z` with the nullhomotopy path at `z` gives a point of `HomotopyFiber f`. -/
def homotopyFiberLiftPoint (z : Z.right) :
    HomotopyFiber f :=
  HomotopyFiber.mk (g.right.hom z) (homotopyFiberLiftPathPoint g H z)
    (homotopyFiberLiftPathPoint_endpoint g H z)

/-- The lifted point of `HomotopyFiber f` has `X`-coordinate `g z`. -/
@[simp] theorem homotopyFiberLiftPoint_point (z : Z.right) :
    (homotopyFiberLiftPoint g H z).point = g.right.hom z := by
  simp [homotopyFiberLiftPoint]

/-- The lifted point of `HomotopyFiber f` has path coordinate given by the nullhomotopy at `z`.
-/
@[simp] theorem homotopyFiberLiftPoint_path (z : Z.right) :
    (homotopyFiberLiftPoint g H z).path = homotopyFiberLiftPathPoint g H z := by
  simp [homotopyFiberLiftPoint]

/-- The pointwise pairing of `g` with the nullhomotopy path is continuous. -/
theorem homotopyFiberLiftContinuous :
    Continuous (homotopyFiberLiftPoint g H) := by
  -- Pair the continuous point coordinate with the continuous path coordinate.
  simpa [homotopyFiberLiftPoint, HomotopyFiber.mk] using
    (g.right.hom.continuous.prodMk (homotopyFiberLiftPathContinuous g H)).subtype_mk
      (homotopyFiberLiftPathPoint_endpoint g H)

/-- Helper for ProofStep 8.6.7: the lifted homotopy-fiber point at `underTopBasepoint Z` is the
canonical basepoint of `HomotopyFiber f`. -/
theorem homotopyFiberLiftPoint_basepoint :
    homotopyFiberLiftPoint g H (underTopBasepoint Z) = HomotopyFiber.basepoint f := by
  apply Subtype.ext
  apply Prod.ext
  · -- The point coordinate is the source basepoint image of the based map `g`.
    have hgbase :
        g.right.hom (underTopBasepoint Z) = underTopBasepoint X := by
      have hw :=
        congrArg
          (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
          (Under.w g)
      simpa [underTopBasepoint] using hw
    change g.right.hom (underTopBasepoint Z) = underTopBasepoint X
    exact hgbase
  · -- The path coordinate is constant because the homotopy is relative to the basepoint.
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    have hrel := H.eq_fst t (x := underTopBasepoint Z) (by simp [basedBasepointSet])
    simpa [homotopyFiberLiftPoint, homotopyFiberLiftPathPoint, PathSpace.basepoint,
      PathSpace.ofPath, PathSpace.mk, ContinuousMap.Homotopy.evalAt, constantBasedMap] using hrel

/-- The continuous map underlying the lift `Z → F_f`. -/
def homotopyFiberLiftContinuousMap :
    C(Z.right, HomotopyFiber f) :=
  { toFun := homotopyFiberLiftPoint g H
    continuous_toFun := homotopyFiberLiftContinuous g H }

/-- The paired map lands at the canonical basepoint of `homotopyFiber f` on the basepoint of `Z`.
-/
theorem homotopyFiberLift_w :
    Z.hom ≫ TopCat.ofHom (homotopyFiberLiftContinuousMap g H) =
      (homotopyFiber f).hom := by
  -- Evaluate both terminal-domain maps at an arbitrary point and compare with the canonical
  -- basepoint calculation proved above.
  ext x
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  have hx' : x = TopCat.terminalIsoPUnit.inv PUnit.unit := by
    simpa using congrArg TopCat.terminalIsoPUnit.inv hx
  calc
    (Z.hom ≫ TopCat.ofHom (homotopyFiberLiftContinuousMap g H)) x
        = (Z.hom ≫ TopCat.ofHom (homotopyFiberLiftContinuousMap g H))
            (TopCat.terminalIsoPUnit.inv PUnit.unit) := by
            rw [hx']
    _ = homotopyFiberLiftPoint g H (underTopBasepoint Z) := rfl
    _ = HomotopyFiber.basepoint f := homotopyFiberLiftPoint_basepoint g H
    _ = (homotopyFiber f).hom (TopCat.terminalIsoPUnit.inv PUnit.unit) := rfl
    _ = (homotopyFiber f).hom x := by rw [hx']

/-- ProofStep 8.6.7 (2). Given `g : Z ⟶ X` and a homotopy from the constant map to `f ∘ g`,
pairing `g` with the induced map `Z → PY` defines a based map `Z ⟶ F_f`. -/
def homotopyFiberLift :
    Z ⟶ homotopyFiber f :=
  Under.homMk (TopCat.ofHom (homotopyFiberLiftContinuousMap g H)) (homotopyFiberLift_w g H)

/-- Evaluating the underlying map of `homotopyFiberLift g H` returns the lifted homotopy-fiber
point. -/
@[simp] theorem homotopyFiberLift_hom_apply (z : Z.right) :
    (homotopyFiberLift g H).right.hom z = homotopyFiberLiftPoint g H z := rfl

end
