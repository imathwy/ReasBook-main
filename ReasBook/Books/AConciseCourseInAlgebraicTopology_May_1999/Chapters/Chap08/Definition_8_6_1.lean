import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Definition_2_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_4

open CategoryTheory Limits
open scoped PathSpace

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `TopCat.pullbackIsoProdSubtype` as the canonical
-- pullback owner in `TopCat`; the local Chapter 7/8 precedent keeps mapping-path and based-space
-- constructions explicit via subtype carriers together with bundled objects in `Under (⊤_ TopCat)`.

/-- The pullback carrier `X ×_f PY` underlying the homotopy fiber of a based map `f`. -/
def HomotopyFiber {X Y : BasedSpace} (f : X ⟶ Y) : Type _ :=
  { z : X.right × P[underTopBasepoint Y] // f.right.hom z.1 = z.2.endpoint }

namespace HomotopyFiber

variable {X Y : BasedSpace} {f : X ⟶ Y}

/-- `HomotopyFiber f` carries the subtype topology inherited from
`X.right × P[underTopBasepoint Y]`. -/
instance instTopologicalSpace : TopologicalSpace (HomotopyFiber f) :=
  inferInstanceAs
    (TopologicalSpace
      { z : X.right × P[underTopBasepoint Y] // f.right.hom z.1 = z.2.endpoint })

/-- The point of `X` underlying an element of `HomotopyFiber f`. -/
def point (z : HomotopyFiber f) : X.right :=
  z.1.1

/-- The path in `Y` underlying an element of `HomotopyFiber f`. -/
def path (z : HomotopyFiber f) : P[underTopBasepoint Y] :=
  z.1.2

/-- Construct an element of `HomotopyFiber f` from a point and a path with matching endpoint. -/
def mk (x : X.right) (χ : P[underTopBasepoint Y])
    (hχ : f.right.hom x = χ.endpoint) : HomotopyFiber f :=
  ⟨(x, χ), hχ⟩

@[simp] theorem point_mk (x : X.right) (χ : P[underTopBasepoint Y])
    (hχ : f.right.hom x = χ.endpoint) :
    point (mk x χ hχ) = x :=
  rfl

@[simp] theorem path_mk (x : X.right) (χ : P[underTopBasepoint Y])
    (hχ : f.right.hom x = χ.endpoint) :
    path (mk x χ hχ) = χ :=
  rfl

/-- The defining condition on `z : HomotopyFiber f` is that `f(z.point) = z.path(1)`. -/
@[simp] theorem endpoint_eq (z : HomotopyFiber f) : f.right.hom z.point = z.path.endpoint := by
  simpa [point, path] using z.2

/-- The constant pair `(underTopBasepoint X, const_{underTopBasepoint Y})` satisfies the defining
equation of `HomotopyFiber f`. -/
theorem basepoint_condition (f : X ⟶ Y) :
    f.right.hom (underTopBasepoint X) =
      (PathSpace.basepoint (underTopBasepoint Y)).endpoint := by
  have hw :=
    congrArg
      (fun k ↦ k (TopCat.terminalIsoPUnit.inv PUnit.unit))
      (CategoryTheory.Under.w f)
  simpa [underTopBasepoint] using hw

/-- The canonical basepoint of `HomotopyFiber f` is given by the basepoint of `X` together with
the constant path at the basepoint of `Y`. -/
def basepoint (f : X ⟶ Y) : HomotopyFiber f :=
  mk (underTopBasepoint X) (PathSpace.basepoint (underTopBasepoint Y)) (basepoint_condition f)

/-- The point coordinate of the canonical basepoint of `HomotopyFiber f` is the basepoint of `X`.
-/
@[simp] theorem point_basepoint (f : X ⟶ Y) :
    (basepoint f).point = underTopBasepoint X :=
  rfl

/-- The path coordinate of the canonical basepoint of `HomotopyFiber f` is the constant path at
the basepoint of `Y`. -/
@[simp] theorem path_basepoint (f : X ⟶ Y) :
    (basepoint f).path = PathSpace.basepoint (underTopBasepoint Y) :=
  rfl

end HomotopyFiber

/-- Definition 8.6.1. For a based map `f : X ⟶ Y`, the homotopy fiber `F_f` is the based space
whose underlying carrier is the pullback
`X ×_f PY = { (x, χ) | f(x) = χ(1) }`, realized here as `HomotopyFiber f`, with distinguished
basepoint `(underTopBasepoint X, PathSpace.basepoint (underTopBasepoint Y))`. -/
def homotopyFiber {X Y : BasedSpace} (f : X ⟶ Y) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (HomotopyFiber.basepoint f)))

/-- The chosen basepoint of `homotopyFiber f` is the canonical constant pair. -/
@[simp] theorem underTopBasepoint_homotopyFiber {X Y : BasedSpace} (f : X ⟶ Y) :
    underTopBasepoint (homotopyFiber f) = HomotopyFiber.basepoint f := by
  rfl
