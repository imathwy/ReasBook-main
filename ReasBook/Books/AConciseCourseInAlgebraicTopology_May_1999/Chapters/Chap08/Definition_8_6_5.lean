import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_6_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Pullback_8_6_2

open CategoryTheory
open scoped Topology.Homotopy unitInterval

noncomputable section

-- Semantic recall: `lean_leansearch` did not surface a usable based-space sequence owner here,
-- while Chapter 25 already uses the local induced-loop-map pattern. This file keeps the source
-- faithful by recording the generated fiber sequence as an explicit `ℕ`-indexed based sequence.

/-- A sequence of based spaces indexed by `ℕ`, with maps from stage `n + 1` to stage `n`. -/
structure BasedSequence where
  /-- The `n`th object in the sequence. -/
  obj : ℕ → BasedSpace
  /-- The map from stage `n + 1` to stage `n`. -/
  map : (n : ℕ) → obj (n + 1) ⟶ obj n

namespace BasedSequence

/-- A `BasedSequence` may be viewed as its object function. -/
instance : CoeFun BasedSequence (fun _ ↦ ℕ → BasedSpace) where
  coe S := S.obj

end BasedSequence

/-- The path in `ΩY` induced by a based map `f : X ⟶ Y` on a loop in `X`. -/
def loopBasedMapPath {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    Ω Y.right (underTopBasepoint Y) :=
  let g : C(X.right, Y.right) := f.right.hom
  let hg : g (underTopBasepoint X) = underTopBasepoint Y :=
    fundamentalGroupFunctorMap_basepoint f
  (χ.map g.continuous).cast hg.symm hg.symm

/-- The loop-space map induced by a based map is continuous. -/
theorem loopBasedMapContinuous {X Y : BasedSpace} (f : X ⟶ Y) :
    Continuous fun χ : Ω X.right (underTopBasepoint X) ↦ loopBasedMapPath f χ := by
  -- Forget the target loop space to the ambient compact-open function space.
  rw [continuous_induced_rng]
  -- After forgetting the endpoint constraints, the map is postcomposition by `f.right.hom`.
  simpa [loopBasedMapPath] using
    (ContinuousMap.continuous_postcomp ⟨f.right.hom, f.right.hom.continuous⟩).comp
      (continuous_induced_dom :
        Continuous fun χ : Ω X.right (underTopBasepoint X) ↦ χ.toContinuousMap)

/-- The continuous map on loop spaces induced by a based map. -/
def loopBasedMapContinuousMap {X Y : BasedSpace} (f : X ⟶ Y) :
    C(Ω X.right (underTopBasepoint X), Ω Y.right (underTopBasepoint Y)) :=
  { toFun := fun χ ↦ loopBasedMapPath f χ
    continuous_toFun := loopBasedMapContinuous f }

/-- The induced loop-space map preserves the distinguished constant loop. -/
theorem loopBasedMap_w {X Y : BasedSpace} (f : X ⟶ Y) :
    (Ωᵇ X).hom ≫ TopCat.ofHom (loopBasedMapContinuousMap f) = (Ωᵇ Y).hom := by
  -- Both maps out of the terminal object evaluate to the constant loop at the basepoint of `Y`.
  ext x t
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((((Ωᵇ X).hom ≫ TopCat.ofHom (loopBasedMapContinuousMap f)) x).1 t)
        = ((loopBasedMapPath f (Path.refl (underTopBasepoint X))).1 t) := rfl
    _ = ((Path.refl (underTopBasepoint Y)).1 t) := by
      simp [loopBasedMapPath]
    _ = (((Ωᵇ Y).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)).1 t) := rfl
    _ = (((Ωᵇ Y).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x))).1 t) := by
      rw [hx]
    _ = (((Ωᵇ Y).hom x).1 t) := by
      simp

/-- The based loop-space map induced by a based map `f : X ⟶ Y`. -/
def loopBasedMap {X Y : BasedSpace} (f : X ⟶ Y) :
    Ωᵇ X ⟶ Ωᵇ Y :=
  Under.homMk
    (TopCat.ofHom (loopBasedMapContinuousMap f))
    (loopBasedMap_w f)

/-- The underlying loop-space map sends a loop to its image under `f`. -/
@[simp] theorem loopBasedMap_hom_apply {X Y : BasedSpace} (f : X ⟶ Y)
    (χ : Ω X.right (underTopBasepoint X)) :
    (loopBasedMap f).right.hom χ = loopBasedMapPath f χ := rfl

/-- Path reversal realizes the additive sign on loop spaces. -/
def loopBasedSpaceNegPath (X : BasedSpace) :
    Ω X.right (underTopBasepoint X) → Ω X.right (underTopBasepoint X) :=
  fun χ ↦ χ.symm

/-- Path reversal is continuous on the loop space of a based space. -/
theorem loopBasedSpaceNegContinuous (X : BasedSpace) :
    Continuous (loopBasedSpaceNegPath X) := by
  -- Forget the target loop space to the ambient compact-open function space.
  rw [continuous_induced_rng]
  -- After forgetting the endpoint constraints, reversal is precomposition by `unitInterval.symm`.
  simpa [loopBasedSpaceNegPath] using
    (ContinuousMap.continuous_precomp
      (⟨unitInterval.symm, unitInterval.continuous_symm⟩ : C(I, I))).comp
      (continuous_induced_dom :
        Continuous fun χ : Ω X.right (underTopBasepoint X) ↦ χ.toContinuousMap)

/-- The continuous loop-space inversion map. -/
def loopBasedSpaceNegContinuousMap (X : BasedSpace) :
    C(Ω X.right (underTopBasepoint X), Ω X.right (underTopBasepoint X)) :=
  { toFun := loopBasedSpaceNegPath X
    continuous_toFun := loopBasedSpaceNegContinuous X }

/-- Loop inversion fixes the distinguished constant loop. -/
theorem loopBasedSpaceNeg_w (X : BasedSpace) :
    (Ωᵇ X).hom ≫ TopCat.ofHom (loopBasedSpaceNegContinuousMap X) = (Ωᵇ X).hom := by
  -- Both maps out of the terminal object evaluate to the constant loop at the basepoint of `X`.
  ext x t
  have hx : TopCat.terminalIsoPUnit.hom x = PUnit.unit := by
    cases h : TopCat.terminalIsoPUnit.hom x
    rfl
  calc
    ((((Ωᵇ X).hom ≫ TopCat.ofHom (loopBasedSpaceNegContinuousMap X)) x).1 t)
        = ((loopBasedSpaceNegPath X (Path.refl (underTopBasepoint X))).1 t) := rfl
    _ = ((Path.refl (underTopBasepoint X)).1 t) := by
      simp [loopBasedSpaceNegPath]
    _ = (((Ωᵇ X).hom (TopCat.terminalIsoPUnit.inv PUnit.unit)).1 t) := rfl
    _ = (((Ωᵇ X).hom
          (TopCat.terminalIsoPUnit.inv (TopCat.terminalIsoPUnit.hom x))).1 t) := by
      rw [hx]
    _ = (((Ωᵇ X).hom x).1 t) := by
      simp

/-- The based self-map of `ΩX` implementing the sign convention by path reversal. -/
def loopBasedSpaceNeg (X : BasedSpace) : Ωᵇ X ⟶ Ωᵇ X :=
  Under.homMk
    (TopCat.ofHom (loopBasedSpaceNegContinuousMap X))
    (loopBasedSpaceNeg_w X)

/-- The sign-convention version of the induced loop-space map. -/
def signedLoopBasedMap {X Y : BasedSpace} (f : X ⟶ Y) :
    Ωᵇ X ⟶ Ωᵇ Y :=
  loopBasedMap f ≫ loopBasedSpaceNeg Y

/-- The objects of the fiber sequence generated by `f`, indexed so that stage `0` is `Y`. -/
def fiberSequenceGeneratedByObj {X Y : BasedSpace} (f : X ⟶ Y) : ℕ → BasedSpace
  | 0 => Y
  | 1 => X
  | 2 => homotopyFiber f
  | n + 3 => Ωᵇ (fiberSequenceGeneratedByObj f n)

/-- The maps in the fiber sequence generated by `f`, with the loop-space sign convention
implemented by `signedLoopBasedMap`. -/
def fiberSequenceGeneratedByMap {X Y : BasedSpace} (f : X ⟶ Y) :
    (n : ℕ) → fiberSequenceGeneratedByObj f (n + 1) ⟶ fiberSequenceGeneratedByObj f n
  | 0 => f
  | 1 => homotopyFiberProjection f
  | 2 => homotopyFiberLoopInclusion f
  | n + 3 => signedLoopBasedMap (fiberSequenceGeneratedByMap f n)

/-- Definition 8.6.5. The fiber sequence generated by `f` is the `ℕ`-indexed based sequence
whose rightmost stages are `Y`, `X`, and `F_f = homotopyFiber f`, with maps
`f : X ⟶ Y`, `homotopyFiberProjection f : F_f ⟶ X`, `homotopyFiberLoopInclusion f : Ωᵇ Y ⟶ F_f`,
and whose remaining stages and maps are obtained by iterating `Ωᵇ` and the chosen
sign-convention loop maps `signedLoopBasedMap`. This models the displayed sequence
`⋯ ⟶ Ω² X ⟶ Ω² Y ⟶ Ω F_f ⟶ Ω X ⟶ Ω Y ⟶ F_f ⟶ X ⟶ Y`. -/
def fiberSequenceGeneratedBy {X Y : BasedSpace} (f : X ⟶ Y) : BasedSequence where
  obj := fiberSequenceGeneratedByObj f
  map := fiberSequenceGeneratedByMap f

/-- The object function of `fiberSequenceGeneratedBy f` is `fiberSequenceGeneratedByObj f`. -/
theorem fiberSequenceGeneratedBy_obj {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).obj = fiberSequenceGeneratedByObj f := rfl

/-- The map function of `fiberSequenceGeneratedBy f` is `fiberSequenceGeneratedByMap f`. -/
theorem fiberSequenceGeneratedBy_map {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).map = fiberSequenceGeneratedByMap f := rfl

/-- Stage `0` of the generated fiber sequence is `Y`. -/
@[simp] theorem fiberSequenceGeneratedBy_obj_zero {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).obj 0 = Y := rfl

/-- Stage `1` of the generated fiber sequence is `X`. -/
@[simp] theorem fiberSequenceGeneratedBy_obj_one {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).obj 1 = X := rfl

/-- Stage `2` of the generated fiber sequence is the homotopy fiber `F_f`. -/
@[simp] theorem fiberSequenceGeneratedBy_obj_two {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).obj 2 = homotopyFiber f := rfl

/-- The first map in the generated fiber sequence is `f : X ⟶ Y`. -/
@[simp] theorem fiberSequenceGeneratedBy_map_zero {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).map 0 = f := rfl

/-- The second map in the generated fiber sequence is the projection `F_f ⟶ X`. -/
@[simp] theorem fiberSequenceGeneratedBy_map_one {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).map 1 = homotopyFiberProjection f := rfl

/-- The third map in the generated fiber sequence is the inclusion `ΩY ⟶ F_f`. -/
@[simp] theorem fiberSequenceGeneratedBy_map_two {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).map 2 = homotopyFiberLoopInclusion f := rfl

/-- The next object after `F_f` is `ΩY`. -/
@[simp] theorem fiberSequenceGeneratedBy_obj_three {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).obj 3 = Ωᵇ Y := rfl

/-- The first loop-space map in the generated fiber sequence is the signed loop map of `f`. -/
@[simp] theorem fiberSequenceGeneratedBy_map_three {X Y : BasedSpace} (f : X ⟶ Y) :
    (fiberSequenceGeneratedBy f).map 3 = signedLoopBasedMap f := rfl
