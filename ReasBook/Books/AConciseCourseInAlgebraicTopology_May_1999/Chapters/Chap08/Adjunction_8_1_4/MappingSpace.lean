import Mathlib.Topology.CompactOpen
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap02.Lemma_2_4_2

open CategoryTheory
open scoped BasedSpace

noncomputable section

/-- The based mapping space between `X` and `Y`, viewed as the subtype of continuous maps between
their underlying spaces that preserve the chosen basepoints. -/
abbrev underBasedMapSpace (X Y : BasedSpace) : Type _ :=
  { f : C(X.right, Y.right) // f (underTopBasepoint X) = underTopBasepoint Y }

/-- The distinguished basepoint of the based mapping space `F(X, Y)`, namely the constant map at
the basepoint of `Y`. -/
abbrev underBasedMapSpaceBasepoint (X Y : BasedSpace) : underBasedMapSpace X Y :=
  ⟨ContinuousMap.const X.right (underTopBasepoint Y), rfl⟩

@[simp] theorem underBasedMapSpaceBasepoint_apply
    (X Y : BasedSpace) (x : X.right) :
    (underBasedMapSpaceBasepoint X Y).1 x = underTopBasepoint Y := rfl

/-- The based mapping space `F(X, Y)` packaged again as an object of `Under (⊤_ TopCat)` with its
constant map as distinguished basepoint. -/
abbrev underBasedMapSpaceObject (X Y : BasedSpace) : BasedSpace :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit (underBasedMapSpaceBasepoint X Y)))

/-- Precomposition in the source and postcomposition in the target induce the usual map on based
mapping spaces. -/
def underBasedMapSpaceMap
    {X X' Y Y' : BasedSpace} (f : X' ⟶ X) (g : Y ⟶ Y') :
    underBasedMapSpace X Y → underBasedMapSpace X' Y' :=
  let sourceMap : C(X'.right, X.right) := f.right.hom
  let targetMap : C(Y.right, Y'.right) := g.right.hom
  fun h ↦
    ⟨
      targetMap.comp (h.1.comp sourceMap),
      by
        simp [sourceMap, targetMap, ContinuousMap.comp_apply, h.2,
          fundamentalGroupFunctorMap_basepoint]
    ⟩

@[simp] theorem underBasedMapSpaceMap_apply
    {X X' Y Y' : BasedSpace} (f : X' ⟶ X) (g : Y ⟶ Y')
    (h : underBasedMapSpace X Y) (x : X'.right) :
    (underBasedMapSpaceMap f g h).1 x = g.right.hom (h.1 (f.right.hom x)) := rfl

/-- The based mapping-space object is contravariantly functorial in its source and covariantly
functorial in its target. -/
def underBasedMapSpaceObjectMap
    {X X' Y Y' : BasedSpace} (f : X' ⟶ X) (g : Y ⟶ Y') :
    underBasedMapSpaceObject X Y ⟶ underBasedMapSpaceObject X' Y' :=
  Under.homMk
    (TopCat.ofHom
      { toFun := underBasedMapSpaceMap f g
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ fun h ↦ (underBasedMapSpaceMap f g h).2
          exact (ContinuousMap.continuous_postcomp g.right.hom).comp
            ((ContinuousMap.continuous_precomp f.right.hom).comp continuous_subtype_val) })
    (by
      ext x
      apply Subtype.ext
      ext y
      simp [underBasedMapSpaceBasepoint, underBasedMapSpaceMap,
        fundamentalGroupFunctorMap_basepoint])

@[simp] theorem underBasedMapSpaceObjectMap_apply
    {X X' Y Y' : BasedSpace} (f : X' ⟶ X) (g : Y ⟶ Y')
    (h : underBasedMapSpace X Y) (x : X'.right) :
    ((underBasedMapSpaceObjectMap f g).right.hom h).1 x =
      g.right.hom (h.1 (f.right.hom x)) := rfl
