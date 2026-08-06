import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_1_1

open CategoryTheory Limits

noncomputable section

/-- The one-point based space. -/
abbrev onePointBasedSpace : BasedSpace :=
  Under.mk TopCat.terminalIsoPUnit.hom

/-- The chosen basepoint of `onePointBasedSpace` is `PUnit.unit`. -/
@[simp] theorem underTopBasepoint_onePointBasedSpace :
    underTopBasepoint onePointBasedSpace = PUnit.unit := sorry

/-- The constant map from a based space to the one-point based space. -/
def collapseToOnePointContinuousMap (X : BasedSpace) : C(X.right, onePointBasedSpace.right) :=
  ContinuousMap.const X.right PUnit.unit

/-- The constant map to the one-point based space preserves the chosen basepoints. -/
theorem collapseToOnePoint_w (X : BasedSpace) :
    X.hom ≫ TopCat.ofHom (collapseToOnePointContinuousMap X) =
      onePointBasedSpace.hom := sorry

/-- The canonical collapse of a based space to the one-point based space. -/
def collapseToOnePoint (X : BasedSpace) : X ⟶ onePointBasedSpace :=
  Under.homMk
    (TopCat.ofHom (collapseToOnePointContinuousMap X))
    (collapseToOnePoint_w X)

/-- The map `collapseToOnePoint X` is the constant map with value `PUnit.unit`. -/
theorem collapseToOnePoint_apply (X : BasedSpace) (x : X.right) :
    (collapseToOnePoint X).right.hom x = PUnit.unit := sorry
