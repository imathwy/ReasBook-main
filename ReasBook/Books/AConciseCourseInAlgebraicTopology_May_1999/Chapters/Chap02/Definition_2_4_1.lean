module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.Topology.Category.TopCat.Limits.Basic

public section

open CategoryTheory Limits

noncomputable section

universe u

/-- The category `T` of based spaces, formalized as the under category
`Under (⊤_ TopCat)`. Its objects are maps from the one-point space into a topological space, and
its morphisms are commutative triangles over `⊤_ TopCat`, equivalently continuous maps preserving
the chosen basepoints. -/
abbrev BasedSpace := Under (⊤_ TopCat.{u})

/-- Definition 2.4.1: `BasedSpace` is the canonical under-category presentation
`Under (⊤_ TopCat)` of based topological spaces. -/
theorem basedSpace_def : BasedSpace.{u} = Under (⊤_ TopCat.{u}) := by
  -- Unfold the abbreviation so the statement becomes reflexive.
  rfl

/-- The chosen basepoint of a based space in `Under (⊤_ TopCat)`. -/
def underTopBasepoint (X : BasedSpace.{u}) : X.right :=
  X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)

/-- Regard a topological space with a chosen point as an object of the based-space category. -/
noncomputable abbrev basedSpaceAtPoint (X : TopCat.{u}) (x : X) : BasedSpace.{u} :=
  Under.mk
    (TopCat.terminalIsoPUnit.hom ≫
      TopCat.ofHom (ContinuousMap.const PUnit x))

@[simp] theorem underTopBasepoint_basedSpaceAtPoint (X : TopCat.{u}) (x : X) :
    underTopBasepoint (basedSpaceAtPoint X x) = x := by
  rfl

namespace BasedSpace

/-- The based-space category has an initial object given by the one-point space with its identity
basepoint. -/
noncomputable instance : HasInitial BasedSpace.{u} := by
  simpa [BasedSpace] using
    (Under.mkIdInitial : Limits.IsInitial (Under.mk (𝟙 (⊤_ TopCat.{u})))).hasInitial

end BasedSpace

section BasedSpaceApi

variable (X : TopCat.{u})

/- A based space with underlying space `X` is given by a map from the one-point space into `X`. -/
example (f : ⊤_ TopCat.{u} ⟶ X) : BasedSpace.{u} := Under.mk f

/- A morphism of based spaces is induced by a continuous map between the underlying spaces that
preserves the chosen basepoints. -/
variable {A B : BasedSpace.{u}}

example (f : A.right ⟶ B.right) (hf : A.hom ≫ f = B.hom) : A ⟶ B :=
  Under.homMk f hf

/- Every morphism of based spaces satisfies the defining basepoint-preservation relation. -/
example (f : A ⟶ B) : A.hom ≫ f.right = B.hom := Under.w f

end BasedSpaceApi

/- The category of based spaces inherits its categorical structure from the canonical instance on
the under category. -/
#check (inferInstance : Category (BasedSpace.{u}))

end
