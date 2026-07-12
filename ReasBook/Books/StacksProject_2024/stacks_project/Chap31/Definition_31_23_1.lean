import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Topology.Sheaves.CommRingCat

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

local notation "JX" => Opens.grothendieckTopology X.toTopCat

-- Semantic recall: `lean_leansearch` surfaced
-- `TopCat.Presheaf.totalQuotientPresheaf`, and the associated sheaf is obtained here by the
-- canonical opens-site sheafification functor `presheafToSheaf`.

/-- Definition 31.23.1 (1): the sheaf of meromorphic functions on a locally ringed space `X` is
the sheaf associated to the total-quotient presheaf of the structure sheaf. -/
abbrev meromorphicFunctionSheaf : TopCat.Sheaf CommRingCat X.toTopCat :=
  (presheafToSheaf JX CommRingCat).obj
    (TopCat.Presheaf.totalQuotientPresheaf X.𝒪.presheaf)

/-- The canonical morphism from the structure sheaf to the sheaf of meromorphic functions. -/
noncomputable abbrev toMeromorphicFunctionSheafHom :
    X.𝒪 ⟶ meromorphicFunctionSheaf X :=
  (sheafificationIso X.𝒪).hom ≫
    (presheafToSheaf JX CommRingCat).map
      (TopCat.Presheaf.toTotalQuotientPresheaf X.𝒪.presheaf)

/-- The canonical algebra map from the stalk `𝒪_{X,x}` to the meromorphic stalk `𝒦_{X,x}`. -/
noncomputable instance instAlgebraStalkMeromorphicFunctionSheaf (x : X) :
    Algebra (X.presheaf.stalk x) ((meromorphicFunctionSheaf X).presheaf.stalk x) :=
  RingHom.toAlgebra
    (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (toMeromorphicFunctionSheafHom X).hom).hom)

/-- The canonical algebra map from regular sections on `U` to meromorphic sections on `U`. -/
noncomputable instance instAlgebraSectionsMeromorphicFunctionSheaf (U : Opens X.toTopCat) :
    Algebra (X.presheaf.obj (op U)) ((meromorphicFunctionSheaf X).presheaf.obj (op U)) :=
  RingHom.toAlgebra
    (((toMeromorphicFunctionSheafHom X).hom.app (op U)).hom)

/-- Definition 31.23.1 (2): the meromorphic functions on `X` are the global sections of the sheaf
`X.meromorphicFunctionSheaf`. -/
abbrev meromorphicFunctions : CommRingCat :=
  (meromorphicFunctionSheaf X).presheaf.obj (op ⊤)

/-- The canonical map from regular global sections to meromorphic functions. -/
noncomputable abbrev toMeromorphicFunctions :
    X.presheaf.obj (op ⊤) ⟶ meromorphicFunctions X :=
  (toMeromorphicFunctionSheafHom X).hom.app (op ⊤)

end AlgebraicGeometry.LocallyRingedSpace
