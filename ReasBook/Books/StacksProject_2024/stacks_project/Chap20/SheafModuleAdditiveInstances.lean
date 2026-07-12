import Mathlib.Topology.Sheaves.Abelian
import StacksProject_2024.Chap20.Open_subspace_module_core

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Sheaves of abelian groups on a topological space carry their canonical preadditive structure. -/
instance sheafAddCommGrp_preadditive (X : TopCat.{u}) :
    Preadditive (X.Sheaf AddCommGrpCat.{u}) :=
  inferInstanceAs
    (Preadditive
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

/-- Sheaves of abelian groups on a topological space therefore have canonical zero morphisms. -/
instance sheafAddCommGrp_hasZeroMorphisms (X : TopCat.{u}) :
    HasZeroMorphisms (X.Sheaf AddCommGrpCat.{u}) :=
  Preadditive.preadditiveHasZeroMorphisms

namespace RingedSpace

/-- The category of `\mathcal O_X`-modules has canonical zero morphisms from its preadditive
structure. -/
instance modules_hasZeroMorphisms (X : RingedSpace.{u}) :
    HasZeroMorphisms (Modules X) :=
  Preadditive.preadditiveHasZeroMorphisms

end RingedSpace

end AlgebraicGeometry
