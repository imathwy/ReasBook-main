import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap15.«15_60_1_1»

noncomputable section

open CategoryTheory
open MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']

local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModR'" => DerivedCategory (ModuleCat R')

open scoped DerivedTensorWithAlgebra

private noncomputable abbrev rightTensorAdj
    [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (L : DModR') : MonoidalCategory.tensorRight L ⊣ CategoryTheory.ihom L :=
  (CategoryTheory.ihom.adjunction L).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight L)

recall Adjunction.rightAdjointUniq
recall CategoryTheory.ihom.adjunction
recall CategoryTheory.ihom

set_option linter.hashCommand false in
#check
  fun [MonoidalCategory DModR'] [BraidedCategory DModR'] [MonoidalClosed DModR']
    (K : DModR) (G : DModR' ⥤ DModR')
    (adj : MonoidalCategory.tensorRight (K ⊗[R]^L[R']) ⊣ G) (M : DModR') ↦
      ((adj.rightAdjointUniq (rightTensorAdj (K ⊗[R]^L[R']))).app M :
        G.obj M ≅ ((K ⊗[R]^L[R']) ⟶[DModR'] M))

end

end CategoryTheory
