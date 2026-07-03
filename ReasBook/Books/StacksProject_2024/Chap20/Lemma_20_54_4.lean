import Mathlib
import StacksProject_2024.Chap20.Lemma_20_28_6
import StacksProject_2024.Chap20.«20_54_2_1»

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => ModuleDerived X
local notation "DModY" => ModuleDerived Y

variable (f : X ⟶ Y)

variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(modulePullback f).Additive]
variable [(modulePushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (ModuleDerived X)] [MonoidalCategory (ModuleDerived Y)]

variable
  (adj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
  (pullbackTensorIso :
    ∀ (A B : DModY),
      (modulePullbackDerived f).obj (A ⊗ B) ≅
        ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))

-- Proof sketch: because `f` identifies `X` with a closed subset of `Y`, pushforward on module
-- sheaves is exact, so `Rf_*` is computed by ordinary pushforward on complexes. Pullback of a
-- K-flat representative computes `Lf^*`, and the stalkwise tensor identity for a closed subset
-- inclusion identifies the two complexes representing the source and target of the projection
-- formula map.
/-- Lemma 20.54.4: if `f : X ⟶ Y` identifies `X` homeomorphically with a closed subset of `Y`,
then the projection-formula morphism
`K \otimes_{\mathcal O_Y}^{\mathbf L} Rf_* E ⟶
Rf_*(Lf^* K \otimes_{\mathcal O_X}^{\mathbf L} E)` is an isomorphism for all
`E ∈ D(\mathcal O_X)` and `K ∈ D(\mathcal O_Y)`. -/
theorem projectionFormulaMorphism_isIso_of_isClosedEmbedding
    (hf : Topology.IsClosedEmbedding f.hom.base)
    (E : DModX) (K : DModY) :
    IsIso (projectionFormulaMorphism
      (modulePullbackDerived f)
      (moduleDerivedPushforward f)
      adj
      pullbackTensorIso
      E
      K) := sorry

end

end AlgebraicGeometry.RingedSpace
