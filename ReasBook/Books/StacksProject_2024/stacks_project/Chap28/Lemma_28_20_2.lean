import Mathlib
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap17.Definition_17_17_1

open AlgebraicGeometry
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf-side owners
-- `SheafOfModules.IsFinitePresentation` and `SheafOfModules.IsFiniteType`, while local Chapter 17
-- precedent fixes `SheafOfModules.IsFlat`, `SheafOfModules.IsLocallyFree`, and
-- `SheafOfModules.IsFiniteLocallyFree` as the scheme-module surface. The Stacks item is therefore
-- stated as the scheme-level TFAE parallel to Algebra, Lemma `10.78.2`.

variable {X : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]

/-- The condition that a scheme module is of finite presentation and flat. -/
class FinitePresentationFlat : Prop extends ℱ.IsFinitePresentation, ℱ.IsFlat

/-- A finite-presentation-flat scheme module is of finite presentation. -/
instance instIsFinitePresentationOfFinitePresentationFlat [h : FinitePresentationFlat ℱ] :
    ℱ.IsFinitePresentation :=
  h.toIsFinitePresentation

/-- A finite-presentation-flat scheme module is flat. -/
instance instIsFlatOfFinitePresentationFlat [h : FinitePresentationFlat ℱ] : ℱ.IsFlat :=
  h.toIsFlat

/-- The condition that a scheme module is of finite presentation and has free stalks. -/
class FinitePresentationStalkwiseFree : Prop extends ℱ.IsFinitePresentation where
  stalk_free : ∀ x : X, Module.Free (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)

/-- A finite-presentation stalkwise-free scheme module is of finite presentation. -/
instance instIsFinitePresentationOfFinitePresentationStalkwiseFree
    [h : FinitePresentationStalkwiseFree ℱ] :
    ℱ.IsFinitePresentation :=
  h.toIsFinitePresentation

/-- The condition that a scheme module is locally free and of finite type. -/
class LocallyFreeFiniteType : Prop extends SheafOfModules.IsLocallyFree ℱ, ℱ.IsFiniteType

/-- A locally-free finite-type scheme module is locally free. -/
instance instIsLocallyFreeOfLocallyFreeFiniteType [h : LocallyFreeFiniteType ℱ] :
    SheafOfModules.IsLocallyFree ℱ :=
  h.toIsLocallyFree

/-- A locally-free finite-type scheme module is of finite type. -/
instance instIsFiniteTypeOfLocallyFreeFiniteType [h : LocallyFreeFiniteType ℱ] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

/-- The condition that a scheme module is of finite type with free stalks and locally constant
fiber-rank function. -/
class FiniteTypeStalkwiseFreeRankLocallyConstant : Prop extends ℱ.IsFiniteType where
  stalk_free : ∀ x : X, Module.Free (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x)
  rank_locallyConstant :
    IsLocallyConstant
      (fun x : X ↦
        (Module.finrank
          (IsLocalRing.ResidueField (X.presheaf.stalk x))
          ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[X.presheaf.stalk x]
            ↑(RingedSpace.stalkModuleCat ℱ x)) : ℤ))

/-- A finite-type stalkwise-free module with locally constant rank is of finite type. -/
instance instIsFiniteTypeOfFiniteTypeStalkwiseFreeRankLocallyConstant
    [h : FiniteTypeStalkwiseFreeRankLocallyConstant ℱ] :
    ℱ.IsFiniteType :=
  h.toIsFiniteType

/-- Lemma 28.20.2: for a quasi-coherent `\mathcal O_X`-module `\mathcal F` on a scheme `X`, the
following are equivalent: `\mathcal F` is flat and of finite presentation; `\mathcal F` is of
finite presentation and every stalk `\mathcal F_x` is free over `\mathcal O_{X, x}`; `\mathcal
F` is locally free of finite type; `\mathcal F` is finite locally free; and `\mathcal F` is of
finite type, every stalk `\mathcal F_x` is free over `\mathcal O_{X, x}`, and the fiber-rank
function `\rho_{\mathcal F}` is locally constant. -/
@[stacks 05P2]
theorem finiteLocallyFree_tfae :
    List.TFAE [
      FinitePresentationFlat ℱ,
      FinitePresentationStalkwiseFree ℱ,
      LocallyFreeFiniteType ℱ,
      SheafOfModules.IsFiniteLocallyFree ℱ,
      FiniteTypeStalkwiseFreeRankLocallyConstant ℱ
    ] := sorry

end AlgebraicGeometry.Scheme.Modules
