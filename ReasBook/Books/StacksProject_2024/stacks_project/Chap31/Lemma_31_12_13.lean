import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap17.Definition_17_14_1
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Lemma_31_11_3
import StacksProject_2024.Chap31.Definition_31_12_1
import StacksProject_2024.Chap31.Lemma_31_15_8

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped ENat AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `Module.IsReflexive`,
-- `Module.IsTorsionFree`, `Scheme.Modules`, and finite-local-free sheaves; local Chapter 31
-- precedent fixes the scheme-module owners used below.

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- Helper for Lemma 31.12.13: in this file, a coherent `\mathcal O_X`-module is used through
the quasi-coherent Chapter 31 torsion-free interface. -/
local instance instIsQuasicoherentOfIsCoherentForLemma311213 : ℱ.IsQuasicoherent := sorry

/-- The open-subscheme witness condition used below: there is an open subset whose complement has
irreducible components of codimension at least `2`, such that the pullback of `ℱ` is finite
locally free and the canonical adjunction map is an isomorphism. -/
structure FiniteLocallyFreeOnCodimTwoOpenWithAdjunctionIso (ℱ : X.Modules) where
  /-- The open subset on which `ℱ` becomes finite locally free. -/
  U : X.Opens
  /-- The complement of the chosen open subset has irreducible components of codimension at least
  `2`. -/
  codim_complement :
    Scheme.IdealSheafData.irreducibleComponentsCodimAtLeast 2 ((U : Set X)ᶜ : Set X)
  /-- The pullback of `ℱ` to the chosen open subset is finite locally free. -/
  isFiniteLocallyFree_pullback :
    SheafOfModules.IsFiniteLocallyFree ((Scheme.Modules.pullback U.ι).obj ℱ)
  /-- The canonical adjunction map from `ℱ` to the pushforward of its pullback is an isomorphism. -/
  isIso_pullbackPushforwardAdjunction :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app ℱ)

/-- Lemma 31.12.13: let `X` be an integral locally Noetherian normal scheme and let `ℱ` be a
coherent `\mathcal O_X`-module. The following are equivalent: `ℱ` is reflexive; `ℱ` is torsion
free and satisfies Serre's condition `(S_2)`; and there is an open subscheme `j : U ⟶ X` whose
complement has irreducible components of codimension at least `2`, such that `j^*ℱ` is finite
locally free and the canonical adjunction map `ℱ ⟶ j_* j^*ℱ` is an isomorphism. -/
@[stacks 0AY6]
theorem isReflexive_tfae_torsionFree_satisfiesSerreConditionS_two_exists_open_finiteLocallyFree
    (hXnormal : X.isNormal) :
    List.TFAE
      [ IsReflexive ℱ,
        IsTorsionFree ℱ ∧ satisfiesSerreConditionS ℱ 2,
        Nonempty (FiniteLocallyFreeOnCodimTwoOpenWithAdjunctionIso ℱ)
      ] := sorry

end AlgebraicGeometry.Scheme.Modules
