import Mathlib
import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap04.Definition_4_33_9
import stacks_proof.stacks_project.Chap04.Lemma_4_33_13
import stacks_proof.stacks_project.Chap07.Definition_7_13_1
import stacks_proof.stacks_project.Chap07.Definition_7_15_1_Topoi
import stacks_proof.stacks_project.Chap07.Lemma_7_21_1
import stacks_proof.stacks_project.Chap07.Remark_7_20_5
import stacks_proof.stacks_project.Chap08.Definition_8_4_5
import stacks_proof.stacks_project.Chap08.Lemma_8_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite
open scoped MorphismOfTopoiIn
universe u v w

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/-- The Grothendieck topology on the total category of a fibred category inherited from the base
site. -/
abbrev inheritedTopology
    (J : GrothendieckTopology C) (X : FibredCategoryOver C) :
    GrothendieckTopology X.S :=
  (stronglyCartesianLiftPrecoverage J.toPrecoverage X.p).toGrothendieck

end FibredCategoryOver

namespace FibredCategoryMor

open FibredCategoryOver

variable {X Y : FibredCategoryOver C}
variable (J : GrothendieckTopology C) (F : X ⟶ Y)

local notation "JX" => inheritedTopology J X
local notation "JY" => inheritedTopology J Y

/- Domain-style sampling for Lemma 8.10.3:
- primary domain: morphisms of topoi induced by site functors that are both continuous and
  cocontinuous;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `Functor.sheafPushforwardCocontinuous`,
  `Functor.sheafPushforwardCocontinuousCompSheafToPresheafIso`,
  `Functor.sheafPushforwardContinuous`,
  `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.morphismOfTopoiInOfCocontinuous_pushforward`;
- best owner abstraction: the bundled morphism of topoi
  `F.toFunctor.morphismOfTopoiInOfCocontinuous JX JY`.

Source/core/bridge triage:
- `source-facing`: the induced morphism of topoi on the inherited sheaf topoi;
- `core/canonical`: the Chapter 7 owner
  `Functor.morphismOfTopoiInOfCocontinuous`;
- `bridge/view`: the continuity and cocontinuity instances below, which supply the hypotheses for
  the canonical Chapter 7 owner.

Primitive-vs-derived split:
- primitive data: the inherited Grothendieck topologies on `X.S` and `Y.S`, and the underlying
  functor `F.toFunctor`;
- derived API: the resulting `MorphismOfTopoiIn` package and its inverse/direct-image functors,
  already supplied canonically by `Functor.morphismOfTopoiInOfCocontinuous`.
-/

/-- A morphism of fibred categories over `C` is continuous for the Grothendieck topologies
inherited from the base site. -/
instance inheritedTopology_isContinuous :
    (toBasedFunctor F).toFunctor.IsContinuous JX JY := by
  -- The inherited precoverages on `X` and `Y` already satisfy the Chapter 7 continuity bridge.
  infer_instance

/-- A morphism of fibred categories over `C` is cocontinuous for the Grothendieck topologies
inherited from the base site. -/
instance inheritedTopology_isCocontinuous :
    (toBasedFunctor F).toFunctor.IsCocontinuous JX JY := by
  -- The Chapter 7 cover-lifting bridge upgrades the inherited-cover argument to cocontinuity.
  infer_instance

/- Companion recall: the induced morphism of topoi is already canonically owned by
`Functor.morphismOfTopoiInOfCocontinuous`. -/
recall Functor.morphismOfTopoiInOfCocontinuous

/- Lemma 8.10.3: the cocontinuous functor on total categories induced by `F` determines the
canonical morphism of topoi between the inherited sheaf topoi. -/
#check
  ((toBasedFunctor F).toFunctor.morphismOfTopoiInOfCocontinuous JX JY : MorphismOfTopoiIn JY JX)

/- Companion specialization of Lemma 7.21.1: the direct image of the induced morphism is the
canonical cocontinuous sheaf pushforward owner `{}_sF`. -/
#check (Functor.morphismOfTopoiInOfCocontinuous_pushforward (toBasedFunctor F).toFunctor JX JY)

/- Companion specialization of Lemma 7.20.2: the direct image `f_* = {}_sF` has underlying
presheaf equal to the presheaf pushforward `{}_pF`. -/
#check
  ((toBasedFunctor F).toFunctor.sheafPushforwardCocontinuousCompSheafToPresheafIso
    (Type w) JX JY)

/- Companion specialization of Lemma 7.21.5: the inverse image on sheaves attached to the
continuous functor `F.toFunctor` is already the presheaf pullback `F^p` on underlying
presheaves. -/
#check
  ((toBasedFunctor F).toFunctor.sheafPushforwardContinuousCompSheafToPresheafIso
    (Type w) JX JY)

/- In particular, the inverse image is given pointwise by evaluation at `F(x)`. -/
theorem inheritedTopology_inverseImage_obj_obj
    (𝒢 : Sheaf JY (Type w)) (x : X.S) :
    ((((toBasedFunctor F).toFunctor.sheafPushforwardContinuous (Type w) JX JY).obj 𝒢).1.obj
      (op x)) =
      𝒢.1.obj (op ((toBasedFunctor F).obj x)) :=
  rfl

end FibredCategoryMor

end

end CategoryTheory
