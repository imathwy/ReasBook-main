import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap07.Example_7_14_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v w

namespace CategoryTheory

namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}

/-- If `τ' ≤ τ`, then the induced localized topology over any object is again finer. -/
theorem comparisonOver_le (hle : τ' ≤ τ) (X : C) : τ'.over X ≤ τ.over X := by
  intro Y S hS
  exact hle _ hS

end

end GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable (hle : τ' ≤ τ) {X Y : C} (f : X ⟶ Y)

/- Domain-style sampling for 21.30.0.1:
- primary domain: change of Grothendieck topology on slice sites and its compatibility with
  relocalization along `f : X ⟶ Y`;
- sampled owner API:
  `Functor.sheafPushforwardContinuousComp'`,
  `GrothendieckTopology.overMapPullback`,
  `id_isContinuous_of_le`,
  `Functor.leftUnitor`,
  `Functor.rightUnitor`;
- source/core/bridge triage:
  `source-facing`: the compatibility of the topology-comparison morphisms `ε_X`, `ε_Y` with the
    relocalization morphisms attached to `f`;
  `core/canonical`: the sheaf-composition owner
    `Functor.sheafPushforwardContinuousComp'`;
  `bridge/view`: the specialization of that owner to the identity functors
    `𝟭 (Over X)` and `𝟭 (Over Y)` between the over-topologies `τ'.over _` and `τ.over _`.

Primitive data are only the comparison hypothesis `hle : τ' ≤ τ` and the morphism `f : X ⟶ Y`.
The localized topology-change pushforwards are already canonical sheaf pushforwards for the
identity functors on `Over X` and `Over Y`, so this file should use the owner theorem directly
rather than keep a parallel wrapper functor or a second comparison-iso definition.
-/

/- 21.30.0.1: the compatibility of `ε_X`, `ε_Y`, and relocalization along `f` is the canonical
specialization of `Functor.sheafPushforwardContinuousComp'` to the two identity functors on the
slice categories. -/
recall Functor.sheafPushforwardContinuousComp'

/- In Lean, the comparison `f_τ^{-1} ⋙ ε_X ≅ ε_Y ⋙ f_{τ'}^{-1}` is exactly the composite of the
left- and right-unitor specializations of the sheaf-composition owner theorem. -/
#check
  (by
    let _ : Functor.IsContinuous (𝟭 (Over X)) (τ'.over X) (τ.over X) :=
      id_isContinuous_of_le (GrothendieckTopology.comparisonOver_le hle X)
    let _ : Functor.IsContinuous (𝟭 (Over Y)) (τ'.over Y) (τ.over Y) :=
      id_isContinuous_of_le (GrothendieckTopology.comparisonOver_le hle Y)
    let _ : (Over.map f).IsContinuous (τ'.over X) (τ.over Y) :=
      Functor.isContinuous_comp (𝟭 (Over X)) (Over.map f) (τ'.over X) (τ.over X) (τ.over Y)
    exact
      (Functor.sheafPushforwardContinuousComp'
          (Functor.leftUnitor (Over.map f)) (Type w)
          (τ'.over X) (τ.over X) (τ.over Y)) ≪≫
        (Functor.sheafPushforwardContinuousComp'
          (Functor.rightUnitor (Over.map f)) (Type w)
          (τ'.over X) (τ'.over Y) (τ.over Y)).symm)

end

end CategoryTheory
