import Mathlib
import StacksProject_2024.Chap17.Lemma_17_19_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopologicalSpace.Opens
open scoped TopCat

noncomputable section

universe u

/- Domain-style sampling for 17.19.2.1:
- primary domain: set-valued sheaves on a topological space, finite coproducts of lower-shriek
  constant sheaves, and coequalizers in the sheaf topos;
- sampled owner declarations:
  `HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn`,
  `Sheaf.instHasColimitsOfShape`,
  `j![U, S]`,
  `∐`,
  `coequalizer`,
  `coequalizer.condition`;
- best owner abstraction: the source-facing owner is the property of admitting a finite
  `j_{U!}\underline S` coequalizer presentation, with canonical realization by the ambient
  finite coproduct and `coequalizer` constructions;
- primitive data: finite index families `U`, `V`, `S`, `T` and a parallel pair `left right`
  between the associated coproducts;
- derived API: the owner predicates below, the displayed coproducts, the coequalizer object, the
  projection `coequalizer.π left right`, and the relation `coequalizer.condition left right`.

Source/core/bridge triage:
- `source-facing`: the owner predicate saying that a sheaf is of the form displayed in Equation
  `17.19.2.1`;
- `core/canonical`: finite coproducts in `Sh(X)` and `coequalizer`;
- `bridge/view`: refinements imposing extra conditions on the indexing opens, such as membership in
  a chosen basis.
-/

section

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]
local instance : HasColimitsOfShape WalkingParallelPair (TopCat.Sheaf (Type u) X) :=
  Sheaf.instHasColimitsOfShape

/-- A sheaf admits a finite `j_{U!}\underline S`-coequalizer presentation with open condition `P`
if it is isomorphic to the coequalizer of a parallel pair between finite coproducts of such
sheaves, all indexing opens satisfy `P`, and all fibres are finite. -/
def HasFiniteExtensionByZeroConstantSheafCoequalizerPresentationOn
    (P : Opens X → Prop) (ℱ : Sh(X)) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (κ : Type u) (_ : Fintype κ)
    (U : ι → Opens X) (V : κ → Opens X)
    (S : ι → Type u) (T : κ → Type u)
    (left right :
      (∐ fun b : κ ↦ j![V b, T b]) ⟶
        (∐ fun a : ι ↦ j![U a, S a]))
    (_ : ℱ ≅ coequalizer left right),
      (∀ a, P (U a)) ∧
        (∀ b, P (V b)) ∧
          (∀ a, Finite (S a)) ∧
            ∀ b, Finite (T b)

variable {ι κ : Type u} [Fintype ι] [Fintype κ]
variable (U : ι → Opens X) (V : κ → Opens X)
variable (S : ι → Type u) (T : κ → Type u)
variable (left right :
  (∐ fun j : κ ↦ j![V j, T j]) ⟶
    (∐ fun i : ι ↦ j![U i, S i]))

/- 17.19.2.1: the displayed finite coproduct is the canonical coproduct
`∐ fun i ↦ j_{U_i!}\underline{S_i}` in `Sh(X)`. -/
#check (∐ fun i : ι ↦ j![U i, S i])

/- 17.19.2.1: the displayed sheaf is the canonical coequalizer of the parallel pair
`left`, `right` between the two finite coproducts. -/
#check coequalizer left right

/- Companion recall: the universal projection from the target coproduct to the displayed
coequalizer is the canonical morphism `coequalizer.π left right`. -/
#check coequalizer.π left right

/- Companion recall: the defining relation of the displayed coequalizer is the canonical equation
`coequalizer.condition left right`. -/
#check coequalizer.condition left right

end
