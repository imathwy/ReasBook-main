import Mathlib
import StacksProject_2024.stacks_project.Chap30.«30_23_3_1»
import StacksProject_2024.stacks_project.Chap30.Lemma_30_26_9

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

private abbrev coherentProperSupportProperty (f : X ⟶ S) :
    ObjectProperty (RingedSpace.Coh X.toRingedSpace) :=
  fun ℱ ↦ HasProperSupportOver f ℱ.obj

/- Domain-style sampling for Equation 30.27.0.1:
- primary domain: the completion functor on coherent modules whose support is proper over a base;
- sampled owner API:
  `RingedSpace.Coh`,
  `CoherentFormalModules`,
  `HasProperSupportOver`,
  `CategoryTheory.ObjectProperty.FullSubcategory`;
- best owner abstraction: the source-facing categories are the proper-support full subcategories of
  the canonical coherent-module category and the canonical coherent-formal-module category, while
  the completion functor itself remains a bridge extending the Chapter `30.23.3.1` chosen
  completion functor;
- derived API: the source-facing proper-support source/target categories and the restricted
  completion functor between them.

Source/core/bridge triage:
- `source-facing`: the categories of coherent modules and coherent formal modules with support
  proper over the base;
- `core/canonical`: `RingedSpace.Coh X.toRingedSpace`, `Scheme.CoherentFormalModules X I`,
  `HasProperSupportOver`, and the Chapter `30.23.3.1` completion-functor owner;
- `bridge/view`: the restricted completion functor on those proper-support full subcategories.
-/

/-- The source-facing category
`\textit{Coh}_{\text{support proper over }S}(\mathcal O_X)` of coherent `\mathcal O_X`-modules
whose support is proper over the base morphism `f : X ⟶ S`. -/
@[stacks 088A]
abbrev CoherentProperSupportOver (f : X ⟶ S) :=
  (coherentProperSupportProperty f).FullSubcategory

/-- Objects of `CoherentProperSupportOver f` satisfy the defining proper-support condition. -/
@[stacks 088A]
theorem coherentProperSupportOver_obj_property (f : X ⟶ S)
    (ℱ : CoherentProperSupportOver f) :
    HasProperSupportOver f ℱ.obj.obj :=
  ℱ.property

/-- The `n`th coherent stage of a coherent formal module. -/
abbrev coherentFormalModuleStage
    {I : X.IdealSheafData} (M : Scheme.CoherentFormalModules X I) (n : ℕ) :
    RingedSpace.Coh X.toRingedSpace :=
  (M.obj).obj (Opposite.op n)

private abbrev coherentFormalProperSupportProperty
    (f : X ⟶ S) (I : X.IdealSheafData) :
    ObjectProperty (Scheme.CoherentFormalModules X I) :=
  fun M ↦ ∀ n : ℕ, HasProperSupportOver f (coherentFormalModuleStage M n).obj

/-- The source-facing category
`\textit{Coh}_{\text{support proper over }S}(X, \mathcal I)` of coherent formal modules along
`I` whose support is proper over the base morphism `f : X ⟶ S`. -/
@[stacks 088A]
abbrev CoherentFormalProperSupportOver (f : X ⟶ S) (I : X.IdealSheafData) :=
  (coherentFormalProperSupportProperty f I).FullSubcategory

/-- Objects of `CoherentFormalProperSupportOver f I` satisfy the defining proper-support
condition at each stage `n`. -/
@[stacks 088A]
theorem coherentFormalProperSupportOver_obj_property (f : X ⟶ S) (I : X.IdealSheafData)
    (M : CoherentFormalProperSupportOver f I) (n : ℕ) :
    HasProperSupportOver f (coherentFormalModuleStage M.obj n).obj :=
  M.property n

/-- The proper-support coherent modules form the Serre class singled out in Lemma `30.26.9 (7)`.
-/
theorem coherentProperSupportOver_isSerreClass
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
        ObjectProperty (RingedSpace.Coh X.toRingedSpace)) :=
  coherent_hasProperSupportOver_isSerreClass f

/-- The completion functor of `30.23.3.1` preserves proper support over the base at every coherent
stage. -/
@[stacks 088A]
theorem coherentCompletionFunctor_preservesProperSupportOver
    {f : X ⟶ S} [LocallyOfFiniteType f] {I : X.IdealSheafData}
    (ctx : CoherentCompletionFunctor X I)
    (ℱ : CoherentProperSupportOver f) (n : ℕ) :
    HasProperSupportOver f (coherentFormalModuleStage (ctx.obj ℱ.obj) n).obj := by
  sorry

/-- 30.27.0.1: the completion functor
`\textit{Coh}_{\text{support proper over }S}(\mathcal O_X) \to
\textit{Coh}_{\text{support proper over }S}(X, \mathcal I)`,
formalized as the Chapter `30.23.3.1` completion functor restricted to the source-facing
proper-support full subcategories. -/
@[stacks 088A]
abbrev coherentProperSupportCompletionFunctor
    {f : X ⟶ S} {I : X.IdealSheafData}
    [LocallyOfFiniteType f]
    (ctx : CoherentCompletionFunctor X I) :
    CoherentProperSupportOver f ⥤ CoherentFormalProperSupportOver f I :=
  ObjectProperty.lift (coherentFormalProperSupportProperty f I)
    ((coherentProperSupportProperty f).ι ⋙ ctx)
    (fun ℱ n ↦ coherentCompletionFunctor_preservesProperSupportOver ctx ℱ n)

end AlgebraicGeometry.Scheme.Modules
