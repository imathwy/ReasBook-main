import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import StacksProject_2024.Chap12.Definition_12_10_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (τ τ' : GrothendieckTopology C)

/-- Situation 21.30.1: a comparison setup for cohomology on a category `C` with two
Grothendieck topologies `τ` and `τ'`, consisting of a morphism property `P` and for each object
`X` a weak Serre subcategory `A'_X ⊂ Ab(C_{τ'}/X)`, such that `P` is stable under base change,
inverse image preserves the chosen subcategories, objects of `A'_X` are already `τ`-sheaves,
higher direct images along arrows in `P` stay in the chosen subcategories, and every `τ`-covering
admits the refinement pattern described in the text by `τ'`-coverings and singleton `P`-covers. -/
@[stacks 0EZ3]
class CohomologyComparisonSituation
    (P : MorphismProperty C)
    (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})) : Prop where
  /-- Each `A'_X` is a weak Serre subcategory of `Ab(C_{τ'}/X)`. -/
  isWeakSerre (X : C) [HasSheafify (τ'.over X) AddCommGrpCat.{max u v}] :
      IsWeakSerreClass (A' X)
  /-- Pullbacks of arrows in `P` along arbitrary maps exist. -/
  hasPullbacks : P.HasPullbacks
  /-- The morphism property `P` is stable under base change. -/
  isStableUnderBaseChange : P.IsStableUnderBaseChange
  /-- Inverse image along any morphism sends `A'_Y` into `A'_X`. -/
  inverseImage_mem {X Y : C} (f : X ⟶ Y)
      {ℱ : Sheaf (τ'.over Y) AddCommGrpCat.{max u v}} (_ : A' Y ℱ) :
      A' X ((τ'.overMapPullback AddCommGrpCat.{max u v} f).obj ℱ)
  /-- Every object of `A'_X` satisfies the sheaf condition for the coarser topology `τ`. -/
  isSheaf_for_coarser_topology {X : C}
      {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (_ : A' X ℱ) :
      CategoryTheory.Presheaf.IsSheaf (τ.over X) ℱ.1
  /-- Higher direct images along arrows in `P` remain inside the chosen weak Serre
  subcategories. -/
  higherDirectImage_mem
      [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{max u v}]
      [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{max u v})]
      [∀ {X Y : C} (f : X ⟶ Y),
        Functor.Additive
          ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
            (τ'.over X) (τ'.over Y))]
      {X Y : C} (f : X ⟶ Y) (_ : P f) (i : ℕ)
      {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (_ : A' X ℱ) :
      A' Y ((((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{max u v}
        (τ'.over X) (τ'.over Y)).rightDerived i).obj ℱ)
  /-- Every `τ`-covering refines to a `τ'`-covering, followed by singleton covers from `P`, and
  then by further `τ'`-coverings as in the Stacks-project situation. -/
  tau_covering_refinement {U : C} {ι : Type u} (cover : ι → Over U)
      (_ : (τ.over U).CoversTop cover) :
      ∃ (J : Type u) (V : J → Over U),
        (τ'.over U).CoversTop V ∧
          ∃ (W : J → C) (f : ∀ j, W j ⟶ (V j).left),
            ∀ j,
              P (f j) ∧
                Sieve.generate (Presieve.singleton (f j)) ∈ τ (V j).left ∧
                  ∃ (Kj : Type u) (Wcoverj : Kj → Over (W j)),
                    (τ'.over (W j)).CoversTop Wcoverj ∧
                      ∀ k : Kj,
                        ∃ i : ι,
                          Nonempty
                            ((Over.mk ((Wcoverj k).hom ≫ f j ≫ (V j).hom)) ⟶ cover i)

attribute [instance] CohomologyComparisonSituation.isWeakSerre
attribute [instance] CohomologyComparisonSituation.hasPullbacks
attribute [instance] CohomologyComparisonSituation.isStableUnderBaseChange

namespace CohomologyComparisonSituation

variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{max u v})}

/-- If `ℱ ∈ A'_X` in Situation `21.30.1`, then the same presheaf canonically defines a
`τ`-sheaf on `C/X`. -/
def coarserSheaf
    (h : CohomologyComparisonSituation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    Sheaf (τ.over X) AddCommGrpCat.{max u v} :=
  ⟨ℱ.1, h.isSheaf_for_coarser_topology hℱ⟩

@[simp]
theorem coe_coarserSheaf
    (h : CohomologyComparisonSituation τ τ' P A')
    {X : C} {ℱ : Sheaf (τ'.over X) AddCommGrpCat.{max u v}} (hℱ : A' X ℱ) :
    (h.coarserSheaf hℱ).1 = ℱ.1 :=
  rfl

section LocalVanishing

variable {C : Type v} [Category.{v} C]
variable {τ τ' : GrothendieckTopology C}
variable {P : MorphismProperty C}
variable {A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{v})}
variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{v}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{v})]

/-- The source-facing local comparison vanishing condition `(V_n)`: for every `X`, every
`ℱ ∈ A'_X`, every `U : Over X`, and every degree `n + 1` cohomology class of the coarser
`τ`-sheaf underlying `ℱ`, there is a `τ'`-cover of `U` on which that class restricts to zero. -/
def LocalVanishing
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ) : Prop :=
  ∀ (X : C) (ℱ : Sheaf (τ'.over X) AddCommGrpCat.{v}) (hℱ : A' X ℱ),
    let G := (h.coarserSheaf hℱ).cohomologyPresheaf (n + 1)
    ∀ (U : Over X) (ξ : G.obj (Opposite.op U)), ∃ T : (τ'.over X).Cover U, ∀ I : T.Arrow,
      (G.map I.f.op) ξ = 0

end LocalVanishing

end CohomologyComparisonSituation

/- Source-facing notation for the local comparison vanishing condition `(V_n)`. -/
scoped notation "(V_" n ")" => fun h ↦ CohomologyComparisonSituation.LocalVanishing h n

end CategoryTheory.GrothendieckTopology
