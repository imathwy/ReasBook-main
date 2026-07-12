import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap13.Lemma_13_11_2
import StacksProject_2024.Chap22.ModuleCatHasDerivedCategory

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe u

namespace CochainComplex

section

variable (A : Type u) [Ring A]

local notation "Ac" => HomotopyCategory.subcategoryAcyclic (ModuleCat A)
local notation "H" n => HomotopyCategory.homologyFunctor (ModuleCat A) (up ℤ) n
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "QhA" =>
  (DerivedCategory.Qh :
    HomotopyCategory (ModuleCat A) (up ℤ) ⥤ DerivedCategory (ModuleCat A))

/- Source/core/bridge triage:
- `source-facing`: Lemma 22.22.1 for the homotopy category `K(Mod_(A, d))` and derived category
  `D(A, d)` of differential graded `A`-modules;
- `core/canonical`: the generic Chapter 13 owners
  `HomotopyCategory.subcategoryAcyclic`,
  `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`,
  `subcategoryAcyclic_kernel_Qh`, and
  `DerivedCategory.homologyFunctorFactorsh`;
- `bridge/view`: the Chapter 22 DG-module model `ModuleCat A`, together with the named derived
  category instance `ModuleCat.hasDerivedCategory`.

This item adds no new owner beyond those Chapter 13 and mathlib declarations. The correct public
surface is therefore a recall/check specialization to `ModuleCat A`, not a duplicate local proof
or wrapper around the existing quasi-isomorphism and localization API. -/

/- Lemma 22.22.1 (1)–(3): the acyclic differential graded `A`-modules form a strictly full,
saturated, triangulated subcategory of `K(Mod_(A, d))`; in the current Lean model these are the
standard owner instances on `HomotopyCategory.subcategoryAcyclic (ModuleCat A)`. -/
#check (inferInstance : ObjectProperty.IsClosedUnderIsomorphisms Ac)

#check (show ObjectProperty.IsStableUnderRetracts Ac from by
  dsimp [HomotopyCategory.subcategoryAcyclic]
  infer_instance)

#check (inferInstance : ObjectProperty.IsTriangulated Ac)

/- Lemma 22.22.1 (4): the saturated multiplicative system attached to the acyclic subcategory is
exactly the quasi-isomorphism class in `K(Mod_(A, d))`. -/
recall HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W
#check
  (HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (ModuleCat A) :
    Qis = (HomotopyCategory.subcategoryAcyclic (ModuleCat A)).trW)

/- Lemma 22.22.1 (5)–(7): the quasi-isomorphism class in `K(Mod_(A, d))` has left and right
calculi of fractions and satisfies the two-out-of-three property. -/
#check (inferInstance : MorphismProperty.HasLeftCalculusOfFractions Qis)

#check (inferInstance : MorphismProperty.HasRightCalculusOfFractions Qis)

#check
  (show MorphismProperty.HasTwoOutOfThreeProperty Qis from by
    refine
      { comp_mem := ?_
        of_postcomp := ?_
        of_precomp := ?_ }
    · intro X Y Z f g hf hg
      rw [HomotopyCategory.mem_quasiIso_iff] at hf hg ⊢
      intro n
      simpa [Functor.map_comp] using
        (show IsIso (((H n).map f) ≫ ((H n).map g)) from inferInstance)
    · intro X Y Z f g hg hfg
      rw [HomotopyCategory.mem_quasiIso_iff] at hg hfg ⊢
      intro n
      have hfg' : IsIso (((H n).map f) ≫ ((H n).map g)) := by
        simpa [Functor.map_comp] using hfg n
      simpa using
        (MorphismProperty.of_postcomp
          (MorphismProperty.isomorphisms (ModuleCat A))
          ((H n).map f) ((H n).map g) (hg n) hfg')
    · intro X Y Z f g hf hfg
      rw [HomotopyCategory.mem_quasiIso_iff] at hf hfg ⊢
      intro n
      have hfg' : IsIso (((H n).map f) ≫ ((H n).map g)) := by
        simpa [Functor.map_comp] using hfg n
      simpa using
        (MorphismProperty.of_precomp
          (MorphismProperty.isomorphisms (ModuleCat A))
          ((H n).map f) ((H n).map g) (hf n) hfg'))

/- Lemma 22.22.1 (8): the kernel of the localization functor `Q : K(Mod_(A, d)) ⥤ D(A, d)` is
the acyclic subcategory. -/
recall subcategoryAcyclic_kernel_Qh
#check
  (subcategoryAcyclic_kernel_Qh (ModuleCat A) :
    Functor.kernel QhA = Ac)

/- Lemma 22.22.1 (9): the degree-zero homology functor on `K(Mod_(A, d))` factors through the
localization functor to the derived category. -/
recall DerivedCategory.homologyFunctorFactorsh
#check
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat A) 0 :
    QhA ⋙ DerivedCategory.homologyFunctor (ModuleCat A) 0 ≅
      HomotopyCategory.homologyFunctor (ModuleCat A) (up ℤ) 0)

end

end CochainComplex
