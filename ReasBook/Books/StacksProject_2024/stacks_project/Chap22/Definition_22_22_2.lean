import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.DGModuleModel
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape

noncomputable section

universe u

section

variable (A : Type u) [Ring A]

local notation "DA" => DerivedCategory (ModuleCat A)
local notation "Ac" => HomotopyCategory.subcategoryAcyclic (ModuleCat A)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)
local notation "QhA" => (DerivedCategory.Qh : ModuleCat.KDGMod A ⥤ DA)
local notation "H0A" => DerivedCategory.homologyFunctor (ModuleCat A) 0

/- Source/core/bridge triage:
- `source-facing`: the derived category `D(A, d)` of differential graded `A`-modules and its
  degree-zero homology functor `H⁰`;
- `core/canonical`: `DerivedCategory (ModuleCat A)`, the Chapter 22 owner
  `ModuleCat.KDGMod A`, the localization functor `DerivedCategory.Qh`, and
  `DerivedCategory.homologyFunctor (ModuleCat A) 0`;
- `bridge/view`: quasi-isomorphisms are identified with the acyclic Verdier quotient class by
  `HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W`, and `H⁰` descends along `Qh` via
  `DerivedCategory.homologyFunctorFactorsh`.
-/

/- Definition 22.22.2: for a differential graded algebra `(A, d)`, the derived category
`D(A, d)` is the Verdier quotient `K(Mod_(A,d))/Ac`, equivalently the localization
`Qis⁻¹ K(Mod_(A,d))`, and `H⁰ : D(A, d) ⥤ Mod_A` is the unique functor whose composition with
the quotient functor recovers degree-zero homology. In the current Chapter 22 Lean model,
differential graded `A`-modules are represented by cochain complexes of `A`-modules, so the
canonical owners are `ModuleCat.KDGMod A` for `K(Mod_(A,d))` and
`DerivedCategory (ModuleCat A)` for `D(A, d)`, with the global Chapter 22 instance
`ModuleCat.hasDerivedCategory` supplying the derived-category structure on `ModuleCat A`. The
quotient/localization functor is `DerivedCategory.Qh`, and the descended degree-zero homology
functor is `DerivedCategory.homologyFunctor (ModuleCat A) 0`. Local Lemma 22.22.1 already
supplies the same acyclic and quasi-isomorphism owners used in the quotient/localization
comparison. -/
#check DA

/- The canonical quotient/localization functor `K(Mod_(A, d)) ⥤ D(A, d)` is `DerivedCategory.Qh`.
-/
recall DerivedCategory.Qh
#check QhA

/- The Verdier quotient description and the localization at quasi-isomorphisms agree through the
canonical acyclic subcategory `Ac` and quasi-isomorphism class `Qis`. -/
#check
  (inferInstance :
    (DerivedCategory.Qh : ModuleCat.KDGMod A ⥤ DA).IsLocalization
      (HomotopyCategory.subcategoryAcyclic (ModuleCat A)).trW)

recall HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W
#check
  (HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (ModuleCat A) :
    Qis = (HomotopyCategory.subcategoryAcyclic (ModuleCat A)).trW)

/- The descended degree-zero homology functor on `D(A, d)` is `H0`. -/
recall DerivedCategory.homologyFunctor
#check (H0A : DA ⥤ ModuleCat A)

/- The composition of `H0` with the localization functor recovers degree-zero homology on
`K(Mod_(A, d))`. -/
recall DerivedCategory.homologyFunctorFactorsh
#check
  (DerivedCategory.homologyFunctorFactorsh (ModuleCat A) 0 :
    QhA ⋙ H0A ≅
      HomotopyCategory.homologyFunctor (ModuleCat A) (up ℤ) 0)

end
