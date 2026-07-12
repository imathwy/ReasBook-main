import StacksProject_2024.Chap22.DGModuleModel

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe u

-- Semantic recall tool unavailable in this runner; the canonical owner choice was verified
-- locally against the Chapter 22 homotopy-category files using
-- `HomotopyCategory (ModuleCat A) (up ℤ)` for `K(Mod_(A,d))`.

section

variable (A : Type u) [Ring A]

/- Source/core/bridge triage:
- `source-facing`: the homotopy category `K(Mod_(A, d))` of differential graded `A`-modules;
- `core/canonical`: the canonical homotopy-category owner
  `HomotopyCategory (ModuleCat A) (up ℤ)`;
- `bridge/view`: the Chapter 22 support owners `ModuleCat.DGMod A` and `ModuleCat.KDGMod A`.
-/

/- Definition 22.5.3: the homotopy category `K(Mod_(A, d))` of differential graded
`(A, d)`-modules is the quotient of the differential graded module category by the homotopy
relation on morphisms. In this chapter's Lean model, differential graded `A`-modules are
cochain complexes of `A`-modules, so `K(Mod_(A, d))` is the Chapter 22 owner
`ModuleCat.KDGMod A`.
-/
#check (ModuleCat.KDGMod A)

/- Companion recall: the quotient relation identifying morphisms in `ModuleCat.DGMod A` is the
canonical homotopy congruence on chain maps. -/
#check (homotopic (ModuleCat A) (up ℤ) : HomRel (ModuleCat.DGMod A))

/- Companion recall: the quotient functor from differential graded `A`-modules to
`K(Mod_(A, d))` is the specialized homotopy-category quotient functor from
`ModuleCat.DGMod A` to `ModuleCat.KDGMod A`. -/
#check (HomotopyCategory.quotient (ModuleCat A) (up ℤ) :
  ModuleCat.DGMod A ⥤ ModuleCat.KDGMod A)

end
