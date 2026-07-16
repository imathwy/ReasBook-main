import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap13.Lemma_13_12_1
import StacksProject_2024.stacks_project.Chap22.ModuleCatHasDerivedCategory

open CategoryTheory
open DerivedCategory

noncomputable section

universe u

namespace CochainComplex

section

variable (A : Type u) [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ
local notation "DDGMod" => DerivedCategory (ModuleCat A)

/- Lemma 22.23.1: for a differential graded algebra `(A, d)`, the canonical localization functor
`Mod_(A, d) ⟶ D(A, d)` carries the standard connecting morphisms of short exact sequences,
equivalently the Stacks maps `-p ∘ q⁻¹`, and therefore forms a `δ`-functor. In the current
Chapter 22 Lean model `Mod_(A, d)` is represented by `DGMod = CochainComplex (ModuleCat A) ℤ`, so
the source-facing owner is the canonical Chapter 13 `δ`-functor on cochain complexes. This file
is therefore a pure recall of that owner, not a second public wrapper around the same data. -/
recall cochainComplexToDerivedDeltaFunctor

/- Companion bridge: the underlying functor of the canonical DG-module `δ`-functor is the
localization functor `Q : Mod_(A, d) ⥤ D(A, d)`. -/
@[simp] theorem cochainComplexToDerivedDeltaFunctor_toFunctor :
    (cochainComplexToDerivedDeltaFunctor (ModuleCat A)).toFunctor = (Q : DGMod ⥤ DDGMod) :=
  rfl

/- Companion bridge: the connecting morphism of the canonical DG-module `δ`-functor is the
derived-category boundary morphism attached to a short exact sequence. -/
@[simp] theorem cochainComplexToDerivedDeltaFunctor_δ {S : ShortComplex DGMod}
    (hS : S.ShortExact) :
    (cochainComplexToDerivedDeltaFunctor (ModuleCat A)).δ hS = triangleOfSESδ hS :=
  rfl

end

end CochainComplex
