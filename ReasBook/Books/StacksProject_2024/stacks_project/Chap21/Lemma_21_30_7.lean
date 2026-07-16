import StacksProject_2024.stacks_project.Chap21.Situation_21_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CategoryTheory.GrothendieckTopology

noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{u} C]
variable {τ τ' : GrothendieckTopology C}
variable (P : MorphismProperty C)
variable (A' : ∀ X : C, ObjectProperty (Sheaf (τ'.over X) AddCommGrpCat.{u}))

variable [∀ X : C, HasSheafify (τ'.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasInjectiveResolutions (Sheaf (τ'.over X) AddCommGrpCat.{u})]
variable [∀ {X Y : C} (f : X ⟶ Y),
  Functor.Additive
    ((Over.map f).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (τ'.over X) (τ'.over Y))]

variable [∀ X : C, HasSheafify (τ.over X) AddCommGrpCat.{u}]
variable [∀ X : C, HasExt (Sheaf (τ.over X) AddCommGrpCat.{u})]

-- Proof sketch: start with a class `ξ ∈ H^{n + 2}_τ(U, 𝓕)` for `𝓕 ∈ A_X` and
-- use locality to reduce to the case of a singleton `τ`-cover in the morphism property `P`.
-- Lemma `21.30.5` identifies the pullback of `ξ` with a unique `τ'`-class, Lemma `21.30.6`
-- kills that class after a `τ'`-covering, and Lemma `21.30.4` plus the truncation triangle and
-- Lemma `21.20.5` show that `ξ` comes from `τ'`-cohomology. Locality of `τ'`-cohomology then
-- yields the desired `τ'`-local vanishing of `ξ`.
/-- Lemma 21.30.7: in Situation 21.30.1, the local comparison vanishing condition `(V_n)`
implies the next-step condition `(V_{n + 1})`. -/
@[stacks 0EZE]
theorem localizedComparisonLocalVanishingCondition_succ
    (h : CohomologyComparisonSituation τ τ' P A')
    (n : ℕ)
    (hVn : (V_n) h) :
    (V_(n + 1)) h := sorry

end CategoryTheory.GrothendieckTopology
