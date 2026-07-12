import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import StacksProject_2024.Chap07.Lemma_7_42_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

section Exactness

variable [HasWeakSheafify JC AddCommGrpCat.{w}]
variable [HasSheafify JC AddCommGrpCat.{w}]
variable [JC.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JD AddCommGrpCat.{w}]
variable [HasSheafify JD AddCommGrpCat.{w}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify JC (Type w)]
variable [HasWeakSheafify JD (Type w)]

/-- Lemma 18.15.3: if `u : (C, JC) ⥤ (D, JD)` is continuous and almost cocontinuous, then the
direct-image functor on sheaves of abelian groups is exact. -/
theorem sheafPushforwardContinuous_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD] :
    exactFunctor (Sheaf JD AddCommGrpCat.{w})
      (Sheaf JC AddCommGrpCat.{w})
      (u.sheafPushforwardContinuous AddCommGrpCat.{w} JC JD) := by
  sorry

/-- Lemma 18.15.3: under the same hypotheses, pushforward of module sheaves along a morphism
`φ : 𝒪C ⟶ u_* 𝒪D` is exact. -/
theorem sheafOfModules_pushforward_exact_of_isAlmostCocontinuous
    (u : C ⥤ D) [u.IsContinuous JC JD] [u.IsAlmostCocontinuous JC JD]
    (𝒪C : Sheaf JC RingCat.{w}) (𝒪D : Sheaf JD RingCat.{w})
    (φ : 𝒪C ⟶ (u.sheafPushforwardContinuous RingCat.{w} JC JD).obj 𝒪D) :
    exactFunctor (SheafOfModules 𝒪D) (SheafOfModules 𝒪C)
      (SheafOfModules.pushforward φ) := by
  sorry

end Exactness

end CategoryTheory.Functor
