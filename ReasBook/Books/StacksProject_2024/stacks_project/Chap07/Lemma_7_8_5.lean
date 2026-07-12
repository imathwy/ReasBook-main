import Mathlib
import StacksProject_2024.Chap07.Definition_7_8_1
import StacksProject_2024.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.8.5:
- primary domain: separatedness of set-valued presheaves for presieves, and fixed-target families
  viewed through the presieves they generate;
- inspected owner declarations:
  `Presieve.IsSeparatedFor`,
  `Presieve.IsSeparatedFor.ext`,
  `Presieve.FactorsThru`,
  `SemiRepresentableFamily.Over.Refines`;
- best owner abstraction: the core separatedness statement lives on the canonical presieve owner
  `Presieve.IsSeparatedFor`, and refinement of fixed-target families is a bridge/view statement via
  the induced factorization relation `Presieve.FactorsThru` between the generated presieves;
- primitive data: a presieve `R`, a presieve `S`, a factorization witness `R.FactorsThru S`, and a
  fixed-target family morphism `𝒱 ⟶ 𝒰`;
- derived API here: the owner-level monotonicity theorem
  `Presieve.IsSeparatedFor.of_factorsThru`, the bridge theorem
  `SemiRepresentableFamily.Over.toPresieve_factorsThru_of_hom`, the family-morphism theorem
  `SemiRepresentableFamily.Over.isSeparatedFor_of_hom`, and the source-facing refinement corollary
  `SemiRepresentableFamily.Over.isSeparatedFor_of_refines`.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily.Over.isSeparatedFor_of_refines`;
- `core/canonical`: `Presieve.IsSeparatedFor` together with `Presieve.FactorsThru`;
- `bridge/view`: `SemiRepresentableFamily.Over.toPresieve_factorsThru_of_hom`.
-/

namespace Presieve

/-- If every arrow of `R` factors through an arrow of `S`, then separatedness for `R` implies
separatedness for `S`. -/
theorem IsSeparatedFor.of_factorsThru {U : C} {ℱ : Cᵒᵖ ⥤ Type w} {R S : Presieve U}
    (hR : R.IsSeparatedFor ℱ) (hRS : R.FactorsThru S) :
    S.IsSeparatedFor ℱ := by
  intro x t₁ t₂ ht₁ ht₂
  apply hR.ext
  intro Y f hf
  rcases hRS hf with ⟨Z, i, g, hg, rfl⟩
  simp_rw [op_comp, FunctorToTypes.map_comp_apply]
  rw [ht₁ _ hg, ht₂ _ hg]

end Presieve

namespace SemiRepresentableFamily
namespace Over

/-- A morphism of fixed-target families makes the source-generated presieve factor through the
target-generated presieve. -/
theorem toPresieve_factorsThru_of_hom {U : C} {𝒱 𝒰 : Over U} (φ : 𝒱 ⟶ 𝒰) :
    𝒱.toPresieve.FactorsThru 𝒰.toPresieve := by
  intro Y f hf
  rcases Presieve.ofArrows_surj (fun j : 𝒱.index ↦ (𝒱.obj j).hom) f hf with ⟨j, hj, hf⟩
  refine ⟨_, eqToHom hj.symm ≫ (φ.f j).left, _, Presieve.ofArrows.mk (φ.α j), ?_⟩
  simpa [hf, Category.assoc] using congrArg (eqToHom hj.symm ≫ ·) (Over.w (φ.f j))

/-- Bridge form of Lemma 7.8.5 for an explicit morphism of fixed-target families. -/
theorem isSeparatedFor_of_hom {U : C} (ℱ : Cᵒᵖ ⥤ Type w)
    {𝒱 𝒰 : Over U} (φ : 𝒱 ⟶ 𝒰)
    (h𝒱 : 𝒱.toPresieve.IsSeparatedFor ℱ) :
    𝒰.toPresieve.IsSeparatedFor ℱ :=
  h𝒱.of_factorsThru (toPresieve_factorsThru_of_hom φ)

/-- Lemma 7.8.5: if a fixed-target family `𝒱` refines `𝒰` and `ℱ` is separated for `𝒱`, then
`ℱ` is separated for `𝒰`. -/
theorem isSeparatedFor_of_refines {U : C} (ℱ : Cᵒᵖ ⥤ Type w)
    {𝒱 𝒰 : Over U} (h : Refines 𝒱 𝒰)
    (h𝒱 : 𝒱.toPresieve.IsSeparatedFor ℱ) :
    𝒰.toPresieve.IsSeparatedFor ℱ := by
  exact h.elim fun φ ↦ isSeparatedFor_of_hom ℱ φ h𝒱

end Over
end SemiRepresentableFamily

end CategoryTheory
