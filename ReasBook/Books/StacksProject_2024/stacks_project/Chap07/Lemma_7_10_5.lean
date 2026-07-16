import Mathlib
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_1
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ w₂ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
  [J.IsStableUnderComposition]

open Limits
open Precoverage

namespace SemiRepresentableFamily
namespace Over

/- Domain-style sampling for Lemma 7.10.5:
- primary domain: precoverage covering families and common refinements;
- sampled owner API:
  `Precoverage.ZeroHypercover`,
  `Precoverage.ZeroHypercover.inter`,
  `PreZeroHypercover.interFst`,
  `PreZeroHypercover.interSnd`;
- source/core/bridge triage:
  `source-facing`: the existence of a common covering refinement of two fixed-target families;
  `core/canonical`: `J.ZeroHypercover U` together with its canonical intersection cover;
  `bridge/view`: the comparison between a covering family and the canonical intersection
  construction on `J.ZeroHypercover U`.

Primitive data are only the two covering families and their covering proofs. The common refinement
is derived from `ZeroHypercover.inter`, so the public statement should stay at the level of the
covering-family API rather than introducing extra wrapper data.
-/

-- Proof sketch: view each covering family as a `0`-hypercover, take the canonical intersection
-- `𝒰.inter 𝒱`, and translate its two projection morphisms back to refinement morphisms of
-- fixed-target families.
/-- Lemma 7.10.5: two covering fixed-target families over `U` admit a common covering
refinement. -/
theorem exists_covering_family_common_refinement {U : C}
    (𝒰 𝒱 : Over U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ (𝒲 : Over U) (_ : IsCovering J 𝒲), Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := sorry

end Over
end SemiRepresentableFamily

end CategoryTheory
