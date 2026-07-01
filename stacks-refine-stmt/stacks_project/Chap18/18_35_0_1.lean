import Mathlib

open CategoryTheory Limits

universe u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [HasBinaryCoproducts (Sheaf J CommRingCat.{u})]
variable (𝒜 : Sheaf J CommRingCat.{u}) (𝒝 : Under 𝒜)

/- Domain-style sampling for 18.35.0.1:
- primary domain: canonical presentations of sheaves of commutative rings, expressed by the
  free-forgetful adjunction on `Under 𝒜`;
- sampled owner API:
  `Under.costar`,
  `Under.costarAdjForget`,
  `((Under.costarAdjForget 𝒜).counit.app 𝒝)`,
  `(Under.costarAdjForget 𝒜).right_triangle_components 𝒝`;
- best owner abstraction: `Under.costarAdjForget 𝒜`;
- primitive data: the base sheaf of rings `𝒜` and the `𝒜`-algebra object `𝒝 : Under 𝒜`;
- derived API: the canonical presentation morphism and its value on bracket generators.

Source/core/bridge triage:
- `source-facing`: the canonical presentation morphism `\mathcal A[\mathcal B] \to \mathcal B`;
- `core/canonical`: `Under.costarAdjForget 𝒜`;
- `bridge/view`: this file is the general-site specialization of that under-category counit, so it
  should recall the owner directly rather than rebuild it via a parallel sheafification wrapper.
-/

/- 18.35.0.1: for a sheaf of commutative rings `\mathcal A` on a site and a sheaf of
`\mathcal A`-algebras `\mathcal B`, the canonical presentation morphism
`\mathcal A[\mathcal B] \to \mathcal B` is the underlying morphism of the counit of the canonical
adjunction `Under.costarAdjForget 𝒜`. -/
#check (((Under.costarAdjForget 𝒜).counit.app 𝒝).right :
  ((Under.costar 𝒜).obj 𝒝.right).right ⟶ 𝒝.right)

/-- The canonical presentation morphism sends the bracket generator `[b]` to `b`. -/
theorem siteCanonicalPresentationHom_on_brackets :
    (Under.costarAdjForget 𝒜).unit.app 𝒝.right ≫
        ((Under.costarAdjForget 𝒜).counit.app 𝒝).right =
      𝟙 𝒝.right := by
  simpa using (Under.costarAdjForget 𝒜).right_triangle_components 𝒝

end CategoryTheory
