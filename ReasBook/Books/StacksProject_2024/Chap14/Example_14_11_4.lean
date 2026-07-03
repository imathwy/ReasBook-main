import Mathlib
import stacks_project.Chap04.Example_4_38_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped RepresentablePresheaf Simplicial

universe u

section

variable (U : SSet.{u}) (n : ℕ)

/- Domain-style sampling for Example 14.11.4:
- primary domain: representable simplicial presheaves, their categories of elements, and the
  slice/fibred-in-sets presentation of standard simplices;
- sampled owner API:
  `representableElementsOpToOverEquivalence`,
  `representableElementsOpToOver_isEquivalenceOverBase`,
  `CategoryTheory.CategoryOfElements.costructuredArrowYonedaEquivalence`,
  `SSet.yonedaEquiv`;
- best owner abstraction: the source-facing owner for the example is the representable-to-slice
  bridge for `⦋n⦌ : SimplexCategory`, namely
  `representableElementsOpToOverEquivalence ⦋n⦌`; the simplicial Yoneda
  equivalence is then the canonical derived Hom formula for that representable;
- primitive data: the simplex degree `n`, and then the target simplicial set `U` for the final
  Hom computation;
- derived API: the over-base equivalence with `Over.forget ⦋n⦌`, and the Hom-to-`n`-simplex
  equivalence `SSet.yonedaEquiv`.

Source/core/bridge triage:
- `source-facing`: the identification of `Δ/[n] → Δ` with the category of elements of the
  representable presheaf `h[⦋n⦌]`, hence with the standard simplex `Δ[n]`;
- `core/canonical`: `representableElementsOpToOverEquivalence`, together with the final owner
  `SSet.yonedaEquiv`;
- `bridge/view`: the over-base equivalence
  `representableElementsOpToOver_isEquivalenceOverBase ⦋n⦌`. -/

/- Example 14.11.4: the category `Δ/[n] → Δ`, viewed as a category fibred in sets over `Δ`, is
the opposite category of elements of the representable presheaf `h[⦋n⦌]`; the project’s
representable-to-slice bridge specializes this to a canonical equivalence
`h[⦋n⦌].Elementsᵒᵖ ≌ Δ/[n]`. -/
#check
  (representableElementsOpToOverEquivalence ⦋n⦌ :
    h[⦋n⦌].Elementsᵒᵖ ≌ Over ⦋n⦌)

/- Companion bridge: in the fibred-over-the-base formulation, the same comparison is an
equivalence over `SimplexCategory` from the representable category of elements to the slice
projection `Over.forget ⦋n⦌`. -/
#check (representableElementsOpToOver_isEquivalenceOverBase ⦋n⦌)

/- Since the standard simplex `Δ[n]` is the simplicial representable at `⦋n⦌`, the resulting
presheaf formula for maps into `U` is the canonical simplicial Yoneda equivalence. -/
#check (SSet.yonedaEquiv : (Δ[n] ⟶ U) ≃ U _⦋n⦌)

end
