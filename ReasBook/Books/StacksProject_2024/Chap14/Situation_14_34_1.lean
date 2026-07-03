import Mathlib.CategoryTheory.Adjunction.Basic

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uS vA vS

namespace CategoryTheory

variable {𝒜 : Type uA} {𝒮 : Type uS} [Category.{vA} 𝒜] [Category.{vS} 𝒮]
variable (U : 𝒮 ⥤ 𝒜) (V : 𝒜 ⥤ 𝒮)
variable (adj : U ⊣ V)

/- Domain-style sampling for Situation 14.34.1:
- primary domain: adjunctions of functors between categories;
- sampled owner API:
  `CategoryTheory.Adjunction`,
  `Adjunction.homEquiv`,
  `Adjunction.left_triangle`,
  `Adjunction.right_triangle`;
- best owner abstraction: `CategoryTheory.Adjunction U V`, written `U ⊣ V`;
- primitive data: the specified adjunction witness `adj : U ⊣ V`;
- derived API: the Hom-set equivalence, unit/counit, and triangle identities attached to that
  owner.

Source/core/bridge triage:
- `source-facing`: the situation that `U` is a specified left adjoint of `V`;
- `core/canonical`: `Adjunction U V`, written `U ⊣ V`;
- `bridge/view`: the derived equivalence `Adjunction.homEquiv` and its consequences.

Since the source item only fixes the ambient adjunction setup and does not add extra mathematical
data beyond the specified witness `adj`, the correct refinement is to expose that canonical owner
instance directly rather than introduce a specialized local wrapper or duplicate declaration. -/

/- Situation 14.34.1: categories `\mathcal A` and `\mathcal S`, a functor
`V : \mathcal A ⥤ \mathcal S`, and a specified left adjoint `U : \mathcal S ⥤ \mathcal A`;
this setup is expressed by fixing an adjunction witness `adj : U ⊣ V`. -/
#check adj

end CategoryTheory
