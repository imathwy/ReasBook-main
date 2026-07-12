import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import StacksProject_2024.Chap12.Lemma_12_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v

namespace SheafOfModules

/- Domain-style sampling:
- primary domain: sheaves of modules on a ringed site, viewed as an abelian category equipped with
  the canonical contravariant Hom functor into a fixed injective target;
- sampled owner declarations:
  `preadditiveYonedaObj`,
  `CategoryTheory.preservesFiniteColimits_preadditiveYonedaObj_of_injective`,
  `exactFunctor_iff`,
  `SheafOfModules.instAbelian`;
- best owner abstraction: the ambient abelian category `SheafOfModules 𝒪`, with the canonical
  owner `preadditiveYonedaObj 𝒥` for the contravariant Hom functor;
- primitive data: the ring-valued sheaf `𝒪` and the target module sheaf `𝒥`;
- derived API: exactness of `preadditiveYonedaObj 𝒥` under the injective hypothesis on `𝒥`.

Source/core/bridge triage:
- `source-facing`: exactness of the dual functor `ℱ ↦ Hom(ℱ, 𝒥)` on `SheafOfModules 𝒪`;
- `core/canonical`: `preadditiveYonedaObj 𝒥`;
- `bridge/view`: none needed; the source-facing theorem can use the canonical owner directly.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒪 : Sheaf J RingCat.{max u v}}

section

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

-- Proof sketch: `preadditiveYonedaObj 𝒥` is the canonical owner for `ℱ ↦ Hom(ℱ, 𝒥)` on the
-- abelian category `SheafOfModules 𝒪`. If `𝒥` is injective, mathlib gives preservation of finite
-- colimits, while finite limits are always preserved; `exactFunctor_iff` then yields exactness.
/-- Lemma 19.8.1: for an injective `\mathcal O`-module sheaf `𝒥`, the dual functor
`ℱ ↦ ℱ^∨ = Hom(ℱ, 𝒥)` on `SheafOfModules 𝒪` is exact. -/
@[stacks 01DR]
theorem dual_exact (𝒥 : SheafOfModules.{max u v, v, u, max u v} 𝒪) [Injective 𝒥] :
    exactFunctor _ _ (preadditiveYonedaObj 𝒥) := by
  -- Route correction: apply the Chapter 12 injective criterion directly to the ambient category
  -- `SheafOfModules 𝒪`, avoiding the universe mismatch introduced by the `Mod(𝒪)` alias.
  let hAb : Abelian (SheafOfModules.{max u v, v, u, max u v} 𝒪) :=
    SheafOfModules.instAbelian 𝒪
  let hExt : CategoryTheory.HasExt (SheafOfModules.{max u v, v, u, max u v} 𝒪) := by
    letI : Abelian (SheafOfModules.{max u v, v, u, max u v} 𝒪) := hAb
    exact CategoryTheory.HasExt.standard (SheafOfModules.{max u v, v, u, max u v} 𝒪)
  -- The dual functor is exact because the target `𝒥` is injective.
  exact
    ((@CategoryTheory.injective_iff_exact_preadditiveYonedaObj
        (SheafOfModules.{max u v, v, u, max u v} 𝒪) inferInstance hAb hExt 𝒥).1 inferInstance)

end

end SheafOfModules
