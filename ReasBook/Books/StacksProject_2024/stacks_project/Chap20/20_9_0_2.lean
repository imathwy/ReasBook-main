import Mathlib

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u v

variable {X : TopCat.{u}} {I J : Type v}

/- Domain-style sampling for 20.9.0.2:
- primary domain: indexed open-cover refinements and the induced morphisms between the associated
  formal coproducts;
- sampled owner declarations:
  `Opens X`,
  `FormalCoproduct`,
  `CategoryTheory.homOfLE`,
  `cechComplexFunctor`;
- best owner abstraction: a refinement of indexed open covers is primitive data on families of
  opens, so the chapter owner should be the Prop-valued predicate `IsRefinement 𝒰 𝒱 t` together
  with the canonical formal-coproduct morphism `refinementHom 𝒰 𝒱 t ht` that it induces;
- primitive data: indexed families `𝒰 : I → Opens X`, `𝒱 : J → Opens X`, and a map `t : J → I`;
- derived API: the induced morphisms on Čech complexes and total complexes, developed in later
  files.

Source/core/bridge triage:
- `source-facing`: `IsRefinement`;
- `core/canonical`: `FormalCoproduct`;
- `bridge/view`: `refinementHom`, which turns a refinement witness into the canonical morphism of
  formal coproducts.
-/

/-- A map `t : J → I` exhibits `𝒱` as a refinement of `𝒰` if `V_j ⊆ U_{t(j)}` for every `j`. -/
def IsRefinement (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I) : Prop :=
  ∀ j : J, 𝒱 j ≤ 𝒰 (t j)

/-- The morphism of formal coproducts attached to a refinement map of indexed open covers. -/
def refinementHom (𝒰 : I → Opens X) (𝒱 : J → Opens X) (t : J → I)
    (ht : IsRefinement 𝒰 𝒱 t) :
    (⟨J, 𝒱⟩ : FormalCoproduct (Opens X)) ⟶ (⟨I, 𝒰⟩ : FormalCoproduct (Opens X)) where
  f := t
  φ j := homOfLE (ht j)
