import StacksProject_2024.Chap06.Definition_6_6_1
import StacksProject_2024.Chap19.Theorem_19_8_4
import StacksProject_2024.Chap21.SheafOfModulesForgetPreservesInjectiveObjects
import StacksProject_2024.Chap21.Lemma_21_10_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

noncomputable section

universe u v

variable {C : Type u} [Category.{max u v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.12.2:
- primary domain: sheaves of modules on a ringed site, their module-valued cohomology presheaves,
  and the underlying additive cohomology presheaves obtained by forgetting coefficients;
- sampled owner declarations:
  `Mod(𝒪)`,
  `PMod(𝒪.obj)`,
  `SheafOfModules.forget`,
  `SheafOfModules.toSheaf`,
  `PresheafOfModules.toPresheaf`,
  `Sheaf.cohomologyPresheafFunctor`,
  `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`;
- best owner abstraction: the source-facing owner is the `PMod(𝒪.obj)`-valued right derived
  functor of the inclusion `Mod(𝒪) ⥤ PMod(𝒪.obj)`, exposed below as
  `SheafOfModules.cohomologyPresheafFunctor`, its objectwise specialization
  `SheafOfModules.cohomologyPresheaf`, and the fixed-object owner
  `SheafOfModules.cohomologyAtObjectFunctor`; forgetting to additive presheaves is only the bridge
  to the canonical abelian owner `Sheaf.cohomologyPresheafFunctor`;
- primitive data: the structure sheaf `𝒪`, the cohomological degree `p`, and the module sheaf `ℱ`
  for the objectwise specialization;
- derived API: the additive forgetful bridge from the module-valued cohomology presheaf to the
  cohomology presheaf of the underlying abelian sheaf.

Source/core/bridge triage:
- `source-facing`: the module-valued cohomology-presheaf functor `Mod(𝒪) ⥤ PMod(𝒪.obj)` and its
  value on one `\mathcal O`-module sheaf;
- `core/canonical`: `SheafOfModules.forget`, `SheafOfModules.toSheaf`, and the existing
  left-exactness instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`;
- `bridge/view`: `PresheafOfModules.toPresheaf`, `Sheaf.cohomologyPresheafFunctor`, and the
  comparison theorems below after forgetting the `\mathcal O`-module structure.
-/

/- Lemma 21.12.2 first clause: the inclusion `Mod(𝒪) ⥤ PMod(𝒪.obj)` is left exact. This is
already the canonical instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`. -/
section

variable (𝒪 : Sheaf J RingCat.{max u v})

#synth PreservesFiniteLimits (SheafOfModules.forget 𝒪)

end

namespace SheafOfModules

/-- The `p`-th module-valued cohomology-presheaf functor on a ringed site, defined as the
degree-`p` right derived functor of the inclusion `Mod(𝒪) ⥤ PMod(𝒪.obj)`. -/
abbrev cohomologyPresheafFunctor (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) :
    Mod(𝒪) ⥤ PMod(𝒪.obj) :=
  (SheafOfModules.forget 𝒪).rightDerived p

/-- The module-valued cohomology presheaf `U ↦ H^p(U, ℱ)` of a sheaf of `𝒪`-modules, viewed in
`PMod(𝒪.obj)`. -/
abbrev cohomologyPresheaf
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Mod(𝒪)) (p : ℕ) :
    PMod(𝒪.obj) :=
  (cohomologyPresheafFunctor 𝒪 p).obj ℱ

/-- The additive functor `ℱ ↦ H^p(U, ℱ)` on sheaves of `𝒪`-modules over a fixed object `U`. -/
abbrev cohomologyAtObjectFunctor
    (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) (U : C) :
    Mod(𝒪) ⥤ AddCommGrpCat.{max u v} :=
  cohomologyPresheafFunctor 𝒪 p ⋙
    PresheafOfModules.toPresheaf 𝒪.obj ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)

section

variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [HasSheafify J AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Lemma 21.12.2: after forgetting the `𝒪`-module structure, the degree-`p` right derived
functor of the inclusion `Mod(𝒪) ⥤ PMod(𝒪.obj)` is the cohomology-presheaf functor
`ℱ ↦ (U ↦ H^p(U, ℱ))` of the underlying abelian sheaf. -/
@[stacks 06YK]
theorem cohomologyPresheafFunctor_toPresheaf_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (p : ℕ) :
    IsIsomorphic
      (((SheafOfModules.forget 𝒪).rightDerived p) ⋙ PresheafOfModules.toPresheaf 𝒪.obj)
      (SheafOfModules.toSheaf 𝒪 ⋙ Sheaf.cohomologyPresheafFunctor J p) := sorry

/-- For a sheaf of `𝒪`-modules `ℱ`, forgetting the module structure on the module-valued
cohomology presheaf recovers the cohomology presheaf of the underlying abelian sheaf. -/
theorem cohomologyPresheaf_toPresheaf_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Mod(𝒪)) (p : ℕ) :
    IsIsomorphic
      ((PresheafOfModules.toPresheaf 𝒪.obj).obj (cohomologyPresheaf 𝒪 ℱ p))
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).cohomologyPresheaf p) := sorry

/-- After forgetting the `𝒪`-module structure and evaluating at `U`, the module-valued
cohomology presheaf recovers the objectwise cohomology group `H^p(U, ℱ)` of the underlying
abelian sheaf. -/
theorem cohomologyAtObject_isomorphic
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : Mod(𝒪)) (p : ℕ) (U : C) :
    IsIsomorphic
      ((cohomologyAtObjectFunctor 𝒪 p U).obj ℱ)
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).H' p U) := sorry

end

end SheafOfModules
