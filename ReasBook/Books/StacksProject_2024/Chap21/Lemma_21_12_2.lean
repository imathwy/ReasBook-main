import Mathlib
import StacksProject_2024.Chap19.Theorem_19_7_4
import StacksProject_2024.Chap19.Theorem_19_8_4
import StacksProject_2024.Chap21.Lemma_21_10_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
variable [HasExt (Sheaf J AddCommGrpCat)]

/- Domain-style sampling for Lemma 21.12.2:
- primary domain: sheaves of modules on a ringed site, their underlying abelian sheaves and
  presheaves, and right derived functors of the inclusion into presheaves of modules;
- sampled owner declarations:
  `SheafOfModules.forget`,
  `SheafOfModules.toSheaf`,
  `SheafOfModules.toSheafCompSheafToPresheafIso`,
  `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`,
  `siteAbelianSheaf_hasEnoughInjectives`;
- best owner abstraction: the core owners are the canonical forgetful functors
  `SheafOfModules.forget` and `SheafOfModules.toSheaf`, together with the abelian-sheaf
  comparison theorem `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`; the
  left-exactness clause is already owned by the canonical instance
  `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`, so this file should not keep a parallel local
  theorem name for it, and the needed injective-resolution machinery for underlying abelian sheaves
  comes canonically from Chapter 19 via `siteAbelianSheaf_hasEnoughInjectives`;
- primitive data: the structure sheaf `𝒪`, a sheaf of `𝒪`-modules `ℱ`, and the cohomological
  degree `p`;
- derived API: the underlying-abelian-presheaf comparison in degree `p`, obtained by forgetting the
  module structure from the right derived object of `SheafOfModules.forget`.

Source/core/bridge triage:
- `source-facing`: the Stacks comparison between the derived inclusion
  `Mod(\mathcal O) ⥤ PMod(\mathcal O)` and the cohomology presheaf of the underlying abelian
  sheaf;
- `core/canonical`: `SheafOfModules.forget`, `SheafOfModules.toSheaf`, the anonymous instance
  `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`, and
  `abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor`;
- `bridge/view`: the module-to-abelian comparison theorem below.
-/

-- Enough injectives for `Mod(𝒪)` is already inferred from the imported owner-level instance
-- `modulesOnRingedSite_hasFunctorialInjectiveEmbeddings 𝒪` via the Chapter 12 bridge
-- `HasFunctorialInjectiveEmbeddings → EnoughInjectives`, so no extra local wrapper is needed here.

/- Lemma 21.12.2 first clause: the inclusion `Mod(\mathcal O) ⥤ PMod(\mathcal O)` is left exact.
This is already the canonical instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`. -/
section

variable (𝒪 : Sheaf J RingCat.{max u v})

#synth PreservesFiniteLimits (SheafOfModules.forget 𝒪)

end

-- Proof sketch: compute the right derived functors of `SheafOfModules.forget 𝒪` on an injective
-- resolution of `ℱ`. After forgetting further to abelian presheaves, this is the same sections
-- complex used to define the cohomology presheaf of the underlying abelian sheaf
-- `(SheafOfModules.toSheaf 𝒪).obj ℱ`.
/-- Lemma 21.12.2: for a sheaf of `\mathcal O`-modules `\mathcal F` on a ringed site, after
forgetting the `\mathcal O`-module structure the `p`-th right derived object of the inclusion
`Mod(\mathcal O) ⥤ PMod(\mathcal O)` is the cohomology presheaf
`U ↦ H^p(U, \mathcal F)` of the underlying abelian sheaf; the left exactness of the inclusion is
the existing instance `PreservesFiniteLimits (SheafOfModules.forget 𝒪)`. -/
theorem ringedSiteModuleInclusion_rightDerived_obj_is_cohomologyPresheaf
    (𝒪 : Sheaf J RingCat.{max u v}) (ℱ : SheafOfModules 𝒪) (p : ℕ) :
    IsIsomorphic
      ((PresheafOfModules.toPresheaf 𝒪.obj).obj
        (((SheafOfModules.forget 𝒪).rightDerived p).obj ℱ))
      (((SheafOfModules.toSheaf 𝒪).obj ℱ).cohomologyPresheaf p) := by
  let h :
      IsIsomorphic ((sheafToPresheaf J AddCommGrpCat).rightDerived p)
        (Sheaf.cohomologyPresheafFunctor J p) :=
    abelianSheafInclusion_rightDerived_is_cohomologyPresheafFunctor p
  let ⟨e⟩ := h
  simpa [Sheaf.cohomologyPresheaf] using
    (show IsIsomorphic (((sheafToPresheaf J AddCommGrpCat).rightDerived p).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱ))
        ((Sheaf.cohomologyPresheafFunctor J p).obj ((SheafOfModules.toSheaf 𝒪).obj ℱ)) from
      ⟨e.app ((SheafOfModules.toSheaf 𝒪).obj ℱ)⟩)
