import Mathlib
import stacks_project.Chap06.Definition_6_10_1
import stacks_project.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

noncomputable section

/- Domain-style sampling for Theorem 19.8.4:
- primary domain: enough injectives in categories of sheaves of modules on a ringed site, as the
  immediate input for the Chapter 13 resolution-functor existence theorem;
- sampled owner declarations:
  `Mod(𝒪)`,
  `EnoughInjectives`,
  `CategoryTheory.exists_resolutionFunctorOne`,
  `CategoryTheory.exists_homotopyResolutionFunctor`;
- best owner abstraction: the source-facing owner here is `EnoughInjectives (Mod(𝒪))`; this is the
  canonical common input for the Chapter 13 existence theorems, while any stronger
  functorial-injective-embedding owner would require separate justification not supplied in this
  file;
- primitive data: the enough-injectives theorem for `Mod(𝒪)`;
- derived API: the Chapter 13 resolution-functor and homotopy-resolution consequences that use the
  `EnoughInjectives` instance.

Source/core/bridge triage:
- `source-facing`: Theorem 19.8.4, asserting enough injectives in `Mod(𝒪)`;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the Chapter 13 existence theorems that consume the `EnoughInjectives` instance.
-/

-- Proof sketch: build enough injectives in `Mod(𝒪)` by the ringed-site injective
-- embedding argument from the discussion preceding the theorem.
/-- Theorem 19.8.4: for a site `\mathcal C` and a sheaf of rings `\mathcal O` on `\mathcal C`,
the category of sheaves of `\mathcal O`-modules has enough injectives. -/
instance modulesOnRingedSite_hasEnoughInjectives
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    EnoughInjectives (Mod(𝒪)) := sorry
