import Mathlib
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import StacksProject_2024.Chap06.Definition_6_10_1
import StacksProject_2024.Chap12.Definition_12_27_5
import StacksProject_2024.Chap18.Lemma_18_14_2

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
  `ModuleCat.enoughInjectives`,
  `siteAbelianSheaf_hasEnoughInjectives`;
- best owner abstraction: the source-facing owner here is `EnoughInjectives (Mod(𝒪))`; this is the
  canonical common input for the Chapter 13 existence theorems, and no earlier project owner
  supplies the same arbitrary-`RingCat` statement directly;
- primitive data: the enough-injectives theorem for `Mod(𝒪)`;
- derived API: the Chapter 13 resolution-functor and homotopy-resolution consequences that use the
  `EnoughInjectives` instance.

Source/core/bridge triage:
- `source-facing`: Theorem 19.8.4, asserting enough injectives in `Mod(𝒪)`;
- `core/canonical`: `EnoughInjectives`;
- `bridge/view`: the Chapter 13 existence theorems that consume the `EnoughInjectives` instance.

The commutative-ring generator constructions from Chapter 18 live at a stricter `CommRingCat`
layer, so they are companion specializations rather than a replacement owner for this arbitrary
ring-sheaf theorem.
-/

-- Proof sketch: the imported sheaf-of-modules API already installs the Grothendieck-abelian
-- owners on `Mod(𝒪)`, so enough injectives is available as the canonical owner-level instance.

/-- Theorem 19.8.4: for a site `\mathcal C` and a sheaf of rings `\mathcal O` on `\mathcal C`,
the category of sheaves of `\mathcal O`-modules has enough injectives. -/
@[stacks 01DU]
instance modulesOnRingedSite_hasEnoughInjectives
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (𝒪 : Sheaf J RingCat.{max u v}) :
    EnoughInjectives (Mod(𝒪)) := by
  -- Reuse the canonical owner-level instance already synthesized for sheaves of modules.
  simpa using (inferInstance : EnoughInjectives (Mod(𝒪)))
