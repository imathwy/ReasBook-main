import Mathlib
import StacksProject_2024.Chap12.Definition_12_27_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

noncomputable section

/-
Domain-style sampling for Theorem 19.7.4:
- primary domain: enough injectives and functorial injective embeddings for abelian sheaves on a
  site;
- sampled owner declarations:
  `EnoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  the Chapter 12 instance `HasFunctorialInjectiveEmbeddings C → EnoughInjectives C`,
  `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`;
- best owner abstraction: the source-facing statement in this file is
  `EnoughInjectives (Sheaf K AddCommGrpCat)`, while
  `HasFunctorialInjectiveEmbeddings (Sheaf K AddCommGrpCat)` is the canonical owner-level derived
  API used downstream;
- primitive data: enough injectives for the category of abelian sheaves on the site;
- derived API: the owner-level `HasFunctorialInjectiveEmbeddings` instance supplied by the Chapter
  12 bridge.

Source/core/bridge triage:
- `source-facing`: Theorem 19.7.4, asserting enough injectives for abelian sheaves on a site;
- `core/canonical`: `EnoughInjectives` and `HasFunctorialInjectiveEmbeddings`;
- `bridge/view`: the canonical Chapter 12 passage from enough injectives to functorial injective
  embeddings.
-/

-- Proof sketch: choose the uniform ordinal bound from Lemma 19.7.2 for the family of all
-- subsheaves of free abelian sheaves on representables, build the transfinite system `J_α(ℱ)`,
-- and use Lemma 19.7.3 together with Lemma 19.7.1 to obtain functorial injective embeddings of
-- abelian sheaves; the Chapter 12 bridge then yields enough injectives.
/-- Theorem 19.7.4: the category of sheaves of abelian groups on a site has enough injectives. -/
theorem siteAbelianSheaf_hasEnoughInjectives
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) :
    EnoughInjectives (Sheaf K AddCommGrpCat.{max u v}) := sorry

/-- Canonical owner-level form of Theorem 19.7.4 for abelian sheaves on a site. -/
instance siteAbelianSheaf_hasFunctorialInjectiveEmbeddings
    {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) :
    HasFunctorialInjectiveEmbeddings (Sheaf K AddCommGrpCat.{max u v}) := by
  exact hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian
