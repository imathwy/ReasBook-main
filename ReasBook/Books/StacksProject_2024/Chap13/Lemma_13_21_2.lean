import Mathlib
import stacks_project.Chap13.Definition_13_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe v u

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]

/-
Domain-style sampling:
- primary domain: Cartan-Eilenberg resolutions of bounded-below cochain complexes in an abelian
  category with enough injectives;
- sampled owner declarations:
  `CartanEilenbergResolution`,
  `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`,
  `CategoryTheory.InjectiveResolution`;
- best owner abstraction: the source-facing owner for the present lemma is
  `CartanEilenbergResolution`, while the columnwise and successive short-exact-sequence inputs used
  to build it are already canonically owned by `CochainComplex.InjectiveResolution`,
  `CategoryTheory.ShortComplex`, and `CategoryTheory.InjectiveResolution`;
- primitive data here: only the bounded-below source complex `K`;
- derived API here: the genuine existence statement that `K` admits a Cartan-Eilenberg
  resolution.

Source/core/bridge triage:
- `source-facing`: the existence statement below;
- `core/canonical`: the existing injective-resolution owners from Chapter 13 and mathlib;
- `bridge/view`: none in this file, since the target statement is already directly about the
  source-facing owner `CartanEilenbergResolution`.
-/

-- Proof sketch: choose a lower bound for `K`, then for each short exact sequence
-- `0 ⟶ Z^p ⟶ K^p ⟶ B^{p + 1} ⟶ 0` and `0 ⟶ B^{p + 1} ⟶ Z^{p + 1} ⟶ H^{p + 1}(K^•) ⟶ 0`
-- use the canonical owner `CochainComplex.InjectiveResolution` from Lemma 13.18.3 together with
-- the short-complex comparison data supplied directly by Lemma 13.18.9 to fit consecutive choices
-- into short exact sequences of complexes. Iterating this construction produces the
-- double complex and augmentation data required by the source-facing owner
-- `CartanEilenbergResolution`.
/-- Lemma 13.21.2: every bounded-below cochain complex in an abelian category with enough
injectives admits a Cartan-Eilenberg resolution. -/
theorem exists_cartanEilenbergResolution (K : CochainComplex.Plus 𝒜) :
    Nonempty (CartanEilenbergResolution K) := sorry

end
