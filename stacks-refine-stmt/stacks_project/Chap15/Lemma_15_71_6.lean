import Mathlib
import stacks_project.Chap15.Lemma_15_71_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

/-
Domain-style sampling:
* primary domain: `I`-projective modules and their behavior in short exact sequences;
* sampled owner declarations:
  `Module.IsIdealProjective`,
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`,
  `ShortComplex.ShortExact.extClass`,
  `precomp_extClass_surjective_of_projective_X₂`;
* best owner abstraction: the chapter owner is `Module.IsIdealProjective I M`, whose primitive
  data are projective factorizations of the multiplication maps `m ↦ (a : R) • m`; the canonical bridge
  for this short-exact statement is the `Ext`-annihilation formulation from Lemma `15.71.3`,
  combined with the short-exact `Ext` owner `ShortComplex.ShortExact.extClass` and its
  dimension-shifting API when the middle term is projective;
* primitive data: a short exact complex `S` together with explicit hypotheses
  `Module.IsIdealProjective I S.X₃` and `Projective S.X₂`;
* derived API: the `Ext¹`-annihilation characterization of `Module.IsIdealProjective`, obtained from
  `smul_endomorphism_tfae_factorsThroughProjective_factorsThroughFree_ext`, and the
  short-exact `Ext` comparison maps attached to `hS`;
* layer triage: this file is `source-facing`, reusing the chapter owner and the canonical
  short-exact `Ext` bridge rather than introducing a parallel `ModuleCat` wrapper.
-/

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {S : ShortComplex (ModuleCat.{u} R)}

/-- Lemma 15.71.6: in a short exact sequence `0 ⟶ K ⟶ P ⟶ M ⟶ 0` of `R`-modules, if `M` is
`I`-projective and `P` is projective, then `K` is `I`-projective. -/
theorem isIdealProjective_X₁ (hS : S.ShortExact) (hX₃ : Module.IsIdealProjective I S.X₃)
    (hX₂ : Projective S.X₂) :
    Module.IsIdealProjective I S.X₁ := sorry

end CategoryTheory.ShortComplex.ShortExact
