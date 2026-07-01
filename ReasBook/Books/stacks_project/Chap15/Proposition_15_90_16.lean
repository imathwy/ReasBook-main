import Mathlib
import stacks_project.Chap15.Lemma_15_90_13
import stacks_project.Chap15.Lemma_15_90_15

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u v

section

variable {R : Type u} [CommRing R]
variable {S : Type u} [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]

/- Domain-style sampling for 15.90.16:
- primary domain: formal glueing for module categories and categorical equivalences;
- sampled owner declarations:
  `formalGlueingCan`,
  `formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective`,
  `Functor.IsEquivalence`,
  `Functor.asEquivalence`;
- best owner abstraction:
  the source-facing proposition should expose only the equivalence witness for the canonical
  functor `formalGlueingCan S f`, while the inverse functor and the unit/counit isomorphisms stay
  with the canonical owner API `Functor.asEquivalence`;
- primitive data:
  the canonical functor `formalGlueingCan S f` and the quotient-bijectivity hypothesis;
- derived API:
  any quasi-inverse, unit isomorphism, and counit isomorphism are already canonically derived from
  `Functor.IsEquivalence`, so keeping parallel local wrappers would duplicate the owner API.

Source/core/bridge triage:
- `source-facing`: `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- `core/canonical`: `Functor.IsEquivalence` and `Functor.asEquivalence`;
- `bridge/view`: none needed here beyond the canonical equivalence API. -/

-- Proof sketch: combine Lemma `15.90.12`, which identifies `H^0 ∘ Can` with the identity under
-- the quotient hypothesis, with Lemma `15.90.15`, which identifies the comparison map after
-- localizing at each `fᵢ`, and Lemma `15.90.8`, which lifts the remaining extension class. This
-- yields essential surjectivity of `Can`, while the previous left quasi-inverse statement gives
-- full faithfulness, hence `Can` is an equivalence.
/-- Proposition 15.90.16: assume `φ : R → S` is a flat ring map and let
`I = (f₁, \ldots, fₜ) ⊂ R`. If the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the
canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, \ldots, fₜ)` is an equivalence of categories, where the codomain is
the genuine formal glueing category from Remark `15.90.10`. -/
theorem formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    Functor.IsEquivalence (formalGlueingCan S f) := sorry

end
