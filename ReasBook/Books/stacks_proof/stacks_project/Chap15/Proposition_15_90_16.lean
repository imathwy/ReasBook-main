import Mathlib
import StacksProject_2024.Chap13.Lemma_13_7_2
import StacksProject_2024.Chap15.Lemma_15_90_11
import StacksProject_2024.Chap15.Lemma_15_90_12

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
-- the quotient hypothesis, with the source-proof counit analysis on localizations and the final
-- kernel argument for `H⁰`. The proved prefix below isolates the full-faithfulness half coming
-- directly from Lemma `15.90.12`.
/-- Helper for Proposition 15.90.16: the quasi-inverse isomorphism from Lemma `15.90.12`
upgrades the canonical formal glueing functor to a fully faithful left adjoint. -/
noncomputable def formalGlueingCan_fullyFaithful_of_flat_of_quotientMap_bijective
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    (formalGlueingCan S f).FullyFaithful := by
  let e :
      formalGlueingCan S f ⋙ formalGlueingH0 S f ≅ 𝟭 (ModuleCat R) :=
    formalGlueingH0_leftQuasiInverse_of_flat_of_quotientMap_bijective
      (S := S) (f := f)
      (RingHom.flat_algebraMap_iff.mpr (show Module.Flat R S from inferInstance))
      hquot
  -- Lemma `15.90.12` already supplies the source-faithful composite-isomorphic-to-identity input,
  -- so the adjunction criterion yields full faithfulness without further local calculations.
  exact (formalGlueingCanAdjunction (S := S) (f := f)).fullyFaithfulLOfCompIsoId e

/-- Proposition 15.90.16: assume `φ : R → S` is a flat ring map and let
`I = (f₁, \ldots, fₜ) ⊂ R`. If the induced quotient map `R ⧸ I → S ⧸ IS` is bijective, then the
canonical formal glueing functor
`Can : Mod_R ⥤ Glue(R → S, f₁, \ldots, fₜ)` is an equivalence of categories, where the codomain is
the genuine formal glueing category from Remark `15.90.10`. -/
@[stacks 05ER]
theorem formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap (Ideal.map (algebraMap R S) I) (algebraMap R S) Ideal.le_comap_map)) :
    Functor.IsEquivalence (formalGlueingCan S f) := by
  let hFF :=
    formalGlueingCan_fullyFaithful_of_flat_of_quotientMap_bijective
      (S := S) (f := f) hquot
  letI : Functor.Full (formalGlueingCan S f) := hFF.full
  letI : Functor.Faithful (formalGlueingCan S f) := hFF.faithful
  -- Route correction: the remaining source-faithful content is the counit analysis for `H⁰`.
  -- The intended closing step is to prove that `formalGlueingH0 S f` has zero kernel by showing
  -- that, for an object `X` with `H⁰(X) = 0`, each local component of the counit
  -- `Can(H⁰(X)) ⟶ X` is an isomorphism and hence every local module of `X` vanishes. One then
  -- identifies `H⁰(X)` with the base module of such a zero-local object and applies
  -- `Adjunction.isEquivalence_of_fullyFaithful_of_kernel_le_isZero`.
  sorry

end
