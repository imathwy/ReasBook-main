import Mathlib
import StacksProject_2024.Chap10.Lemma_10_134_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra
open Algebra.Generators
open Algebra.Extension

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {g : S} {n m : ℕ}

/- Domain-style sampling:
* primary domain: cotangent modules of finite algebra presentations under localization away from
  one element.
* sampled owner declarations:
  - `presentation_cotangent_stable_equiv`, the chapter owner for stable presentation-independence
    of conormal modules;
  - `Generators.cotangentCompLocalizationAwayEquiv`, the localization-away splitting of the
    cotangent module after adjoining an inverse;
  - `LocalizedModule.equivTensorProduct`, the canonical bridge between a localized module and the
    tensor-product base-change model;
  - `Generators.basisCotangentAway`, the canonical rank-one basis for the localization-away
    presentation.
* best owner abstraction: the source-facing object is the localized conormal module itself,
  modeled canonically as `LocalizedModule.Away g P.toExtension.Cotangent`; the tensor-product
  description is only the bridge used to connect this owner to
  `Generators.cotangentCompLocalizationAwayEquiv`.
* primitive data vs. derived API:
  - primitive data: the presentations `P` and `Q`, together with the away-localized cotangent
    module of `P`;
  - derived API: the stabilized isomorphism with the cotangent module of `Q`;
  - bridge/view: the tensor-product model and the extra rank-one summand coming from adjoining an
    inverse of `g`.
* layer triage:
  - `source-facing`: the stable isomorphism
    `(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`;
  - `core/canonical`: `presentation_cotangent_stable_equiv`;
  - `bridge/view`: `Generators.cotangentCompLocalizationAwayEquiv` together with
    `LocalizedModule.equivTensorProduct`.
-/

-- Proof sketch: let `P' := (Generators.localizationAway (Localization.Away g) g).comp P`, so
-- `P'` is the canonical presentation of `S_g` obtained from `P` by adjoining one inverse for `g`.
-- `Generators.cotangentCompLocalizationAwayEquiv` identifies `P'.toExtension.Cotangent` with the
-- tensor-product model `Localization.Away g ⊗[S] P.toExtension.Cotangent` plus one free rank-one
-- summand, and `LocalizedModule.equivTensorProduct` rewrites that tensor product as the source-
-- facing localized conormal module `LocalizedModule.Away g P.toExtension.Cotangent`.
-- Lemma `10.134.15` compares `P'` with the arbitrary presentation `Q`. Rewriting the
-- localization-away cotangent summand by its canonical rank-one basis yields the source-facing
-- stable equivalence promised by the Stacks lemma, so the clean public statement here is
-- existence rather than a non-canonical chosen witness.
/-- Lemma 10.134.16: for a presentation `P : R[x₁, …, xₙ] → S` and a presentation
`Q : R[y₁, …, yₘ] → S_g`, there exists a `Localization.Away g`-linear equivalence between the
localized conormal module of `P`, stabilized by `S_g^{⊕ m}`, and the conormal module of `Q`,
stabilized by `S_g^{⊕ n}`. This is the source-facing existence form of the textbook isomorphism
`(I / I²)_g ⊕ S_g^{⊕ m} ≅ J / J² ⊕ S_g^{⊕ n}`; the tensor-product base-change model is only the
bridge to the canonical localization APIs used in the proof. -/
theorem localized_presentation_cotangent_stable_equiv
    (P : Generators R S (Fin n)) (Q : Generators R (Localization.Away g) (Fin m)) :
    Nonempty
      ((LocalizedModule.Away g P.toExtension.Cotangent × (Fin m →₀ Localization.Away g)) ≃ₗ[Localization.Away g]
        (Q.toExtension.Cotangent × (Fin n →₀ Localization.Away g))) := by
  sorry

end
