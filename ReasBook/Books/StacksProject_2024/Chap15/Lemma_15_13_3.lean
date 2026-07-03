import StacksProject_2024.Chap15.Lemma_15_11_6
import StacksProject_2024.Chap15.Lemma_15_9_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {R : Type u} {S : Type v} {A : Type w}
variable [CommRing R] [CommRing S] [CommRing A]
variable [Algebra R S] [Algebra R A]

/-
Domain-style sampling:
- primary domain: lifting maps from smooth algebras over a quotient along the henselian étale
  section property;
- sampled owner declarations:
  `Algebra.Smooth.baseChange`,
  `exists_etale_lift_to_quotient_of_smooth`,
  `Ideal.HasEtaleLiftProperty`,
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`;
- best owner abstraction: the primitive lifting input is the Chapter 15 owner
  `Ideal.HasEtaleLiftProperty`; the henselian hypothesis is derived API here via the chapter TFAE,
  while smoothness is still owned canonically by `Algebra.Smooth`;
- primitive data: the ideal `I`, the smooth `R`-algebra `S`, the quotient map
  `f : S →ₐ[R] A ⧸ I`, and the étale-section owner `I.HasEtaleLiftProperty`;
- derived API: the source-facing henselian corollary obtained by extracting
  `I.HasEtaleLiftProperty` from `HenselianRing A I`.

Source/core/bridge triage:
- `source-facing`: `smooth_exists_lift_of_henselianRing`;
- `core/canonical`: `Algebra.Smooth` and `Ideal.HasEtaleLiftProperty`;
- `bridge/view`: the corollary from `HenselianRing A I` via
  `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
-/

-- Proof sketch: base change `S` from `R` to `A` to obtain the smooth `A`-algebra `S ⊗[R] A`.
-- Apply the étale lifting statement for smooth algebras modulo `I` to the induced map
-- `S ⊗[R] A → A ⧸ I`, then use the henselian lifting property for étale `A`-algebras to get a
-- section back to `A`. Precompose the resulting composite with `TensorProduct.includeLeft` to
-- obtain the desired lift `S →ₐ[R] A`. The core input used from the target pair is exactly the
-- chapter owner `I.HasEtaleLiftProperty`.
/-- If `S` is a smooth `R`-algebra and reduction modulo `I` on `A` has the étale section lifting
property, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
theorem smooth_exists_lift_of_hasEtaleLiftProperty (I : Ideal A) [Algebra.Smooth R S]
    (hI : I.HasEtaleLiftProperty) (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := sorry

/-- Lemma 15.13.3: if `S` is a smooth `R`-algebra, `A` is an `R`-algebra, and `(A, I)` is a
henselian pair, then every `R`-algebra map `S → A ⧸ I` lifts to an `R`-algebra map `S → A`. -/
theorem smooth_exists_lift_of_henselianRing (I : Ideal A) [Algebra.Smooth R S]
    [HenselianRing A I] (f : S →ₐ[R] A ⧸ I) :
    ∃ f' : S →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp f' = f := by
  -- This is the `HenselianRing A I → I.HasEtaleLiftProperty` bridge from
  -- `henselianRing_tfae_etaleLift_idempotents_gabberCriterion`.
  have hI : I.HasEtaleLiftProperty := by
    sorry
  exact smooth_exists_lift_of_hasEtaleLiftProperty I hI f

end

end Algebra
