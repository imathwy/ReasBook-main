import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w x

namespace RingHom

section

variable {Aprime : Type u} {A : Type v} {Bprime : Type w} {B : Type x}
variable [CommRing Aprime] [CommRing A] [CommRing Bprime] [CommRing B]
variable (g : Aprime →+* Bprime) (qA : Aprime →+* A) (qB : Bprime →+* B) (f : A →+* B)

/-
Domain-style sampling:
- primary domain: infinitesimal lifting of étale ring maps across square-zero extension squares;
- sampled owner API:
  `RingHom.Etale`,
  `RingHom.etale_iff_formallyUnramified_and_smooth`,
  `RingHom.FormallyUnramified.of_comp`,
  `RingHom.FormallySmooth.of_flat_of_ker_eq_map_of_square_zero`;
- best owner abstraction: this is a source-facing lifting theorem, but its canonical owner
  predicate is `RingHom.Etale`;
- source-facing: the square-zero lifting criterion for étaleness in a commutative square of
  surjective ring maps;
- core/canonical: `RingHom.Etale`, together with its derived owner consequences
  `FormallyUnramified`, `Smooth`, `Flat`, and `FinitePresentation`;
- bridge/view: the commutative square `qB.comp g = f.comp qA` and the kernel comparison
  `ker qB = (ker qA).map g`.

Primitive-vs-derived split:
- primitive data: the four ring maps, the commutative square, surjectivity, and the square-zero
  / kernel-identification hypotheses;
- derived API: the formal unramifiedness / smoothness / flatness consequences extracted from the
  owner predicate `Etale`.

This item adds genuine source-facing content, so the public theorem should stay a theorem about
`g.Etale`; the refinement is to keep the owner predicate explicit and avoid parallel local wrappers
around its derived formal properties.
-/

-- Proof sketch: keep `RingHom.Etale` as the owner abstraction. The quotient map `f` contributes
-- the derived formally unramified, smooth, flat, and finite-presentation data. The formal
-- unramified part ascends through the commutative square via composition with the surjective map
-- `qB`, while the smooth part is obtained by lifting the quotient étale algebra across the
-- square-zero extension and identifying the lift with `Bprime` using
-- `ker qB = (ker qA).map g`. This recovers `g.Etale`.
/-- Lemma 10.143.11: in a commutative square of surjective ring maps
`Aprime ⟶ Bprime` over `A ⟶ B`, if `A → B` is étale, the kernel of `Aprime → A` is square-zero,
and the kernel of `Bprime → B` is the image ideal `(ker qA).map g`, then
`Aprime → Bprime` is étale. -/
theorem etale_of_surjective_of_ker_eq_map_of_square_zero
    (hcomm : qB.comp g = f.comp qA)
    (hEtale : f.Etale)
    (hSurjA : Function.Surjective qA)
    (hSurjB : Function.Surjective qB)
    (hSq : (ker qA) ^ 2 = ⊥)
    (hker : ker qB = (ker qA).map g) :
    g.Etale := sorry

end

end RingHom
