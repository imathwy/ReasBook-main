import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra

universe u v

section

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Lemma 10.139.4:
- primary domain: smooth commutative algebra retractions, their conormal module, and the induced
  formal local structure on adic completions;
- sampled owner declarations:
  `Algebra.Smooth`,
  `KaehlerDifferential.finite`,
  `FormallySmooth.projective_kaehlerDifferential`,
  `retractionKerCotangentToTensorEquivSection`;
- best owner abstraction: the smooth owner `Algebra.Smooth R S` together with the canonical
  conormal owner `(RingHom.ker σ).Cotangent` attached to a section `σ : S →ₐ[R] R`;
- primitive data: the smooth `R`-algebra `S`, the section `σ`, and the left-inverse equation `hσ`;
- derived API: finiteness/projectivity of the conormal module and, after a freeness hypothesis, the
  existence of a formal-power-series description of the `ker σ`-adic completion.

Source/core/bridge triage:
- `source-facing`: the two theorems below about the conormal module and the completed algebra of a
  smooth retraction;
- `core/canonical`: `Algebra.Smooth`, the Kähler/formal-smooth owner theorems, and the canonical
  conormal owner `RingHom.ker σ`;
- `bridge/view`: the textbook identification `I/I²` with `(RingHom.ker σ).Cotangent` and the
  resulting power-series presentation of the completion. -/

section SmoothSection

variable [Algebra.Smooth R S] (σ : S →ₐ[R] R)
  (hσ : Function.LeftInverse σ (algebraMap R S))

-- Proof sketch: apply the split conormal sequence for the section `σ : S →ₐ[R] R` to identify
-- `(RingHom.ker σ).Cotangent` with a base change of `Ω[S⁄R]`; smoothness makes
-- `Ω[S⁄R]` finite and projective over `S`, and restriction along the section preserves those
-- finiteness and projectivity properties over `R`.
/-- Lemma 10.139.4: if `R → S` is smooth and `σ : S →ₐ[R] R` is a left inverse to the structure
map, then the conormal module `I/I²`, with `I = ker σ`, is a finite projective `R`-module. This
is the canonical mathlib-facing formulation of the source statement that `I/I²` is finite locally
free over `R`. -/
theorem smooth_section_cotangent_finite_projective :
    Module.Finite R (RingHom.ker σ).Cotangent ∧
      Module.Projective R (RingHom.ker σ).Cotangent := sorry

-- Proof sketch: choose a finite basis of `(RingHom.ker σ).Cotangent`, lift basis
-- vectors to elements of `ker σ`, and use formal smoothness of `S` over `R` to build compatible
-- inverses modulo successive powers of `ker σ`; the induced map from a multivariable formal power
-- series ring is then an `R`-algebra isomorphism onto the `ker σ`-adic completion.
/-- If the conormal module attached to a smooth retraction is free over `R`, then the
`ker σ`-adic completion of `S` is isomorphic, as an `R`-algebra, to a formal power series ring in
finitely many variables over `R`. -/
theorem smooth_section_adicCompletion_exists_algEquiv_mvPowerSeries
    (hfree : Module.Free R (RingHom.ker σ).Cotangent) :
    ∃ d : ℕ,
      Nonempty ((AdicCompletion (RingHom.ker σ) S) ≃ₐ[R] MvPowerSeries (Fin d) R) := sorry

end SmoothSection

end
